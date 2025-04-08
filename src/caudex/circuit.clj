(ns caudex.circuit
  "Functions to transform a query graph into a dbsp circuit"
  (:require [caudex.query-analyzer :as qa]
            [clojure.set :as set]
            [caudex.dbsp :refer :all]
            [caudex.utils :as utils]
            [ubergraph.alg :as alg]
            [ubergraph.core :as uber]))

(declare build-circuit*)
#trace
 (defn- find-val-idx [op var]
   (let [idx (.indexOf (-to-vector (-get-output-type op)) var)]
     (when (not= -1 idx)
       (->ValIndex idx))))

(defn- get-root [circuit]
  (some #(when (= :root (-get-op-type %)) %) (uber/nodes circuit)))

(defn- find-starting-node
  ([graph]
   (find-starting-node graph (uber/nodes graph)))
  ([graph nodes]
   (let [pattern-nodes
         (into #{}
               (filter #(true?
                         (some (fn [e] (when (= :pattern (uber/attr graph e :clause-type))
                                         true))
                               (uber/out-edges graph %))))
               nodes)]
     (or
      (some (fn [node]
              (when (and (contains? pattern-nodes node)
                         (or (= 0 (uber/in-degree graph node))
                             (nil? (some #(when (= :pattern (uber/attr graph % :clause-type))
                                            %)
                                         (uber/in-edges graph node)))))
                node))
            nodes)
      (first pattern-nodes)))))

(defn- merge-sub-circuit [circuit root sub-circuit]
  (let [sub-circuit-root (get-root sub-circuit)
        sub-circuit (uber/remove-nodes sub-circuit sub-circuit-root)]
    (reduce
     #(if (= :root (-get-op-type (:src %2)))
        (uber/add-directed-edges %1 [root (:dest %2)])
        (uber/add-directed-edges %1 [(:src %2) (:dest %2)]))
     circuit
     (uber/edges sub-circuit))))

(defn- add-op-inputs [circuit op & inputs]
  (reduce
   (fn [c [idx in]]
     (uber/add-directed-edges c [in op {:arg idx}]))
   circuit
   (map-indexed vector inputs)))
#trace
(defn- join-ops [circuit op-1 op-2]
  (let [add-1 (->AddOperator (gensym "add-") (-get-output-type op-1))
        delay-1 (->DelayOperator (gensym "delay-") (-get-output-type op-1))
        add-2 (->AddOperator (gensym "add-") (-get-output-type op-2))
        delay-2 (->DelayOperator (gensym "delay-") (-get-output-type op-2))
        join-1 (->JoinOperator
                (gensym "join-")
                (-get-output-type op-1)
                (-get-output-type op-2)
                (-get-join-constraints (-get-output-type op-1) (-get-output-type op-2)))
        join-2 (->JoinOperator
                (gensym "join-")
                (-get-output-type op-1)
                (-get-output-type op-2)
                (-get-join-constraints (-get-output-type op-1) (-get-output-type op-2)))
        delay-3 (->DelayOperator (gensym "delay-") (-get-output-type op-2))
        final-add (->AddOperator (gensym "add-") (-get-output-type join-1))]
    [(-> circuit
         (add-op-inputs add-1 op-1 delay-1)
         (add-op-inputs delay-1 add-1)
         (add-op-inputs join-1 add-1 op-2)
         (add-op-inputs add-2 op-2 delay-2)
         (add-op-inputs delay-2 add-2)
         (add-op-inputs delay-3 add-2)
         (add-op-inputs join-2 op-1 delay-3)
         (add-op-inputs final-add join-1 join-2))
     final-add]))
#trace
 (defn- join-pattern-clauses [circuit query-graph root input-op-map]
   (let [start (find-starting-node query-graph)
         pattern-edges #(filterv
                         (fn [e] (= :pattern (uber/attr query-graph e :clause-type)))
                         (uber/out-edges query-graph %))
         sym? #(and (symbol? %) (not= '_ %))]
     (loop [processed [] queue (pattern-edges start) ret circuit]
       (let [[ret ops nodes edges] (reduce
                                    (fn [[r ops nodes edges] {:keys [src dest] :as edge}]
                                      (let [attr (uber/attr query-graph edge :label)
                                            conds
                                            (cond-> []
                                              (not (sym? src)) (conj [= (->ValIndex 0) src])
                                              (not (sym? attr)) (conj [= (->ValIndex 1) attr])
                                              (not (sym? dest)) (conj [= (->ValIndex 2) dest]))
                                            selections
                                            (cond-> []
                                              (sym? src) (conj (->ValIndex 0))
                                              (sym? attr) (conj (->ValIndex 1))
                                              (sym? dest) (conj (->ValIndex 2)))
                                            output-type (filterv sym? [src attr dest])
                                            op (->FilterOperator
                                                (gensym "datom-") [src attr dest] conds selections)
                                           ;; Join with previously processed op that has a common var
                                            prev-op
                                            (some #(let [vars (-get-output-type %)]
                                                     (when (set/intersection (set vars) (set output-type))
                                                       %))
                                                  processed)]
                                        [(cond->
                                          (-> r
                                              (uber/add-nodes op)
                                              (uber/add-directed-edges [root op]))
                                           (some? prev-op) (-> (join-ops op prev-op) first))
                                         (conj ops op)
                                         (conj nodes dest)
                                         (conj edges edge)]))
                                    [ret [] [] #{}]
                                    queue)
             queue (into [] (comp
                             (map #(pattern-edges %))
                             cat
                             (filter #(not (contains? edges %))))
                         nodes)
             processed (into processed ops)]
         (if (seq queue)
           (recur processed queue ret)
           (if (seq processed)
             (let [last-op (last (utils/topsort-circuit ret))]
               (if input-op-map
                 (let [output-type (-to-vector (-get-output-type last-op))
                       required-inputs
                       (set/intersection (set output-type) (set (keys input-op-map)))]
                   (reduce
                    #(join-ops (first %1) (second %1) (get input-op-map %2))
                    [ret last-op]
                    required-inputs))
                 [ret last-op]))
             [(uber/add-nodes ret input-op-map) input-op-map]))))))
#trace
 (defn- process-non-pattern-clauses [circuit input-op query-graph rules]
   (let [nodes (filterv
                #(contains? #{:or-join :not-join :pred :fn :rule}
                            (uber/attr query-graph % :type))
                (utils/topsort-query-graph query-graph))]
     (reduce
      (fn [[circuit last-op] node]
        (let [args (sort-by
                    second
                    (into []
                          (comp
                           (filter #(= :arg (first (uber/attr query-graph % :label))))
                           (map #(vector (:src %) (second (uber/attr query-graph % :label)))))
                          (uber/in-edges query-graph node)))
              indices (mapv
                       (fn [[arg]]
                         (let [idx (if (symbol? arg)
                                     (find-val-idx last-op arg)
                                     arg)]
                           (if (nil? idx)
                             (throw (Exception. (str "Could not find " arg " in input op")))
                             idx)))
                       args)
              root (get-root circuit)]
          (case (uber/attr query-graph node :type)
            :pred (let [op (->FilterOperator
                            (gensym "pred-")
                            (-get-output-type last-op)
                            [(into [(uber/attr query-graph node :fn)]
                                   indices)]
                            nil)]
                    [(uber/add-directed-edges circuit [last-op op]) op])
            :fn (let [binding (some #(when (= :binding (uber/attr query-graph % :label)) %)
                                    (uber/out-edges query-graph node))
                      op (->MapOperator (gensym "fn-")
                                        (-get-output-type last-op)
                                        (conj (-> last-op
                                                  (-get-output-type) (-to-vector))
                                              (:dest binding))
                                        (uber/attr query-graph node :fn)
                                        indices)]
                  [(uber/add-directed-edges circuit [last-op op]) op])
            :not-join (let [[sub-circuit last-op]
                            (build-circuit* (mapv first args) node rules last-op)
                            neg-op
                            (->NegOperator (gensym "neg-") (-get-output-type last-op))
                            sub-circuit
                            (uber/add-directed-edges sub-circuit [last-op neg-op])]
                        [(merge-sub-circuit circuit root sub-circuit) neg-op])

            [circuit last-op])))
      [circuit input-op]
      nodes)))

#trace
 (defn- build-circuit*
   ([inputs query-graph rules]
    (build-circuit* inputs query-graph rules nil))
   ([inputs query-graph rules input-op-map]
    (let [components (alg/connected-components query-graph)
          _ (when (> (count components) 1)
              (throw (Exception. "Cannot have disjoint query components")))
          root (->RootOperator (gensym "root-"))
          circuit (-> (uber/ubergraph false false)
                      (uber/add-nodes root))
          [circuit input-op-map]
          (if (seq inputs)
            (if (map? input-op-map)
              input-op-map
              (let [ops
                    (into {}
                          (map
                           #(vector
                             %
                             (->FilterOperator
                              (gensym "input-")
                              [::input % %]
                              [[= ::input (->ValIndex 0)]
                               [= % (->ValIndex 1)]]
                              [(->ValIndex 2)])))
                          inputs)]
                [(reduce
                  #(uber/add-directed-edges %1 [root (val %2)])
                  circuit ops)
                 ops]))
            [circuit nil])
          [circuit last-op] (join-pattern-clauses circuit query-graph root input-op-map)]
      (process-non-pattern-clauses circuit last-op query-graph rules))))

#trace
 (defn build-circuit
   ([query]
    (build-circuit query []))
   ([query rules]
    (let [{:keys [inputs projections rules graph]} (qa/analyze query rules)
          [circuit last-op] (build-circuit* inputs graph rules)
          proj-vars (into [] (comp (map :symbol) (filter some?)) projections)
          projection (->FilterOperator
                      (gensym "proj-")
                      (-get-output-type last-op)
                      []
                      (mapv #(find-val-idx last-op %) proj-vars))]
      (uber/add-directed-edges circuit [last-op projection]))))


(comment

  (build-circuit '[:find ?name
                   :in $ % ?cat-name
                   :where
                   [?p-cat :category/name ?cat-name]
                   [?p :product/name ?name]
                   [?p :product/categories ?cat]
                   (sub-cat? ?cat ?p-cat)]
                 '[[(sub-cat? ?c ?p)
                    [(= ?c ?p)]]
                   [(sub-cat? ?c ?p)
                    [?c :category/parent ?pc]
                    (sub-cat? ?pc ?p)]])
  (build-circuit
   '[:find ?a ?b
     :in ?in ?in2
     :where
     [?a :attr ?in]
     [?b :attr ?in2]]))

