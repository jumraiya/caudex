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

(defn- merge-sub-circuit [circuit sub-circuit args]
  (let [root (get-root circuit)
        sub-circuit-last-op (last (utils/topsort-circuit sub-circuit))
        last-op (last (utils/topsort-circuit circuit))
        projection (->FilterOperator
                    (gensym "proj-")
                    (-get-output-type sub-circuit-last-op)
                    nil
                    (mapv #(find-val-idx sub-circuit-last-op (first %)) args))
        sub-circuit (uber/add-directed-edges sub-circuit [sub-circuit-last-op projection])
        [sub-circuit sub-circuit-last-op] (join-ops sub-circuit projection last-op)
        sub-circuit-root (get-root sub-circuit)]
    [(uber/remove-nodes
      (reduce
       #(if (= :root (-get-op-type (:src %2)))
          (uber/add-directed-edges %1 [root (:dest %2)])
          (uber/add-directed-edges %1 [(:src %2) (:dest %2)]))
       circuit
       (uber/edges sub-circuit))
      sub-circuit-root)
     sub-circuit-last-op]))

(defn- join-with-inputs [circuit op input-op-map]
  (let [o-type (-> op -get-output-type -to-vector set)]
    (reduce
     (fn [[ret last-op] input-op]
       (join-ops ret last-op input-op))
     [circuit op]
     (eduction
      (filter #(contains? o-type (key %)))
      (map val)
      (filter #(= 0 (uber/out-degree circuit %)))
      input-op-map))))

#trace
 (defn- join-pattern-clauses [circuit query-graph root input-op-map]
   (let [start (find-starting-node query-graph)
         pattern-edges #(filterv
                         (fn [e] (= :pattern (uber/attr query-graph e :clause-type)))
                         (uber/out-edges query-graph %))
         var? #(and (symbol? %) (not= '_ %))]
     (loop [processed [] queue (pattern-edges start) ret circuit]
       (let [[ret ops nodes edges last-op]
             (reduce
              (fn [[r ops nodes edges] {:keys [src dest] :as edge}]
                (let [attr (uber/attr query-graph edge :label)
                      conds
                      (cond-> []
                        (not (symbol? src)) (conj [= (->ValIndex 0) src])
                        (not (symbol? attr)) (conj [= (->ValIndex 1) attr])
                        (not (symbol? dest)) (conj [= (->ValIndex 2) dest]))
                      selections
                      (cond-> []
                        (var? src) (conj (->ValIndex 0))
                        (var? attr) (conj (->ValIndex 1))
                        (var? dest) (conj (->ValIndex 2)))
                      output-type (filterv var? [src attr dest])
                      op (->FilterOperator
                          (gensym "datom-") [src attr dest] conds selections)
                      ;; Join with previously processed op that has a common var
                      prev-op
                      (some #(let [vars (-get-output-type %)]
                               (when (seq (set/intersection (set vars) (set output-type)))
                                 %))
                            processed)
                      [ret last-op] (cond->
                                        (-> r
                                            (uber/add-nodes op)
                                            (uber/add-directed-edges [root op]))
                                        (some? prev-op) (join-ops op prev-op)
                                        (nil? prev-op) (vector op))
                      [ret last-op] (join-with-inputs ret last-op input-op-map)]
                  [ret
                   (conj ops op)
                   (conj nodes dest)
                   (conj edges edge)
                   last-op]))
              [ret [] [] #{} nil]
              queue)
             queue (into [] (comp
                             (map #(pattern-edges %))
                             cat
                             (filter #(not (contains? edges %))))
                         nodes)
             processed (into processed ops)]
         (if (seq queue)
           (recur processed queue ret)
           [ret last-op])))))

(defn- process-fn|pred [circuit type args last-op query-graph node input-op-map]
  (let [o-type (-> last-op -get-output-type -to-vector set)
        var-args (into []
                       (comp
                        (map first)
                        (filter symbol?)
                        (remove #(contains? o-type %))
                        (filter #(contains? input-op-map %)))
                       args)
        [circuit last-op] (if (contains? #{:pred :fn} (uber/attr query-graph node :type))
                            (reduce
                             #(join-ops (first %1) (second %1) (get input-op-map %2))
                             [circuit last-op]
                             var-args)
                            [circuit last-op])
        indices
        (mapv
         (fn [[arg _ required?]]
           (let [idx (if (symbol? arg)
                       (find-val-idx last-op arg)
                       arg)]
             (if (and (nil? idx) (symbol? arg) required?)
               (throw (Exception. (str "Could not find " arg " in input op")))
               idx)))
         args)]
   (case type
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
           [(uber/add-directed-edges circuit [last-op op]) op]))))
#trace
 (defn- mk-input-ops [circuit source inputs input-op-map]
   (reduce
    (fn [[circuit m] [in _ required?]]
      (let [idx (or (get input-op-map in) (find-val-idx source in))
            _ (when (and (nil? idx) required?)
                (throw (Exception. (str "Could not find input " in))))]
        (if (some? idx)
          (if (contains? input-op-map in)
            [circuit (assoc m in (get input-op-map in))]
            (let [op (->FilterOperator
                      (gensym "input-")
                      (-get-output-type source)
                      nil
                      [idx])]
              [(uber/add-directed-edges circuit [source op]) (assoc m in op)]))
          [circuit m])))
    [circuit {}]
    inputs))

#trace
 (defn- process-non-pattern-clauses
   "Processes non datom clauses, all required inputs are joined into a single operator"
   [circuit input-op query-graph rules input-op-map]
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
                           (map #(vector (:src %) (second (uber/attr query-graph % :label)) (uber/attr query-graph % :required?))))
                          (uber/in-edges query-graph node)))]
          (case (uber/attr query-graph node :type)
            (:pred :fn)
            (process-fn|pred circuit (uber/attr query-graph node :type) args last-op query-graph node input-op-map)
            :not-join (let [[circuit input-ops]
                            (mk-input-ops circuit last-op args input-op-map)
                            [sub-circuit] (build-circuit* (mapv first args) node rules input-ops)
                            [circuit not-join-last-op] (merge-sub-circuit circuit sub-circuit args)
                            neg-op (->NegOperator (gensym "neg-") (-get-output-type not-join-last-op))
                            circuit (uber/add-directed-edges circuit [not-join-last-op neg-op])]
                        (if (some? last-op)
                          (let [add-op (->AddOperator
                                        (gensym "add-")
                                        (-get-output-type last-op))
                            circuit (uber/add-directed-edges
                                     circuit
                                     [neg-op add-op {:arg 0}]
                                     [last-op add-op {:arg 1}])]
                           [circuit add-op])
                          [circuit neg-op]))

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
              [circuit input-op-map]
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
      (process-non-pattern-clauses circuit last-op query-graph rules input-op-map))))

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

