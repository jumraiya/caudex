(ns caudex.circuit
  "Functions to transform a query graph into a dbsp circuit"
  (:require [caudex.query-analyzer :as qa]
            [clojure.set :as set]
            [caudex.dbsp :refer :all]
            [caudex.utils :as utils]
            [ubergraph.alg :as alg]
            [ubergraph.core :as uber]))

(declare build-circuit*)

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

 (defn- join-ops
   ([circuit op-1 op-2]
    (join-ops circuit op-1 op-2 false))
   ([circuit op-1 op-2 inverse?]
    (let [add-1 (->AddOperator (gensym "add-") (-get-output-type op-1))
          delay-1 (->DelayOperator (gensym "delay-") (-get-output-type op-1))
          add-2 (->AddOperator (gensym "add-") (-get-output-type op-2))
          delay-2 (->DelayOperator (gensym "delay-") (-get-output-type op-2))
          constraints (-get-join-constraints
                       (-get-output-type op-1) (-get-output-type op-2))
          constraints (if inverse?
                        (mapv (fn [[pred & args :as c]]
                                (if (= pred =)
                                  (into [not=] args)
                                  c))
                              constraints)
                        constraints)
          join-1 (->JoinOperator
                  (gensym "join-")
                  (-get-output-type op-1)
                  (-get-output-type op-2)
                  constraints)
          join-2 (->JoinOperator
                  (gensym "join-")
                  (-get-output-type op-1)
                  (-get-output-type op-2)
                  constraints)
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
       final-add])))

(defn- merge-sub-circuit [circuit sub-circuit args]
  (let [root (get-root circuit)
        sub-circuit-last-op (last (utils/topsort-circuit sub-circuit))
        projection (->FilterOperator
                    (gensym "proj-")
                    (-get-output-type sub-circuit-last-op)
                    nil
                    (mapv #(find-val-idx sub-circuit-last-op (first %)) args))
        sub-circuit (add-op-inputs sub-circuit projection sub-circuit-last-op)
        sub-circuit-root (get-root sub-circuit)]
    [(uber/remove-nodes
      (reduce
       #(let [attrs (uber/attrs sub-circuit %2)]
          (if (= :root (-get-op-type (:src %2)))
            (uber/add-directed-edges %1 [root (:dest %2) attrs])
            (uber/add-directed-edges %1 [(:src %2) (:dest %2) attrs])))
       circuit
       (uber/edges sub-circuit))
      sub-circuit-root)
     projection]))

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
                                           (add-op-inputs op root))
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
  (let [o-type (when (some? last-op)
                 (-> last-op -get-output-type -to-vector set))
        var-args (into []
                       (comp
                        (map first)
                        (filter symbol?)
                        (remove #(and (some? o-type) (contains? o-type %)))
                        (filter #(contains? input-op-map %)))
                       args)
        [circuit last-op]  (reduce
                            (fn [[c op] v]
                              (if (some? op)
                                (join-ops c op (get input-op-map v))
                                [c (get input-op-map v)]))
                            [circuit last-op]
                            var-args)
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
              [(add-op-inputs circuit op last-op) op])
      :fn (let [binding (some #(when (= :binding (uber/attr query-graph % :label)) %)
                              (uber/out-edges query-graph node))
                op (->MapOperator (gensym "fn-")
                                  (-get-output-type last-op)
                                  (conj (-> last-op
                                            (-get-output-type) (-to-vector))
                                        (:dest binding))
                                  (uber/attr query-graph node :fn)
                                  indices)]
            [(add-op-inputs circuit op last-op) op]))))


(defn- mk-input-ops [circuit source inputs input-op-map]
  (reduce
   (fn [[c m] [in _ required?]]
     (let [idx (when (some? source)
                 (find-val-idx source in))
           _ (when (and (nil? idx) (not (contains? input-op-map in)) required?)
               (throw (Exception. (str "Could not find input " in))))]
       (cond
         (some? idx) (let [op (->FilterOperator
                               (gensym "input-")
                               (-get-output-type source)
                               nil
                               [idx])]
                       [(add-op-inputs c op source) (assoc m in op)])
         (contains? input-op-map in) [c (assoc m in (get input-op-map in))]
         :else [c m])))
   [circuit {}]
   inputs))

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
            :not-join (let [[circuit input-ops] (mk-input-ops circuit last-op args input-op-map)
                            [sub-circuit] (build-circuit* (mapv first args) node rules input-ops)
                            [circuit not-join-last-op] (merge-sub-circuit circuit sub-circuit args)]
                        (if (some? last-op)
                          (join-ops circuit not-join-last-op last-op true)
                          (let [neg-op (->NegOperator
                                        (gensym "neg-")
                                        (-get-output-type not-join-last-op))]
                            [(add-op-inputs circuit neg-op not-join-last-op) neg-op])))
            :or-join (let [[circuit input-ops]
                           (mk-input-ops circuit last-op args input-op-map)
                           [circuit sub-circuit-outputs]
                           (reduce
                            (fn [[circuit acc] cnjn-graph]
                              (let [sub-circuit
                                    (first (build-circuit* (mapv first args) cnjn-graph rules input-ops :join-unconnected? true))
                                    [circuit output] (merge-sub-circuit circuit sub-circuit args)]
                                [circuit (conj acc output)]))
                            [circuit []]
                            (eduction
                             (filter #(= :conj (uber/attr query-graph % :label)))
                             (map :dest)
                             (uber/out-edges query-graph node)))
                           [circuit or-last-op]
                           (reduce
                            (fn [[circuit output] output']
                              (let [add-op (->AddOperator
                                            (gensym "add-") (-get-output-type output))]
                                [(add-op-inputs circuit add-op output output') add-op]))
                            [circuit (first sub-circuit-outputs)]
                            (rest sub-circuit-outputs))]
                       (if (some? last-op)
                         (join-ops circuit or-last-op last-op)
                         [circuit or-last-op]))
            [circuit last-op])))
      [circuit input-op]
      nodes)))

 (defn- build-circuit*
   ([inputs query-graph rules]
    (build-circuit* inputs query-graph rules nil))
   ([inputs query-graph rules input-op-map & {:keys [join-unconnected?] :or {join-unconnected? false}}]
    (let [components (alg/connected-components query-graph)
          _ (when (and (> (count components) 1) (not join-unconnected?))
              (throw (Exception. "Cannot have disjoint query components")))
          root (->RootOperator (gensym "root-"))
          circuit (-> (uber/ubergraph false false)
                      (uber/add-nodes root))
          [input-op-map connect?]
          (if (map? input-op-map)
            [input-op-map false]
            [(into {}
                   (map
                    #(vector
                      %
                      (->FilterOperator
                       (gensym "input-")
                       [::input % %]
                       [[= ::input (->ValIndex 0)]
                        [= % (->ValIndex 1)]]
                       [(->ValIndex 2)])))
                   inputs)
             true])
          circuit (if (and (seq inputs) connect?)
                    (reduce
                     #(add-op-inputs %1 (val %2) root)
                     circuit input-op-map)
                    (reduce
                     #(uber/add-nodes %1 (val %2))
                     circuit input-op-map))
          [circuit last-op] (join-pattern-clauses circuit query-graph root input-op-map)
          [circuit last-op] (process-non-pattern-clauses circuit last-op query-graph rules input-op-map)
          loners (alg/loners circuit)]
      (if (and join-unconnected? (seq loners))
        (reduce
         (fn [[c op] op-2]
           (join-ops c op op-2))
         [circuit last-op]
         (eduction
          (remove #(= :root (-get-op-type %)))
          loners))
        [circuit last-op]))))

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
      (add-op-inputs circuit projection last-op))))


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

