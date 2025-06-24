(ns caudex.circuit
  (:require [caudex.query-analyzer :as qa]
            [clojure.set :as set]
            [caudex.dbsp :as dbsp]
            [caudex.utils :as utils]
            [caudex.graph :as graph]))

(declare build-circuit*)

(defn- find-val-idx [op var]
  (let [idx (.indexOf (dbsp/-to-vector (dbsp/-get-output-type op)) var)]
    (if (not= -1 idx)
      (dbsp/->ValIndex idx)
      (prn (str "Could not find " var " in " (dbsp/-get-output-type op)))
      ;(throw (Exception. (str "Could not find " var " in " (dbsp/-get-output-type op))))
      )))

#_(defn- get-root [circuit]
  (some #(when (= :root (dbsp/-get-op-type %)) %) (graph/nodes circuit)))

(defn- find-starting-nodes
  ([graph]
   (find-starting-nodes graph (graph/nodes graph)))
  ([graph nodes]
   (let [pattern-nodes
         (into #{}
               (filter #(true?
                         (some (fn [e] (when (= :pattern (graph/attr graph e :clause-type))
                                         true))
                               (graph/out-edges graph %))))
               nodes)]
     (or
      (when-let [nodes
                 (seq
                  (filterv
                   (fn [node]
                     (and (contains? pattern-nodes node)
                          (or (= 0 (graph/in-degree graph node))
                              (nil? (some #(when (= :pattern (graph/attr graph % :clause-type))
                                             %)
                                          (graph/in-edges graph node))))))
                   nodes))]
        nodes)
      [(first pattern-nodes)]))))

(defn- add-op-inputs [circuit op & inputs]
  (reduce
   (fn [c [idx in]]
     (graph/add-directed-edges c [in op {:arg idx}]))
   circuit
   (map-indexed vector inputs)))

 (defn- join-ops
   ([circuit op-1 op-2]
    (join-ops circuit op-1 op-2 false))
   ([circuit op-1 op-2 inverse?]
    (let [
          int-1 (dbsp/->IntegrationOperator (gensym "integrate-") (dbsp/-get-output-type op-1))
          ;add-1 (dbsp/->AddOperator (gensym "add-") (dbsp/-get-output-type op-1))
                                        ; delay-1 (dbsp/->DelayFeedbackOperator (gensym "delay-feedback-") (dbsp/-get-output-type op-1))
          ;add-2 (dbsp/->AddOperator (gensym "add-") (dbsp/-get-output-type op-2))
           int-2 (dbsp/->IntegrationOperator (gensym "integrate-") (dbsp/-get-output-type op-2))
          ;delay-2 (dbsp/->DelayFeedbackOperator (gensym "delay-feedback-") (dbsp/-get-output-type op-2))
          constraints (dbsp/-get-join-constraints
                       (dbsp/-get-output-type op-1) (dbsp/-get-output-type op-2))
          constraints (if inverse?
                        (mapv (fn [[pred & args :as c]]
                                (if (= pred =)
                                  (into [not=] args)
                                  c))
                              constraints)
                        constraints)
          join-1 (dbsp/->JoinOperator
                  (gensym "join-")
                  (dbsp/-get-output-type op-1)
                  (dbsp/-get-output-type op-2)
                  constraints)
          join-2 (dbsp/->JoinOperator
                  (gensym "join-")
                  (dbsp/-get-output-type op-1)
                  (dbsp/-get-output-type op-2)
                  constraints)
          delay-3 (dbsp/->DelayOperator (gensym "delay-") (dbsp/-get-output-type op-2))
          final-add (dbsp/->AddOperator (gensym "add-") (dbsp/-get-output-type join-1))]
      [(-> circuit
           ;(add-op-inputs add-1 op-1 delay-1)
           (add-op-inputs int-1 op-1)
           ;(add-op-inputs delay-1 add-1)
           ;(add-op-inputs join-1 add-1 op-2)
           (add-op-inputs join-1 int-1 op-2)
           ;(add-op-inputs add-2 op-2 delay-2)
           ;(add-op-inputs delay-2 add-2)
           ;(add-op-inputs delay-3 add-2)
           (add-op-inputs int-2 op-2)
           (add-op-inputs delay-3 int-2)
           (add-op-inputs join-2 op-1 delay-3)
           (add-op-inputs final-add join-1 join-2))
       final-add])))

(defn- merge-sub-circuit [circuit sub-circuit args]
  (let [root (utils/get-root-node circuit)
        ;_ (utils/prn-graph sub-circuit "subgraph")
        sub-circuit-last-op (last (utils/topsort-circuit sub-circuit))
        projection (dbsp/->FilterOperator
                    (gensym "proj-")
                    (dbsp/-get-output-type sub-circuit-last-op)
                    nil
                    (mapv #(find-val-idx sub-circuit-last-op (first %)) args))
        sub-circuit (add-op-inputs sub-circuit projection sub-circuit-last-op)
        ;; _ (prn (utils/datafy-circuit sub-circuit))
        ;; _ (prn (utils/datafy-circuit circuit))
        sub-circuit-root (utils/get-root-node sub-circuit)
        ;; _ (prn "sub circuit root" sub-circuit-root)
        ;; _ (prn "main circuit root" root)
        circuit (reduce
                 (fn [circuit {:keys [src dest] :as edge}]
                   (let [attrs (graph/attrs sub-circuit edge)]
                     (if (= sub-circuit-root src)
                       (graph/add-directed-edges circuit [root dest attrs])
                       (graph/add-directed-edges circuit [src dest attrs]))))
                 circuit
                 (graph/edges sub-circuit))
        ;_ (prn (utils/datafy-circuit circuit))
        ]
    [circuit projection]))

(defn- join-with-inputs [circuit op input-op-map]
  (let [o-type (-> op dbsp/-get-output-type dbsp/-to-vector set)]
    (reduce
     (fn [[ret last-op] input-op]
       (join-ops ret last-op input-op))
     [circuit op]
     (eduction
      (filter #(contains? o-type (key %)))
      (map val)
      (filter #(= 0 (graph/out-degree circuit %)))
      input-op-map))))

(defn- join-pattern-clauses* [circuit query-graph root input-op-map]
  (let [starting-nodes (find-starting-nodes query-graph)
        pattern-edges #(filterv
                        (fn [e] (= :pattern (graph/attr query-graph e :clause-type)))
                        (graph/out-edges query-graph %))
        var? #(and (symbol? %) (not= '_ %))
        q (mapcat pattern-edges starting-nodes)]
    (loop [processed [] queue q ret circuit last-op nil]
      (let [[ret ops nodes edges last-op]
            (reduce
             (fn [[r ops nodes edges last-op] {:keys [src dest] :as edge}]
               (let [attr (graph/attr query-graph edge :label)
                     conds
                     (cond-> []
                       (not (symbol? src)) (conj [= (dbsp/->ValIndex 0) src])
                       (not (symbol? attr)) (conj [= (dbsp/->ValIndex 1) attr])
                       (not (symbol? dest)) (conj [= (dbsp/->ValIndex 2) dest]))
                     selections
                     (cond-> []
                       (var? src) (conj (dbsp/->ValIndex 0))
                       (var? attr) (conj (dbsp/->ValIndex 1))
                       (var? dest) (conj (dbsp/->ValIndex 2)))
                     output-type (filterv var? [src attr dest])
                     op (dbsp/->FilterOperator
                         (gensym "datom-") [src attr dest] conds selections)
                     ;; Join with previously processed op that has a common var
                     prev-op
                     (some #(let [vars (dbsp/-get-output-type %)]
                              (when (seq (set/intersection (set vars) (set output-type)))
                                %))
                           (if (some? last-op)
                             (into [last-op] (into ops processed))
                             (into ops processed)))
                     [ret last-op] (cond->
                                       (-> r
                                           (graph/add-nodes op)
                                           (add-op-inputs op root))
                                       (some? prev-op) (join-ops op prev-op)
                                       (nil? prev-op) (vector op))
                     [ret last-op] (join-with-inputs ret last-op input-op-map)]
                 [ret
                  (conj ops op)
                  (conj nodes dest)
                  (conj edges edge)
                  last-op]))
             [ret [] [] #{} last-op]
             queue)
            queue (into [] (comp
                            (map #(pattern-edges %))
                            cat
                            (filter #(not (contains? edges %))))
                        nodes)
            processed (into processed ops)]
        (if (seq queue)
          (recur processed queue ret last-op)
          [ret last-op])))))

(defn- join-pattern-clauses [circuit query-graph root input-op-map]
  (let [[circuit last-op] (join-pattern-clauses* circuit query-graph root input-op-map)
        input-op-ids (into #{} (map dbsp/-get-id) (vals input-op-map))
        terminal-nodes (remove
                        #(or (and (some? last-op)
                                  (= (dbsp/-get-id last-op) (dbsp/-get-id %)))
                             (contains? input-op-ids (dbsp/-get-id %)))
                        (graph/terminal-nodes circuit))]
    (if (seq terminal-nodes)
      (do
        (prn "joining" last-op terminal-nodes)
        (reduce
         (fn [[c op] op-2]
           (join-ops c op op-2))
         [circuit last-op]
         (eduction
          (remove #(= :root (dbsp/-get-op-type %)))
          terminal-nodes)))
      [circuit last-op])))

(defn- process-fn|pred [circuit type args last-op query-graph node input-op-map]
  (let [o-type (when (some? last-op)
                 (-> last-op dbsp/-get-output-type dbsp/-to-vector set))
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
               #?(:cljs (prn (str "Could not find " arg " in input op"))
                  :clj (throw (Exception. (str "Could not find " arg " in input op"))))
               idx)))
         args)]
    (case type
      :pred (let [op (dbsp/->FilterOperator
                      (gensym "pred-")
                      (dbsp/-get-output-type last-op)
                      [(into [(graph/attr query-graph node :fn)]
                             indices)]
                      nil)]
              [(add-op-inputs circuit op last-op) op])
      :fn (let [binding (some #(when (= :binding (graph/attr query-graph % :label)) %)
                              (graph/out-edges query-graph node))
                op (dbsp/->MapOperator (gensym "fn-")
                                       (dbsp/-get-output-type last-op)
                                       (conj (-> last-op
                                                 (dbsp/-get-output-type) (dbsp/-to-vector))
                                             (:dest binding))
                                       (graph/attr query-graph node :fn)
                                       indices)]
            [(add-op-inputs circuit op last-op) op]))))


(defn- mk-input-ops [circuit source inputs input-op-map]
  (reduce
   (fn [[c m] [in _ required?]]
     (let [idx (when (some? source)
                 (find-val-idx source in))
           _ (when (and (nil? idx) (not (contains? input-op-map in)) required?)
               #?(:cljs (prn (str "Could not find input " in))
                  :clj (throw (Exception. (str "Could not find input " in)))))]
       (cond
         (some? idx) (let [op (dbsp/->FilterOperator
                               (gensym "input-")
                               (dbsp/-get-output-type source)
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
                           (graph/attr query-graph % :type))
               (utils/topsort-query-graph query-graph))]
    (reduce
     (fn [[circuit last-op] node]
       (let [args (sort-by
                   second
                   (into []
                         (comp
                          (filter #(= :arg (first (graph/attr query-graph % :label))))
                          (map #(vector (:src %) (second (graph/attr query-graph % :label)) (graph/attr query-graph % :required?))))
                         (graph/in-edges query-graph node)))]
         (case (graph/attr query-graph node :type)
           (:pred :fn)
           (process-fn|pred circuit (graph/attr query-graph node :type) args last-op query-graph node input-op-map)
           :not-join (let [[circuit input-ops] (mk-input-ops circuit last-op args input-op-map)
                           [sub-circuit] (build-circuit* (mapv first args) node rules input-ops)
                           [circuit not-join-last-op] (merge-sub-circuit circuit sub-circuit args)]
                       (if (some? last-op)
                         (join-ops circuit not-join-last-op last-op true)
                         (let [neg-op (dbsp/->NegOperator
                                       (gensym "neg-")
                                       (dbsp/-get-output-type not-join-last-op))]
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
                            (filter #(= :conj (graph/attr query-graph % :label)))
                            (map :dest)
                            (graph/out-edges query-graph node)))
                          [circuit or-last-op]
                          (reduce
                           (fn [[circuit output] output']
                             (let [add-op (dbsp/->AddOperator
                                           (gensym "add-") (dbsp/-get-output-type output))]
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
   (let [components (graph/connected-components query-graph)
         _ (when (and (> (count components) 1) (not join-unconnected?))
             #?(:cljs (prn "Cannot have disjoint query components")
                :clj (throw (Exception. "Cannot have disjoint query components"))))
         root (dbsp/->RootOperator (gensym "root-"))
         circuit (-> (graph/new-graph)
                     (graph/add-nodes root))
         [input-op-map connect?]
         (if (map? input-op-map)
           [input-op-map false]
           [(into {}
                  (map
                   #(vector
                     %
                     (dbsp/->FilterOperator
                      (gensym "input-")
                      [::input % %]
                      [[= ::input (dbsp/->ValIndex 0)]
                       [= % (dbsp/->ValIndex 1)]]
                      [(dbsp/->ValIndex 2)])))
                  inputs)
            true])
         circuit (if (and (seq inputs) connect?)
                   (reduce
                    #(add-op-inputs %1 (val %2) root)
                    circuit input-op-map)
                   (reduce
                    #(graph/add-nodes %1 (val %2))
                    circuit input-op-map))
         [circuit last-op] (join-pattern-clauses circuit query-graph root input-op-map)
         [circuit last-op] (process-non-pattern-clauses circuit last-op query-graph rules input-op-map)
         loners (graph/loners circuit)]
                                        ;(prn (utils/datafy-circuit circuit))
     (if (and join-unconnected? (seq loners))
       (reduce
        (fn [[c op] op-2]
          (join-ops c op op-2))
        [circuit last-op]
        (eduction
         (remove #(= :root (dbsp/-get-op-type %)))
         loners))
       [circuit last-op]))))


(defn build-circuit
  ([query]
   (build-circuit query []))
  ([query rules]
   (let [{:keys [inputs projections rules graph]} (qa/analyze query rules)
         [circuit last-op] (build-circuit* inputs graph rules)
         proj-vars (into [] (comp (map :symbol) (filter some?)) projections)
         projection (dbsp/->FilterOperator
                     (gensym "proj-")
                     (dbsp/-get-output-type last-op)
                     []
                     (mapv #(find-val-idx last-op %) proj-vars))
         c (add-op-inputs circuit projection last-op)]
     c)))


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

