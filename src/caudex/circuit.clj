(ns caudex.circuit
  "Functions to transform a query graph into a dbsp circuit"
  (:require [caudex.query-analyzer :as qa]
            [clojure.set :as set]
            [caudex.dbsp :refer :all]
            [caudex.utils :as utils]
            [ubergraph.alg :as alg]
            [ubergraph.core :as uber]))


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
    (-> circuit
        (add-op-inputs add-1 op-1 delay-1)
        (add-op-inputs delay-1 add-1)
        (add-op-inputs join-1 add-1 op-2)
        (add-op-inputs add-2 op-2 delay-2)
        (add-op-inputs delay-2 add-2)
        (add-op-inputs delay-3 add-2)
        (add-op-inputs join-2 op-1 delay-3)
        (add-op-inputs final-add join-1 join-2))))

(defn- join-pattern-clauses [circuit query-graph root]
  (let [start (find-starting-node query-graph)
        pattern-edges #(filterv (fn [e] (= :pattern (uber/attr query-graph e :clause-type)))
                                (uber/out-edges query-graph %))]
    (loop [processed [] queue (pattern-edges start) ret circuit]
      (let [[ret ops nodes edges] (reduce
                                   (fn [[r ops nodes edges] {:keys [src dest] :as edge}]
                                     (let [attr (uber/attr query-graph edge :label)
                                           conds
                                           (cond-> []
                                             (not (symbol? src)) (conj [= src (->ValIndex 0 0)])
                                             (not (symbol? attr)) (conj [= attr (->ValIndex 0 1)])
                                             (not (symbol? dest)) (conj [= dest (->ValIndex 0 2)]))
                                           selections
                                           (cond-> []
                                             (symbol? src) (conj (->ValIndex 0 0))
                                             (symbol? attr) (conj (->ValIndex 0 1))
                                             (symbol? dest) (conj (->ValIndex 0 2)))
                                           output-type [(filterv symbol? [src attr dest])]
                                           op (->MapOperator
                                               (gensym "datom-") nil output-type conds selections)
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
                                          (some? prev-op) (join-ops op prev-op))
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
          ret)))))

#_(defn- process-non-pattern-clauses [circuit query-graph inputs rules]
  (let [nodes (filterv #(contains? #{:or-join :not-join :pred :fn :rule}
                                   (uber/attr query-graph % :type))
                       (uber/nodes query-graph))]
    (loop [circuit circuit node (first nodes) remaining (rest nodes)]
      (let [deps (uber/in-edges query-graph node)]))))

(defn- build-circuit* [inputs query-graph rules]
  (let [components (alg/connected-components query-graph)
        _ (when (> (count components) 1)
            (throw (Exception. "Cannot have disjoint query components")))
        start (find-starting-node query-graph)
        _ (prn (utils/topsort-query-graph query-graph :start start))
        root (->RootOperator (gensym "root-"))
        circuit (-> (uber/ubergraph false false)
                    (uber/add-nodes root))
        circuit (join-pattern-clauses circuit query-graph root)
        ;circuit (process-non-pattern-clauses circuit query-graph inputs rules)
        ]
    circuit))

(defn build-circuit
  ([query]
   (build-circuit query []))
  ([query rules]
   (let [{:keys [inputs projections rules graph]} (qa/analyze query rules)
         circuit (build-circuit* inputs graph rules)]
     circuit)))

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

