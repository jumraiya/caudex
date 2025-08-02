(ns caudex.circuit
  (:require [caudex.query-analyzer :as qa]
            [clojure.set :as set]
            [caudex.dbsp :as dbsp]
            [caudex.utils :as utils]
            [caudex.graph :as graph]
            [caudex.circuit :as circuit]))

(declare build-circuit*)

(declare add-op-inputs)


(defn- last-index-of [coll item]
  (->> coll
       (map-indexed vector)
       (filter #(= (second %) item))
       last
       first))
;; TODO determine if using last index is truly correct
;; Anti joins result in zsets with vars that are equals but actual values differ
;; For not-joins we are only interested in the input zset so we pick the last occurence
(defn- find-val-idx [op var]
  (let [idx (last-index-of (dbsp/-to-vector (dbsp/-get-output-type op)) var)]
    (if (some? idx)
      (dbsp/->ValIndex idx)
      (prn (str "Could not find " var " in " (dbsp/-get-output-type op)))
                                        ;(throw (Exception. (str "Could not find " var " in " (dbsp/-get-output-type op))))
      )))

(defn- ops-overlap? [op-1 op-2]
  (some? (seq (set/intersection
               (set (dbsp/-get-output-type op-1))
               (set (dbsp/-get-output-type op-2))))))

;; op that returns a constant value e.g. [(ground :const) ?c]
(defn- static-op? [op]
  (and
   (= 1 (count (dbsp/-get-input-types op)))
   (every? #(not (symbol? %)) (-> op dbsp/-get-input-types first dbsp/-to-vector))))


(defn- get-root [circuit]
  (some #(when (= :root (dbsp/-get-op-type %)) %) (graph/nodes circuit)))

#trace
 (defn- project-vars-from-op [circuit op vars]
   (if (and (= :anti-join (dbsp/-get-op-type op))
            (= (set vars) (-> op (dbsp/-get-output-type) (dbsp/-to-vector) set)))
     [circuit op]
     (let [projection (dbsp/->FilterOperator
                       (gensym "proj-")
                       (dbsp/-get-output-type op)
                       nil
                       (eduction
                        (map #(find-val-idx op %))
                        vars))]
       [(add-op-inputs circuit projection op) projection])))

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


(defn- join-ops* [circuit op-1 op-2]
  (let [int-1 (dbsp/->IntegrationOperator (gensym "integrate-") (dbsp/-get-output-type op-1))
        int-2 (dbsp/->IntegrationOperator (gensym "integrate-") (dbsp/-get-output-type op-2))
        constraints (dbsp/-get-join-constraints
                     (dbsp/-get-output-type op-1) (dbsp/-get-output-type op-2))
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
         (add-op-inputs int-1 op-1)
         (add-op-inputs join-1 int-1 op-2)
         (add-op-inputs int-2 op-2)
         (add-op-inputs delay-3 int-2)
         (add-op-inputs join-2 op-1 delay-3)
         (add-op-inputs final-add join-1 join-2))
     final-add]))

(defn- non-integrated-join [circuit op-1 op-2]
  (let [constraints (dbsp/-get-join-constraints
                     (dbsp/-get-output-type op-1) (dbsp/-get-output-type op-2))
        join-op (dbsp/->JoinOperator
                 (gensym "join-")
                 (dbsp/-get-output-type op-1)
                 (dbsp/-get-output-type op-2)
                 constraints)]
    [(add-op-inputs circuit join-op op-1 op-2) join-op]))


(defn- anti-join-ops [circuit input-op not-join-op]
  (let [negated (dbsp/->NegOperator
                 (gensym "neg-")
                 (dbsp/-get-output-type not-join-op))
        op-vars (-> input-op (dbsp/-get-output-type) (dbsp/-to-vector))
        circuit (add-op-inputs circuit negated not-join-op)
        [circuit joined-output] (join-ops* circuit input-op negated)
        [circuit proj] (project-vars-from-op
                        circuit joined-output op-vars)
        final-add (dbsp/->AddOperator
                   (gensym "add-")
                   op-vars)]
    [(add-op-inputs circuit final-add proj input-op) final-add]))

(defn- join-ops
  [circuit op-1 op-2]
  (let [[anti-join? op-1 op-2]
        (cond
          (= :anti-join (dbsp/-get-op-type op-1)) [true op-2 op-1]
          (= :anti-join (dbsp/-get-op-type op-2)) [true op-1 op-2]
          :else [false op-1 op-2])
        join-type (cond
                    (or (static-op? op-1) (static-op? op-2)) non-integrated-join
                    anti-join? anti-join-ops
                    :else join-ops*)]
    (join-type circuit op-1 op-2)))

(defn- consolidate-frontier
  [circuit frontier]
  (loop [circuit circuit frontier frontier]
    (if-let [overlapping-pair (some (fn [op1]
                                      (some (fn [op2]
                                              (when (and (not= op1 op2)
                                                         (or (ops-overlap? op1 op2)
                                                             (static-op? op2)))
                                                [op1 op2]))
                                            frontier))
                                    frontier)]
      (let [[op1 op2] overlapping-pair
            [updated-circuit joined-op] (join-ops circuit op1 op2)
            updated-frontier (-> frontier
                                 (disj op1 op2)
                                 (conj joined-op))]
        (recur updated-circuit updated-frontier))
      [circuit frontier])))

(defn- merge-sub-circuit [circuit sub-circuit]
  (let [root (utils/get-root-node circuit)
        sub-circuit-root (utils/get-root-node sub-circuit)
        circuit (reduce
                 (fn [circuit {:keys [src dest] :as edge}]
                   (let [attrs (graph/attrs sub-circuit edge)]
                     (if (= sub-circuit-root src)
                       (graph/add-directed-edges circuit [root dest attrs])
                       (graph/add-directed-edges circuit [src dest attrs]))))
                 circuit
                 (graph/edges sub-circuit))]
    circuit))

(defn- join-with-inputs [circuit op input-op-map]
  (let [o-type (-> op dbsp/-get-output-type dbsp/-to-vector set)]
    (reduce
     (fn [[ret last-op] input-op]
       (join-ops ret last-op input-op))
     [circuit op]
     (eduction
      (filter #(contains? o-type (key %)))
      (map val)
      ;; Don't join inputs that already have been consumed
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
  (let [[circuit _last-op] (join-pattern-clauses* circuit query-graph root input-op-map)
        input-op-ids (into #{} (map dbsp/-get-id) (vals input-op-map))
        terminal-nodes (remove
                        #(contains? input-op-ids (dbsp/-get-id %))
                        (graph/terminal-nodes circuit))]
    [circuit (set terminal-nodes)]))

#trace
 (defn- process-fn|pred [circuit type args frontier query-graph node input-op-map]
   (let [only-const-args? (every? #(not (symbol? %)) args)
         ops (into []
                   (comp
                    (map first)
                    (filter symbol?)
                    (map #(or
                           (some (fn [op]
                                   (when (contains? (set (dbsp/-get-output-type op)) %)
                                     op))
                                 frontier)
                           (get input-op-map %)))
                    (filter some?))
                   args)

         [circuit last-op frontier]
         (reduce
          (fn [[c op frontier] op-2]
            (let [[c last-op] (join-ops c op op-2)]
              [c last-op (-> frontier (disj op op-2) (conj last-op))]))
          [circuit (first ops) frontier]
          (rest ops))
         last-op (if only-const-args?
                   (get-root circuit)
                   last-op)

         binding (some #(when (= :binding (graph/attr query-graph % :label)) %)
                       (graph/out-edges query-graph node))
         [input-type output-type] (if only-const-args?
                                    [(mapv first args)
                                     [(:dest binding)]]
                                    [(dbsp/-get-output-type last-op)
                                     (conj (-> last-op
                                               (dbsp/-get-output-type) (dbsp/-to-vector))
                                           (:dest binding))])
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
                       input-type
                       [(into [(graph/attr query-graph node :fn)]
                              indices)]
                       nil)]
               [(add-op-inputs circuit op last-op)
                (conj (set frontier) op)])
       :fn (let [op (dbsp/->MapOperator (gensym "fn-")
                                        input-type
                                        output-type
                                        (graph/attr query-graph node :fn)
                                        indices)]
             [(add-op-inputs circuit op last-op) (conj (set frontier) op)]))))

 (defn- mk-input-ops [circuit sources inputs input-op-map]
  (reduce
   (fn [[c m used-sources] [in _ required?]]
     (let [[source idx]
           (some
            #(when-let [idx (find-val-idx % in)]
               [% idx])
            sources)
           _ (when (and (nil? idx) (not (contains? input-op-map in)) required?)
               #?(:cljs (prn (str "Could not find input " in))
                  :clj (throw (Exception. (str "Could not find input " in)))))]
       (cond
         (some? idx) (let [op (dbsp/->FilterOperator
                               (gensym "input-")
                               (dbsp/-get-output-type source)
                               nil
                               [idx])]
                       [(add-op-inputs c op source) (assoc m in op)
                        (if (some? source) (conj used-sources source) used-sources)])
         (contains? input-op-map in) [c (assoc m in (get input-op-map in))]
         :else [c m])))
   [circuit {} #{}]
   inputs))
#trace
 (defn- handle-not-join [circuit frontier args rules input-op-map not-join-body]
   (let [[circuit input-ops] (mk-input-ops circuit frontier args input-op-map)
         [sub-circuit sub-circuit-frontier]
         (build-circuit* (mapv first args) not-join-body rules input-ops)
         [sub-circuit sub-circuit-frontier]
         (reduce
          (fn [[sub-circuit sub-circuit-frontier] op]
            (let [common-vars (set/intersection
                               (set (mapv first args))
                               (set (dbsp/-get-output-type op)))
                  _ (when (empty? common-vars)
                      (throw (Exception. "Not join has no valid outputs")))
                  [sub-circuit proj] (project-vars-from-op sub-circuit op common-vars)
                  neg-op (dbsp/->AntiJoinOperator
                          (gensym "anti-join-")
                          (dbsp/-get-output-type proj))
                  sub-circuit (add-op-inputs sub-circuit neg-op proj)]
              [sub-circuit (-> sub-circuit-frontier (disj op) (conj neg-op))]))
          [sub-circuit sub-circuit-frontier]
          sub-circuit-frontier)
         circuit (merge-sub-circuit circuit sub-circuit)
         combined-frontier (set/union frontier sub-circuit-frontier)
         [circuit consolidated-frontier]
         (consolidate-frontier circuit combined-frontier)
         ;; _  (when (> (count consolidated-frontier) 1)
         ;;      (throw (Exception. "Not join resulted in more than one operator")))
         ;; not-join-last-op (first consolidated-frontier)
         ;; neg-op (dbsp/->NegOperator
         ;;         (gensym "neg-")
         ;;         (dbsp/-get-output-type not-join-last-op))
         ]
     [circuit consolidated-frontier]
     #_[(add-op-inputs circuit neg-op not-join-last-op)
        (-> consolidated-frontier
            (disj not-join-last-op)
            (conj neg-op))]))

#trace
 (defn- merge-or-branches [circuit frontier branches args rules input-ops]
   (let [projection-vars (sort (into
                                (set args)
                                (comp
                                 (map #(dbsp/-get-output-type %))
                                 (map #(dbsp/-to-vector %))
                                 cat)
                                frontier))]
     (reduce
      (fn [[base-circuit projections] branch-graph]
        (let [[sub-circuit sub-circuit-frontier]
              (build-circuit* args branch-graph rules input-ops)
              sub-circuit-frontier
              (into #{}
                    (remove #(= :root (dbsp/-get-op-type %)))
                    sub-circuit-frontier)
              [sub-circuit sub-circuit-frontier]
              (reduce
               (fn [[sub-circuit sub-circuit-frontier] op]
                 (let [common-vars (set/intersection
                                    (set args)
                                    (set (dbsp/-get-output-type op)))
                       _ (when (empty? common-vars)
                           (throw (Exception. "Or branch has no valid outputs")))
                       [sub-circuit proj]
                       (if (static-op? op)
                         [sub-circuit op]
                         (project-vars-from-op sub-circuit op common-vars))]
                   [sub-circuit (-> sub-circuit-frontier (disj op) (conj proj))]))
               [sub-circuit sub-circuit-frontier]
               sub-circuit-frontier)

              merged-circuit (merge-sub-circuit base-circuit sub-circuit)
              combined-frontier (into #{}
                                      (remove #(= :root (dbsp/-get-op-type %)))
                                      (set/union frontier sub-circuit-frontier))
              [final-circuit consolidated-frontier] (consolidate-frontier merged-circuit combined-frontier)
              _  (when (> (count consolidated-frontier) 1)
                   (prn "Or branch resulted in more than one operator")
                   ;(throw (Exception. "Or branch resulted in more than one operator"))
                   )
              last-op (first consolidated-frontier)
              [final-circuit projection]
              (project-vars-from-op final-circuit last-op projection-vars)]
          [final-circuit (conj projections projection)]))
      [circuit []]
      branches)))
#trace
(defn- handle-or-join [circuit frontier args rules input-op-map query-graph or-join-body]
  (let [[circuit input-ops] (mk-input-ops circuit frontier args input-op-map)
        branches (eduction
                  (filter #(= :conj (graph/attr query-graph % :label)))
                  (map :dest)
                  (graph/out-edges query-graph or-join-body))
        [circuit projections] (merge-or-branches
                               circuit frontier branches (mapv first args) rules input-ops)
        [circuit] (reduce
                   (fn [[circuit output] output']
                     (let [add-op (dbsp/->AddOperator
                                   (gensym "add-") (dbsp/-get-output-type output))]
                       [(add-op-inputs circuit add-op output output') add-op]))
                   [circuit (first projections)]
                   (rest projections))]
    [circuit (set (graph/terminal-nodes circuit))]))

 (defn- process-non-pattern-clauses
   "Processes non datom clauses, all required inputs are joined into a single operator"
   [circuit frontier query-graph rules input-op-map]
   (let [nodes (filterv
                #(contains? #{:or-join :not-join :pred :fn :rule}
                            (graph/attr query-graph % :type))
                (utils/topsort-query-graph query-graph))]
     (if (seq nodes)
       (loop [circuit circuit frontier frontier nodes nodes]
         (let [[node & nodes] nodes
               args (->>
                     (into []
                           (comp
                            (filter #(= :arg (first (graph/attr query-graph % :label))))
                            (map #(vector (:src %) (second (graph/attr query-graph % :label)) (graph/attr query-graph % :required?))))
                           (graph/in-edges query-graph node))
                     (sort-by second))
               [circuit frontier]
               (case (graph/attr query-graph node :type)
                 (:pred :fn)
                 (process-fn|pred circuit (graph/attr query-graph node :type) args frontier query-graph node input-op-map)
                 :not-join
                 (handle-not-join circuit frontier args rules input-op-map node)
                 :or-join
                 (handle-or-join circuit frontier args rules input-op-map query-graph node)
                 [circuit frontier])]
           (if (seq nodes)
             (recur circuit frontier nodes)
             [circuit frontier])))
       [circuit frontier])))

(defn- build-circuit*
  ([inputs query-graph rules]
   (build-circuit* inputs query-graph rules nil))
  ([inputs query-graph rules input-op-map & {:keys [join-unconnected?] :or {join-unconnected? false}}]
   (let [components (graph/connected-components query-graph)
         _ (when (and (> (count components) 1) (not join-unconnected?))
             (caudex.utils/prn-graph query-graph)
             #?(:cljs (prn "Cannot have disjoint query components")
                :clj (prn "Warning disjoint components in query")
                ;(throw (Exception. "Cannot have disjoint query components"))
                ))
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
         [circuit frontier] (join-pattern-clauses circuit query-graph root input-op-map)
         [circuit frontier] (process-non-pattern-clauses circuit frontier query-graph rules input-op-map)]
     [circuit frontier])))

(defn build-circuit
  ([query]
   (build-circuit query []))
  ([query rules]
   (let [{:keys [inputs projections rules graph]} (qa/analyze query rules)
         [circuit frontier] (build-circuit* inputs graph rules)
         [circuit last-op]
         (if (> (count frontier) 1)
           (reduce
            (fn [[c op] op-2]
              (join-ops c op op-2))
            [circuit (first frontier)]
            (eduction
             (remove #(= :root (dbsp/-get-op-type %)))
             (rest frontier)))
           [circuit (first frontier)])
         proj-vars (into [] (comp (map :symbol) (filter some?)) projections)
         projection (dbsp/->FilterOperator
                     (gensym "proj-")
                     (dbsp/-get-output-type last-op)
                     []
                     (mapv #(find-val-idx last-op %) proj-vars))
         c (add-op-inputs circuit projection last-op)
         ;; [c] (project-vars-from-op circuit last-op proj-vars)
         ]
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

