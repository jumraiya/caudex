(ns caudex.circuit
  (:require [caudex.query-analyzer :as qa]
            [clojure.set :as set]
            [caudex.dbsp :as dbsp]
            [caudex.utils :as utils]
            [caudex.graph :as graph]))

(declare build-circuit*)

(declare add-op-inputs)

(def eq (vary-meta = #(assoc % :fn-sym '=)))

(def ident (vary-meta identity #(assoc % :fn-sym 'identity)))

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
    (when (some? idx)
      (dbsp/->ValIndex idx)
      ;(prn (str "Could not find " var " in " (dbsp/-get-output-type op)))
                                        ;(throw (Exception. (str "Could not find " var " in " (dbsp/-get-output-type op))))
      )))

(defn- ops-overlap? [op-1 op-2]
  (some? (seq (set/intersection
               (set (dbsp/-get-output-type op-1))
               (set (dbsp/-get-output-type op-2))))))

;; op that returns a constant value e.g. [(ground :const) ?c]
 (defn- static-op? [circuit op]
   (or
    (and
     (if-let [degree (graph/in-degree circuit op)]
      (> degree 0)
      false)
     (every?
      #(static-op? circuit %)
      (eduction
       (map :src)
       (graph/in-edges circuit op))))
    (-> op meta :static-op true?)
    (and
     (= 1 (count (dbsp/-get-input-types op)))
     (every? #(not (symbol? %)) (-> op dbsp/-get-input-types first dbsp/-to-vector)))))


(defn- get-root [circuit]
  (some #(when (= :root (dbsp/-get-op-type %)) %) (graph/nodes circuit)))

(defn- project-vars* [circuit op vars rename-map]
  (let [projection (dbsp/->FilterOperator
                    (gensym "proj-")
                    (mapv
                     #(if (contains? rename-map %)
                        (get rename-map %)
                        %)
                     (-> op dbsp/-get-output-type dbsp/-to-vector))
                    nil
                    (eduction
                     (map #(find-val-idx op %))
                     vars))]
    [(add-op-inputs circuit projection op) projection]))

(defn- project-vars-from-op
  ([circuit op vars]
   (project-vars-from-op circuit op vars {}))
  ([circuit op vars rename-map]
   (project-vars* circuit op vars rename-map)
   #_(if (= vars (-> op (dbsp/-get-output-type) (dbsp/-to-vector)))
     [circuit op]
     (project-vars* circuit op vars rename-map))))

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
         final-add (dbsp/->AddOperator (gensym "add-") (dbsp/-get-output-type join-1))
         circuit (-> circuit
                     (add-op-inputs int-1 op-1)
                     (add-op-inputs join-1 int-1 op-2)
                     (add-op-inputs int-2 op-2)
                     (add-op-inputs delay-3 int-2)
                     (add-op-inputs join-2 op-1 delay-3)
                     (add-op-inputs final-add join-1 join-2))]
     (project-vars-from-op
      circuit final-add
      (set (-> final-add dbsp/-get-output-type dbsp/-to-vector)))))

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
   (let [op-vars (-> input-op (dbsp/-get-output-type) (dbsp/-to-vector))
         ;; _ (when (static-op? circuit input-op)
         ;;     (prn "Trying to join static op with anti-join")
         ;;     #_(throw #?(:cljs (js/Error. "Trying to join static op with anti-join")
         ;;               :clj (Exception. "Trying to join static op with anti-join"))))
         [circuit joined-output] (join-ops* circuit input-op not-join-op)
         negated (dbsp/->NegOperator
                  (gensym "neg-")
                  (dbsp/-get-output-type joined-output))
         circuit (add-op-inputs circuit negated joined-output)
         [circuit proj] (project-vars-from-op
                         circuit negated op-vars)
         final-add (dbsp/->AddOperator
                    (gensym "add-")
                    op-vars)]
     [(add-op-inputs circuit final-add proj input-op) final-add]))


 (defn- join-ops
   [circuit op-1 op-2]
   (if (or (static-op? circuit op-1) (static-op? circuit op-2))
     (non-integrated-join circuit op-1 op-2)
     (join-ops* circuit op-1 op-2)))


(defn- join-ops-seq [circuit ops-seq]
  (reduce
   (fn [[c op] op-2]
     (join-ops c op op-2))
   [circuit (first ops-seq)]
   (eduction
    (remove #(= :root (dbsp/-get-op-type %)))
    (rest ops-seq))))

(defn- add-ops-seq [circuit ops-seq]
  (reduce
   (fn [[circuit output] output']
     (let [add-op (dbsp/->AddOperator
                   (gensym "add-") (dbsp/-get-output-type output))]
       [(add-op-inputs circuit add-op output output') add-op]))
   [circuit (first ops-seq)]
   (rest ops-seq)))


 (defn- consolidate-frontier
   [circuit frontier]
   (let [static-ops (filterv (partial static-op? circuit) frontier)
         [circuit frontier] (if (> (count static-ops) 1)
                              (let [[circuit op] (join-ops-seq circuit static-ops)]
                                [circuit
                                 (-> (reduce disj frontier static-ops)
                                     (conj op))])
                              [circuit frontier])]
     (loop [circuit circuit frontier frontier]
       (if-let [overlapping-pair (some (fn [op1]
                                         (some (fn [op2]
                                                 (when (and (not= op1 op2)
                                                            (or (ops-overlap? op1 op2)
                                                                (and
                                                                 (not= :anti-join (dbsp/-get-op-type op1))
                                                                 (static-op? circuit op2))))
                                                   [op1 op2]))
                                               frontier))
                                       frontier)]
         (let [[op1 op2] overlapping-pair
               [updated-circuit joined-op] (join-ops circuit op1 op2)
               updated-frontier (-> frontier
                                    (disj op1 op2)
                                    (conj joined-op))]
           (recur updated-circuit updated-frontier))
         [circuit (into #{} frontier)]))))

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
                       (not (symbol? src)) (conj [eq (dbsp/->ValIndex 0) src])
                       (not (symbol? attr)) (conj [eq (dbsp/->ValIndex 1) attr])
                       (not (symbol? dest)) (conj [eq (dbsp/->ValIndex 2) dest]))
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
        input-op-ids (into #{} (map dbsp/-get-id) (vals (dissoc input-op-map :sources :rename)))
        terminal-nodes (remove
                        #(contains? input-op-ids (dbsp/-get-id %))
                        (graph/terminal-nodes circuit))]
    [circuit (set (filterv #(not= :root (dbsp/-get-op-type %)) terminal-nodes))]))


 (defn- process-fn|pred [circuit type args frontier query-graph node input-op-map]
  (let [only-const-args? (every? #(not (symbol? %)) (mapv first args))
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
               #?(:cljs (throw (js/Error (str "Could not find " arg " in input op")))
                  :clj (throw (Exception. (str "Could not find " arg " in input op"))))
               idx)))
         args)
        [circuit frontier]
        (case type
          :pred (let [op (dbsp/->FilterOperator
                          (gensym "pred-")
                          input-type
                          [(into [(vary-meta
                                   (graph/attr query-graph node :fn)
                                   #(assoc % :fn-sym
                                           (graph/attr query-graph node :fn-sym)))]
                                 indices)]
                          nil)]
                  [(add-op-inputs circuit op last-op)
                   (conj (set frontier) op)])
          :fn (let [op (dbsp/->MapOperator (gensym "fn-")
                                           input-type
                                           output-type
                                           (vary-meta
                                            (graph/attr query-graph node :fn)
                                            #(assoc % :fn-sym
                                                    (graph/attr query-graph node :fn-sym)))
                                           indices)
                    circuit (add-op-inputs circuit op last-op)]
                #_(reduce
                   (fn [[circuit frontier] fr-op]
                     (let [[c new-op] (join-ops circuit fr-op op)]
                       [c
                        (-> frontier
                            (disj fr-op)
                            (conj new-op))]))
                   [circuit frontier]
                   frontier)
                [circuit (conj (set frontier) op)]))]
    (consolidate-frontier circuit frontier)))

(defn- add-const-input-op [circuit value & [var]]
  (let [f-op (dbsp/->MapOperator (gensym "const-")
                                 [value]
                                 [(or var value)]
                                 ident
                                 [value])]
    [(add-op-inputs circuit f-op (get-root circuit)) f-op]))


 (defn- mk-input-ops
  ([circuit sources inputs input-op-map]
   (reduce
    (fn [[c m] [in _ required?]]
      (let [[c source idx const-op?]
            (if (not (symbol? in))
              (into (add-const-input-op c in)
                    [(dbsp/->ValIndex 0) true])
              (into [c]
                    (some
                     #(when-let [idx (find-val-idx % in)]
                        [% idx false])
                     sources)))
            _ (when (and (nil? idx) (not (contains? input-op-map in)) required?)
                #?(:cljs (throw (js/Error (str "Could not find input " in)))
                   :clj (throw (Exception. (str "Could not find input " in)))))]
        (cond
          (some? idx) (let [op (cond-> (dbsp/->FilterOperator
                                        (gensym "input-")
                                        (-> source dbsp/-get-output-type dbsp/-to-vector)
                                        nil
                                        [idx])
                                 const-op? (with-meta {:static-op true}))
                            m (assoc m in op)]
                        [(add-op-inputs c op source)
                         (if (some? source)
                           (assoc-in m [:sources in] source)
                           m)])
          (contains? input-op-map in)
          [c
           (-> m
               (assoc in (get input-op-map in))
               (assoc-in [:sources in] (get-in input-op-map [:sources in])))]
          :else [c m])))
    [circuit {}]
    inputs)))


 (defn- handle-not-join [circuit frontier args rules input-op-map not-join-body]
   (let [[circuit input-ops] (mk-input-ops circuit frontier args input-op-map)
         [sub-circuit sub-circuit-frontier]
         (build-circuit* (mapv first args) not-join-body rules input-ops)
         [sub-circuit sub-circuit-frontier
          ;used-ops
          ]
         (reduce
          (fn [[sub-circuit sub-circuit-frontier frontier
                ;used-ops-seq
                ]
               op]
            (let [common-vars (set/intersection
                               (set (mapv first args))
                               (set (dbsp/-get-output-type op)))
                  _ (when (empty? common-vars)
                      #?(:cljs (throw (js/Error. "Not join has no valid outputs"))
                         :clj (throw (Exception. "Not join has no valid outputs"))))
                  [sub-circuit proj] (project-vars-from-op sub-circuit op common-vars (get input-ops :rename {}))
                  used-ops (filterv #(and (ops-overlap? % proj)
                                          true
                                          #_(not (static-op? circuit %)))
                                    (-> input-ops :sources vals set))
                  _ (when (empty? used-ops)
                      #?(:cljs (throw (js/Error. "Not join could not find original source"))
                         :clj (throw (Exception. "Not join could not find original source"))))
                  frontier (reduce disj frontier used-ops)
                  [sub-circuit anti-join-outputs] (reduce
                                                   (fn [[sub-circuit anti-join-outputs] input-op]
                                                     (let [[c a-op] (anti-join-ops sub-circuit input-op proj)]
                                                       [c (conj anti-join-outputs a-op)]))
                                                   [sub-circuit []]
                                                   used-ops)
                  [sub-circuit anti-join-output] (join-ops-seq sub-circuit anti-join-outputs)
                  sub-circuit-frontier (-> sub-circuit-frontier
                                           (disj op)
                                           ;(into anti-join-outputs)
                                           (conj anti-join-output))]
              [sub-circuit sub-circuit-frontier frontier
               ;(into used-ops-seq used-ops)
               ]))
          [sub-circuit sub-circuit-frontier
           ;[]
           ]
          sub-circuit-frontier)
         circuit (merge-sub-circuit circuit sub-circuit)
         ;frontier (reduce disj frontier used-ops)
         combined-frontier (set/union frontier sub-circuit-frontier)]
     (consolidate-frontier circuit combined-frontier)))

 (defn- merge-or-branches [circuit branches args rules input-ops]
   (reduce
    (fn [[base-circuit frontiers] branch-graph]
      (let [[sub-circuit sub-circuit-frontier] (build-circuit* args branch-graph rules input-ops)
            arg-set (into #{}
                          (map #(get (:rename input-ops) % %))
                          args)
            #_(if (not-empty (:rename input-ops))
              (-> input-ops :rename keys set)
              (set args))
                                        ;arg-set (set args)
            [sub-circuit sub-circuit-frontier] (reduce
                                                (fn [[sub-circuit sub-circuit-frontier] op]
                                                  (let [op-output (-> op dbsp/-get-output-type dbsp/-to-vector set)
                                                        [c new-op] (project-vars-from-op
                                                                    sub-circuit op
                                                                    (sort-by name
                                                                     (set/intersection
                                                                      arg-set
                                                                      op-output))
                                                                    (get input-ops :rename {}))]
                                                    [c (-> sub-circuit-frontier (disj op) (conj new-op))]))
                                                [sub-circuit sub-circuit-frontier]
                                                sub-circuit-frontier)
            merged-circuit (merge-sub-circuit base-circuit sub-circuit)]
        [merged-circuit (conj frontiers sub-circuit-frontier)]))
    [circuit []]
    branches))

 (defn- handle-or-join* [circuit frontier args rules input-ops branches]
   (let [[circuit or-frontiers] (merge-or-branches circuit branches (mapv first args) rules input-ops)
         [circuit or-outputs] (reduce
                               (fn [[circuit or-outputs] or-frontier]
                                 (let [used-ops (filterv #(some (fn [or-op]
                                                                  (when (ops-overlap? % or-op)
                                                                    %))
                                                                or-frontier)
                                                         (-> input-ops :sources vals))
                                       [circuit or-output] (if (seq used-ops)
                                                             (let [[circuit or-frontier] (consolidate-frontier circuit (into or-frontier used-ops))
                                                                   _ (when (> (count or-frontier) 1)
                                                                       #?(:cljs (throw (js/Error. "Or branch resulted in more than one op"))
                                                                          :clj (throw (Exception. "Or branch resulted in more than one op"))))
                                                                   proj-vars (->> or-frontier first dbsp/-get-output-type dbsp/-to-vector set (sort-by name))
                                                                   [circuit output] (project-vars-from-op circuit (first or-frontier) proj-vars)]
                                                               [circuit [output]])
                                                             [circuit or-frontier])]
                                   [circuit (into or-outputs or-output)]))
                               [circuit []]
                               or-frontiers)
         output-groups (group-by dbsp/-get-output-type or-outputs)
         _ (when (> (count output-groups) 1)
             (throw #?(:cljs (js/Error. (str "Or join resulted in disjoint output types " (keys output-groups)))
                       :clj (Exception. (str "Or join resulted in disjoint output types " (keys output-groups))))))
         [circuit frontier] (reduce
                             (fn [[circuit frontier] [_ ops]]
                               (let [[circuit added-op] (add-ops-seq circuit ops)]
                                 [circuit (conj frontier added-op)]))
                             [circuit frontier]
                             output-groups)]
     (consolidate-frontier circuit frontier)))

(defn- handle-or-join [circuit frontier args rules input-op-map query-graph or-join-body]
  (let [[circuit input-ops] (mk-input-ops circuit frontier args input-op-map)
         branches (eduction
                   (filter #(= :conj (graph/attr query-graph % :label)))
                   (map :dest)
                   (graph/out-edges query-graph or-join-body))]
    (handle-or-join* circuit frontier args rules input-ops branches)))



 (defn- handle-rule-clause [circuit frontier args rules input-op-map rule-name]
   (let [rule-args (-> rules (get rule-name) :branches first :args)
         branches (into []
                        (map #(let [rule-args (:args %)
                                    rename-map (into {}
                                                     (filter (fn [[_ v]] (symbol? v)))
                                                     (zipmap rule-args (mapv first args)))
                                    body (:graph %)]
                                (utils/remap-nodes body rename-map)))
                        (get-in rules [rule-name :branches]))
         [circuit input-op-map]
         (reduce
          (fn [[c m] [arg call-arg]]
            (if (contains? (:sources m) arg)
              m
              (let [[c op] (add-const-input-op c call-arg arg)]
                [c (-> m
                       (assoc arg op)
                       (assoc-in [:sources arg] op))])))
          [circuit input-op-map]
          (eduction
           (remove #(-> % val symbol?))
           (zipmap rule-args (mapv first args))))
         [circuit input-ops]
         (mk-input-ops circuit frontier (mapv (fn [r [a idx r?]] (if (symbol? a) [a idx r?] [r idx r?])) rule-args args) input-op-map)]
     (handle-or-join* circuit frontier args rules input-ops branches)))


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
                :rule
                (handle-rule-clause circuit frontier args rules input-op-map (graph/attr query-graph node :fn))
                [circuit frontier])]
          (if (seq nodes)
            (recur circuit frontier nodes)
            [circuit frontier])))
      [circuit frontier])))

 (defn- build-circuit*
  ([inputs query-graph rules]
   (build-circuit* inputs query-graph rules nil))
  ([inputs query-graph rules input-op-map
     ;& {:keys [join-unconnected?] :or {join-unconnected? false}}
    ]
   (let [;; components (graph/connected-components query-graph)
          ;; _ (when (and (> (count components) 1) (not join-unconnected?))
          ;;     #?(:cljs (prn "Cannot have disjoint query components")
          ;;        :clj (prn "Warning disjoint components in query")
          ;;        ))
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
                      [[eq ::input (dbsp/->ValIndex 0)]
                       [eq % (dbsp/->ValIndex 1)]]
                      [(dbsp/->ValIndex 2)])))
                  inputs)
            true])
         circuit (if (and (seq inputs) connect?)
                   (reduce
                    #(add-op-inputs %1 (val %2) root)
                    circuit input-op-map)
                   (reduce
                    #(graph/add-nodes %1 (val %2))
                    circuit (dissoc input-op-map :sources :rename)))
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
           (join-ops-seq circuit frontier)
           [circuit (first frontier)])
         proj-vars (into [] (comp (map :symbol) (filter some?)) projections)
         projection (dbsp/->FilterOperator
                     (gensym "proj-")
                     (dbsp/-get-output-type last-op)
                     []
                     (mapv #(find-val-idx last-op %) proj-vars))
         c (add-op-inputs circuit projection last-op)
         ;;[c] (project-vars-from-op circuit last-op proj-vars)
         ]
     c)))

(comment

  (build-circuit
   '[:find ?a ?dest ?locked
     :in $ %
     :where
     [?p :object/description "player"]
     [?p :object/location ?loc]
     (new-action-added? ?a :move ?arg :action/move-processed?)
     [(keyword ?arg) ?wall]
     (or-join [?loc ?wall ?dest ?locked]
              (and
               [?exit :exit/location-1 ?loc]
               [?exit :exit/location-1-wall ?wall]
               [?exit :exit/location-2 ?dest]
               [?exit :exit/locked? ?locked])
              (and
               [?exit :exit/location-2 ?loc]
               [?exit :exit/location-2-wall ?wall]
               [?exit :exit/location-1 ?dest]
               [?exit :exit/locked? ?locked])
              (and
               (not-join [?loc ?wall]
                         (or-join [?loc ?wall]
                                  (and
                                   [?e :exit/location-2 ?loc]
                                   [?e :exit/location-2-wall ?wall])
                                  (and
                                   [?e :exit/location-1 ?loc]
                                   [?e :exit/location-1-wall ?wall])))
               [(ground :not-found) ?dest]
               [(ground false) ?locked]))]
   '[[(new-action-added? [?action ?action-type ?action-arg ?handler-attr])
      [?action :action/type ?action-type]
      [?action :action/arg ?action-arg]
      (not-join [?action ?handler-attr]
                [?action ?handler-attr true])]])

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

