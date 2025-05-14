(ns caudex.query-analyzer
  "Functions for processing a query and generating a graph from it"
  (:require [datascript.parser :as ds.p]
            [datascript.built-ins :as d.fns]
            [caudex.graph :as graph]
            [clojure.walk :as walk]))


(declare process-or-join)

(declare process-not-join)

(defn- get-val [v]
  (condp = (type v)
    datascript.parser.PlainSymbol
    (:symbol v)
    datascript.parser.Variable
    (:symbol v)
    datascript.parser.Constant
    (:value v)
    datascript.parser.Placeholder
    '_))

(defn- is-var-required? [graph var]
  (if (or (some #(when (= :binding (graph/attr graph % :label)) %)
                (graph/in-edges graph var))
          (some #(when (= :pattern (graph/attr graph % :clause-type)) %)
                (into (graph/out-edges graph var)
                      (graph/in-edges graph var))))
    false
    (reduce
     (fn [res {:keys [dest] :as edge}]
       (case (graph/attr graph dest :type)
         :or-join (or (some
                       (fn [edge]
                         (when (true? (is-var-required? (:dest edge) var))
                           true))
                       (eduction
                        (filter (fn [e] (= :conj (graph/attr graph e :label))))
                        (graph/out-edges graph dest)))
                      false)
         :not-join (is-var-required? dest var)
         :rule (if (true? (graph/attr graph edge :required?)) true false)
         res))
     true
     (graph/out-edges graph var))))

(defn- mark-required-vars [graph node vars]
  (reduce
   (fn [g var]
     (let [edge (graph/find-edge g var node)]
       (if edge
        (graph/add-attr g edge :required? true)
        g)))
   graph
   (eduction
    (filter #(is-var-required? graph %))
    vars)))

(defn- process-fn-clause [{:keys [graph rule-defs]} clause fn-type counters]
  (let [fn-name (if (= fn-type :rule)
                  (-> clause :name get-val str)
                  (-> clause :fn :symbol str))
        id (get counters fn-name 0)
        fn-node (str fn-name "-" id)
        counters (update counters fn-name #(inc (or % 0)))]
    [(cond->
      (reduce
       (fn [g [idx arg]]
         (let [fn-sym (-> clause :fn :symbol)
               f-name (if (#{:fn :pred} fn-type)
                        #?(:clj (-> fn-sym resolve var-get)
                           :cljs (if-let [f (get d.fns/query-fns fn-sym)]
                                   f
                                   (throw (js/Error. (str "Could not find fn " fn-sym)))))
                        (-> clause :name get-val))
               arg-name (get-val arg)]
           (-> g
               (graph/add-directed-edges
                [arg-name fn-node (cond-> {:label [:arg idx]
                                           :clause-type (case fn-type
                                                          :pred :pred-arg
                                                          :fn :fn-arg
                                                          :rule :rule-arg)}
                                    (and (= :rule fn-type)
                                         (contains?
                                          (-> rule-defs f-name :required-vars)
                                          idx))
                                    (assoc :required? true))])
               (graph/add-attrs fn-node
                                {:fn f-name
                                 :type fn-type}))))
       graph
       (eduction (map-indexed vector) (:args clause)))
       (= fn-type :fn)
       (graph/add-directed-edges
        [fn-node (-> clause :binding :variable :symbol) {:label :binding}]))
     counters]))

(defn- process-where-clauses [{:keys [graph] :as ctx} clauses]
  (first (reduce
          (fn [[graph counters] clause]
            (let [ctx (assoc ctx :graph graph)]
             (condp = (type clause)
               datascript.parser.Pattern
               (let [src (-> clause :pattern first get-val)
                     dest (-> clause :pattern last get-val)
                     attr (-> clause :pattern second get-val)]
                 [(graph/add-directed-edges graph
                                           [src dest {:label attr
                                                      :clause-type :pattern}])
                  counters])
               datascript.parser.Predicate (process-fn-clause ctx clause :pred counters)
               datascript.parser.Function (process-fn-clause ctx clause :fn counters)
               datascript.parser.Or (process-or-join ctx clause counters)
               datascript.parser.Not (process-not-join ctx clause counters)
               datascript.parser.RuleExpr (process-fn-clause ctx clause :rule counters)
               [graph counters])))
          [graph {}]
          clauses)))

(defn- build-query-graph
  ([inputs where-clauses]
   (build-query-graph inputs where-clauses {}))
  ([inputs where-clauses rule-defs]
   (-> {:graph (reduce graph/add-nodes
                (graph/new-graph)
                inputs)
        :rule-defs rule-defs
        :inputs inputs}
       (process-where-clauses where-clauses))))

(defn analyze
  ([q]
   (analyze q []))
  ([q rules]
   (let [query (ds.p/parse-query q)
         rule-data (ds.p/parse-rules rules)
         rule-graphs (reduce
                      (fn [graphs rule]
                        (let [rule-name (get-val (:name rule))
                              branches
                              (reduce
                                (fn [branches branch]
                                  (let [inputs (into
                                                (mapv get-val
                                                      (-> branch :vars :required))
                                                (mapv get-val
                                                      (-> branch :vars :free)))
                                        graph (build-query-graph
                                               inputs (:clauses branch))
                                        required-vars (into []
                                                            (comp
                                                             (map-indexed vector)
                                                             (filter (fn [[_idx var]] (is-var-required? graph var)))
                                                             (map first))
                                                            inputs)
                                        recursive-nodes (filterv #(and (= :rule (graph/attr graph % :type))
                                                                       (= rule-name (graph/attr graph % :fn)))
                                                                 (graph/nodes graph))
                                        graph (reduce
                                               #(graph/add-attr %1 %2 :rule-feedback rule-name)
                                               graph
                                               recursive-nodes)
                                        recursive? (boolean (seq recursive-nodes))]
                                    (conj branches
                                          {:args inputs
                                           :required-args (set required-vars)
                                           :graph graph
                                           :recursive? recursive?})))
                               []
                               (:branches rule))
                              recursive? (reduce
                                          (fn [v {:keys [recursive?]}]
                                            (if (true? recursive?)
                                              (reduced true)
                                              v))
                                          false
                                          branches)]
                          (assoc graphs rule-name
                                 {:recursive? recursive?
                                  :branches branches
                                  :required-vars (reduce into #{} (eduction (map :required-args) branches))})))
                      {}
                      rule-data)
         inputs (let [vars (transient [])]
                  (walk/postwalk
                   #(condp = (type %)
                      datascript.parser.Variable (when-let [v (:symbol %)]
                                                   (conj! vars v))
                      nil)
                   (:qin query))
                  (persistent! vars))
         graph (build-query-graph inputs (:qwhere query) rule-graphs)
         projection (condp = (type (:qfind query))
                      datascript.parser.FindRel
                      (transduce
                       (map-indexed vector)
                       (completing
                        (fn [p [idx el]]
                          (if-let [s (:symbol el)]
                            (conj p {:type :rel :idx idx :symbol s})
                            p)))
                       []
                       (:elements (:qfind query)))
                      [])]
     {:inputs inputs
      :projections projection
      :rules rule-graphs
      :graph graph})))

 (defn- process-or-join [{:keys [graph rule-defs]} {:keys [rule-vars clauses]} counters]
  (let [vars (into #{} (map :symbol (:free rule-vars)))
        or-id (get counters :or 0)
        or-node (str "or-" or-id)
        graph (reduce
               #(graph/add-directed-edges %1 %2)
               (-> graph
                   (graph/add-nodes-with-attrs [or-node {:type :or-join}]))
               (eduction (map-indexed (fn [idx var]
                                        [var or-node {:label [:arg idx]}])) vars))
        counters (assoc counters :or (inc or-id))
        [graph counters]
        (reduce
         (fn [[graph counters] clause]
           (let [new-graph (condp = (type clause)
                             datascript.parser.And
                             (build-query-graph vars (:clauses clause) rule-defs)
                             (build-query-graph vars [clause] rule-defs))
                 conj-id (get counters :conj 0)]
             [(-> graph
                  (graph/add-nodes-with-attrs [new-graph {:op (str "conj-" conj-id)}])
                  (graph/add-directed-edges [or-node new-graph {:label :conj}]))
              (update counters :conj #(inc (or % 0)))]))
         [graph counters]
         clauses)]
    [(mark-required-vars graph or-node vars) counters]))

(defn- process-not-join [{:keys [graph rule-defs]} {:keys [vars clauses]} counters]
  (let [vars (into #{} (map :symbol vars))
        sub-graph (build-query-graph vars clauses rule-defs)
        not-id (get counters :not 0)]
    [(mark-required-vars
      (reduce
       #(graph/add-directed-edges %1 %2)
       (-> graph
           (graph/add-nodes-with-attrs [sub-graph {:op (str "not-" not-id) :type :not-join}]))
       (eduction
        (map-indexed (fn [idx var]
                       [var sub-graph {:label [:arg idx]}])) vars))
      sub-graph
      vars)
     (update counters :not #(inc (or % 0)))]))
