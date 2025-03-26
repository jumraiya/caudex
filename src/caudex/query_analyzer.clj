(ns caudex.query-analyzer
  "Functions for processing a query and generating a graph from it"
  (:require [datascript.parser :as ds.p]
            [ubergraph.core :as uber]
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
    (:value v)))

(defn- is-var-required? [graph var]
  (if (or (some #(when (= :binding (uber/attr graph % :label)) %)
                (uber/in-edges graph var))
          (some #(when (= :pattern (uber/attr graph % :clause-type)) %)
                (uber/out-edges graph var)))
    false
    (reduce
     (fn [res {:keys [dest]}]
       (case (uber/attr graph dest :type)
         :or-join (reduce
                   (fn [res edge]
                     (if (false? (is-var-required? (:dest edge) var))
                       (reduced false)
                       res))
                   true
                   (eduction
                    (filter (fn [e] (= :conj (uber/attr graph e :label))))
                    (uber/out-edges graph dest)))
         :not-join (is-var-required? dest var)
         res))
     true
     (uber/out-edges graph var))))

(defn- mark-required-vars [graph node vars]
  (reduce
   (fn [g var]
     (let [edge (uber/find-edge g var node)]
       (if edge
        (uber/add-attr g edge :required? true)
        g)))
   graph
   (eduction
    (filter #(is-var-required? graph %))
    vars)))

(defn- process-fn-clause [graph clause fn-type counters]
  (let [fn-name (if (= fn-type :rule)
                  (-> clause :name get-val str)
                  (-> clause :fn :symbol str))
        id (get counters fn-name 0)
        fn-node (str fn-name "-" id)
        counters (update counters fn-name #(inc (or % 0)))]
    [(cond->
         (reduce
          (fn [g [idx arg]]
            (let [f-name (if (#{:fn :pred} fn-type)
                           (-> clause :fn :symbol resolve var-get)
                           (-> clause :name get-val))]
              (-> g
                  (uber/add-directed-edges
                   [(get-val arg) fn-node {:label [:arg idx]
                                           :clause-type (case fn-type
                                                          :pred :pred-arg
                                                          :fn :fn-arg
                                                          :rule :rule-arg)}])
                  (uber/add-attrs fn-node
                                  {:fn f-name
                                   :type fn-type}))))
          graph
          (eduction (map-indexed vector) (:args clause)))
         (= fn-type :fn)
         (uber/add-directed-edges
          [fn-node (-> clause :binding :variable :symbol) {:label :binding}]))
     counters]))

(defn- process-where-clauses [graph clauses]
  (first (reduce
          (fn [[graph counters] clause]
            (condp = (type clause)
              datascript.parser.Pattern
              (let [src (-> clause :pattern first get-val)
                    dest (-> clause :pattern last get-val)
                    attr (-> clause :pattern second get-val)]
                [(uber/add-directed-edges graph
                                          [src dest {:label attr
                                                     :clause-type :pattern}])
                 counters])
              datascript.parser.Predicate (process-fn-clause graph clause :pred counters)
              datascript.parser.Function (process-fn-clause graph clause :fn counters)
              datascript.parser.Or (process-or-join graph clause counters)
              datascript.parser.Not (process-not-join graph clause counters)
              datascript.parser.RuleExpr (process-fn-clause graph clause :rule counters)
              [graph counters]))
          [graph {}]
          clauses)))

(defn- build-query-graph [inputs where-clauses]
  (-> (reduce uber/add-nodes
              (uber/ubergraph false false)
              inputs)
      (process-where-clauses where-clauses)))

 (defn analyze
  ([q]
   (analyze q []))
  ([q rules]
   (let [rule-data (ds.p/parse-rules rules)
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
                                       recursive-nodes (filterv #(and (= :rule (uber/attr graph % :type))
                                                                      (= rule-name (uber/attr graph % :fn)))
                                                                (uber/nodes graph))
                                       graph (reduce
                                              #(uber/add-attr %1 %2 :rule-feedback rule-name)
                                              graph
                                              recursive-nodes)
                                       recursive? (boolean (seq recursive-nodes))]
                                   (conj branches
                                         {:args inputs
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
                                 {:recursive? recursive? :branches branches})))
                      {}
                      rule-data)
         query (ds.p/parse-query q)
         inputs (let [vars (transient #{})]
                  (walk/postwalk
                   #(condp = (type %)
                      datascript.parser.Variable (when-let [v (:symbol %)]
                                                   (conj! vars v))
                      nil)
                   (:qin query))
                  (persistent! vars))
         graph (build-query-graph inputs (:qwhere query))
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

 (defn- process-or-join [graph {:keys [rule-vars clauses]} counters]
  (let [vars (into #{} (map :symbol (:free rule-vars)))
        or-id (get counters :or 0)
        or-node (str "or-" or-id)
        graph (reduce
               #(uber/add-directed-edges %1 %2)
               (-> graph
                   (uber/add-nodes-with-attrs [or-node {:type :or-join}]))
               (eduction (map-indexed (fn [idx var]
                                        [var or-node {:label [:arg idx]}])) vars))
        counters (assoc counters :or (inc or-id))
        [graph counters]
        (reduce
         (fn [[graph counters] clause]
           (let [new-graph (condp = (type clause)
                             datascript.parser.And
                             (build-query-graph vars (:clauses clause))
                             (build-query-graph vars [clause]))
                 conj-id (get counters :conj 0)]
             [(-> graph
                  (uber/add-nodes-with-attrs [new-graph {:op (str "conj-" conj-id)}])
                  (uber/add-directed-edges [or-node new-graph {:label :conj}]))
              (update counters :conj #(inc (or % 0)))]))
         [graph counters]
         clauses)]
    [(mark-required-vars graph or-node vars) counters]))

(defn- process-not-join [graph {:keys [vars clauses]} counters]
  (let [vars (into #{} (map :symbol vars))
        sub-graph (build-query-graph vars clauses)
        not-id (get counters :not 0)]
    [(mark-required-vars
      (reduce
       #(uber/add-directed-edges %1 %2)
       (-> graph
           (uber/add-nodes-with-attrs [sub-graph {:op (str "not-" not-id) :type :not-join}]))
       (eduction
        (map-indexed (fn [idx var]
                       [var sub-graph {:label [:arg idx]}])) vars))
      sub-graph
      vars)
     (update counters :not #(inc (or % 0)))]))
