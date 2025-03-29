(ns caudex.dbsp
  "Contains functions, protocols related to DBSP operators.
  Each Operator has input and output 'types' a sequence of values, 
  a type is some sequence of some symbols in a given query 
  e.g. join(input-1: [?a] input-2: [?b]) -> [?a ?b]
  Operators like Map or Join can contain conditions for filtering on joining dependent on above types in the form of [pred v-1 v-2 input-val ...].
  e.g. join(input-1: [?e :attr ?v] input-2: [?v :attr2 23]) -> [?e ?v ?x]
  where join conditions are [= {:input-idx 0 :val-idx 2} {:input-idx 1 :val-idx 0}]
  and [= {:input-idx 1 :val-idx 2} 23]"
  (:require [clojure.core.protocols :refer [Datafiable]]))

(defprotocol Operator
  (-get-id [this])
  (-get-op-type [this])
  (-get-input-types [this])
  (-get-output-type [this]))


(defn datafy-op [op]
  {:id (-get-id op)
   :type (-get-op-type op)
   :inputs (-get-input-types op)
   :output (-get-output-type op)})

;; Defines a zset "type", a concatenation of vars contained in zsets joined to create this one
(defprotocol ZSetType
  (-to-vector [this])
  (-get-joined-type [this new-type])
  (-get-join-constraints [this new-type]))

;; Some constraint b/w two zset types
(defprotocol Constraint
  (-get-pred [this])
  (-get-val-index-1 [this])
  (-get-val-index-2 [this])
  (-satisfies? [this val-1 val-2]))

;; Describes an value derived from an product type i.e. result of a join
(defrecord ValIndex [outer-idx inner-idx])

;; Assumes constraint is defined as [pred-fn val-index-1 val-index-2]
(extend-type clojure.lang.PersistentVector
  Constraint
  (-get-pred [this] (first this))
  (-get-val-index-1 [this] (second this))
  (-get-val-index-2 [this] (nth this 2))
  (-satisfies? [this val-1 val-2]
    ((-get-pred this)
     (get-in val-1 [(:outer-idx (-get-val-index-1 this)) (:inner-idx (-get-val-index-1 this))])
     (get-in val-2 [(:outer-idx (-get-val-index-2 this)) (:inner-idx (-get-val-index-2 this))]))))


(defn- find-constraints [zset-type-1 zset-type-2]
  (let [collect-pos #(transduce
                      (comp
                       (map-indexed vector)
                       (map (fn [[idx-1 data]]
                              (map-indexed
                               (fn [idx-2 el]
                                 (when (symbol? el)
                                   [el [idx-1 idx-2]]))
                               data)))
                       cat
                       (filter (fn [[el]]
                                 (symbol? el))))
                      (completing
                       (fn [indices [el idx]]
                         (update indices el conj idx)))
                      {}
                      %)
        indices-1 (collect-pos (-to-vector zset-type-1))
        indices-2 (collect-pos (-to-vector zset-type-2))]
    (reduce
     (fn [constraints [var indices]]
       (into constraints
             (for [idx-1 indices idx-2 (get indices-2 var)]
               [= (->ValIndex (first idx-1) (second idx-1))
                (->ValIndex (first idx-2) (second idx-2))])))
     []
     indices-1)))

(extend-type clojure.lang.PersistentVector
  ZSetType
  (-to-vector [this] this)
  (-get-joined-type [this new-type] (into this new-type))
  (-get-join-constraints [this new-type]
    (find-constraints this new-type)))

(defrecord RootOperator [id]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :root)
  (-get-input-types [_] [])
  (-get-output-type [_] []))

(defrecord FilterOperator [id input-type output-type filters projections]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :filter)
  (-get-input-types [_] (if (some? input-type) [input-type] []))
  (-get-output-type [_] output-type))

(defrecord MapOperator [id input-type output-type mapping-fn indices]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :map)
  (-get-input-types [_] (if (some? input-type) [input-type] []))
  (-get-output-type [_] output-type))

(defrecord NegOperator [id input-type]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :neg)
  (-get-input-types [_] [input-type])
  (-get-output-type [_] input-type))

(defrecord DelayOperator [id input-type]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :delay)
  (-get-input-types [_] [input-type])
  (-get-output-type [_] input-type))

(defrecord JoinOperator [id input-type-1 input-type-2 join-conds]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :join)
  (-get-input-types [_] [input-type-1 input-type-2])
  (-get-output-type [_] (-get-joined-type input-type-1 input-type-2)))

(defrecord AddOperator [id input-type]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :add)
  (-get-input-types [_] [input-type input-type])
  (-get-output-type [_] input-type))

(extend-protocol Datafiable
  RootOperator
  (datafy [this] (datafy-op this))
  FilterOperator
  (datafy [this] (datafy-op this))
  NegOperator
  (datafy [this] (datafy-op this))
  DelayOperator
  (datafy [this] (datafy-op this))
  JoinOperator
  (datafy [this] (datafy-op this))
  AddOperator
  (datafy [this] (datafy-op this)))
