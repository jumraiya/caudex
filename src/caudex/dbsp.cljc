(ns caudex.dbsp
  "Contains functions, protocols related to DBSP operators.
  Each Operator has input and output 'types' a sequence of values, 
  a type is some sequence of some symbols in a given query 
  e.g. join(input-1: [?a] input-2: [?b]) -> [?a ?b]
  Operators like Map or Join can contain conditions for filtering on joining dependent on above types in the form of [pred v-1 v-2 input-val ...].
  e.g. join(input-1: [?e :attr ?v] input-2: [?v :attr2 23]) -> [?e ?v ?x]
  where join conditions are [= {:input-idx 0 :val-idx 2} {:input-idx 1 :val-idx 0}]
  and [= {:input-idx 1 :val-idx 2} 23]"
  (:require [clojure.core.protocols :refer [datafy Datafiable]]))

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

;; Some constraint b/w a sequence of datums which could be zset rows or constants
(defprotocol Constraint
  (-get-pred [this])
  (-get-args [this])
  (-satisfies? [this rows]))

;; Describes an value derived from an product type
(defrecord ValIndex [idx])

;; Assumes constraint is defined as [pred-fn val-index-1 val-index-2]
(extend-type #?(:clj clojure.lang.PersistentVector
                :cljs cljs.core/PersistentVector)
  Constraint
  (-get-pred [this] (first this))
  (-get-args [this] (subvec this 1))
  (-satisfies? [this row]
    (apply
     (-get-pred this)
     (mapv
      (fn [idx|const]
        (if (record? idx|const)
          (get row (:idx idx|const))
          idx|const))
      (-get-args this)))))

                       
(defn- find-constraints [zset-type-1 zset-type-2]
  (let [collect-pos #(transduce
                      (comp
                       (map-indexed vector)
                       (filter (fn [[_ el]] (symbol? el)))
                       (map (fn [[idx-1 el]]
                              [el (+ %2 idx-1)])))
                      (completing
                       (fn [indices [el idx]]
                         (update indices el conj idx)))
                      {}
                      %1)
        indices-1 (collect-pos (-to-vector zset-type-1) 0)
        indices-2 (collect-pos (-to-vector zset-type-2)
                               (count (-to-vector zset-type-1)))]
    (reduce
     (fn [constraints [var indices]]
       (into constraints
             (for [idx-1 indices idx-2 (get indices-2 var)]
               [= (->ValIndex idx-1)
                (->ValIndex idx-2)])))
     []
     indices-1)))

#_(defn- find-constraints [zset-type-1 zset-type-2]
    (let [collect-pos #(transduce
                        (comp
                         (filter symbol?)
                         (map-indexed vector)
                         (map (fn [[idx-1 el]]
                                [el (+ %2 idx-1)])))
                        (completing
                         (fn [indices [el idx]]
                           (update indices el conj idx)))
                        {}
                        %1)
          indices-1 (collect-pos (-to-vector zset-type-1) 0)
          indices-2 (collect-pos (-to-vector zset-type-2) (count (-to-vector zset-type-1)))]
      (reduce
       (fn [constraints [var indices]]
         (into constraints
               (for [idx-1 indices idx-2 (get indices-2 var)]
                 [= (->ValIndex idx-1)
                  (->ValIndex idx-2)])))
       []
       indices-1)))

(extend-type #?(:clj clojure.lang.PersistentVector
                :cljs cljs.core/PersistentVector)
  ZSetType
  (-to-vector [this] this)
  (-get-joined-type [this new-type]
    (into this new-type))
  (-get-join-constraints [this new-type]
    (find-constraints this new-type)))

;; All operators are either unary or binary and always have a single output
;; Although the output could be sent to multiple operators.

;; Entry point for transaction data into a circuit
;; The operator is expected to take tx-data and produce a zset from it.
(defrecord RootOperator [id]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :root)
  (-get-input-types [_] [])
  (-get-output-type [_] []))

;; Multi-use operator, could be used for datom ingress, projections or predicates
;; Takes zero or more filters in the form of [predicate arg+], where arg could be a value
;; or an index (as a ValIndex record) into the input zset row.
;; Takes optional sequence of projections in the form of ValIndexes
(defrecord FilterOperator [id input-type filters projections]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :filter)
  (-get-input-types [_] (if (some? input-type) [input-type] []))
  (-get-output-type [_]
    (if (empty? projections)
      input-type
      (mapv #(nth (-to-vector input-type) (:idx %)) projections))))

;; Used for transforming a zset entry into something else.
;; args are sequence of either values or ValIndexes
(defrecord MapOperator [id input-type output-type mapping-fn args]
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

(defrecord DelayFeedbackOperator [id input-type]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :delay-feedback)
  (-get-input-types [_] [input-type])
  (-get-output-type [_] input-type))

(defrecord IntegrationOperator [id input-type]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :integrate)
  (-get-input-types [_] [input-type])
  (-get-output-type [_] input-type))

;; Represents a cartesian product of two zset types. May be conditional or unconditional
(defrecord JoinOperator [id input-type-1 input-type-2 join-conds]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :join)
  (-get-input-types [_] [input-type-1 input-type-2])
  (-get-output-type [_] (-get-joined-type input-type-1 input-type-2)))

;; Similar to Join except each join condition's complement is used for joining
;; Also results in a join even if the negated input zset is empty
(defrecord AntiJoinOperator [id input-type]
  Operator
  (-get-id [_] id)
  (-get-op-type [_] :anti-join)
  (-get-input-types [_] [input-type])
  (-get-output-type [_] input-type))

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
  (datafy [this]
    (assoc (datafy-op this)
           :filters (mapv #(mapv (fn [v] (datafy v)) %) (:filters this))
           :projections (mapv datafy (:projections this))))
  MapOperator
  (datafy [this]
    (assoc (datafy-op this)
           :mapping-fn (:mapping-fn this)
           :args (mapv datafy (:args this))))
  NegOperator
  (datafy [this] (datafy-op this))
  DelayOperator
  (datafy [this] (datafy-op this))
  DelayFeedbackOperator
  (datafy [this] (datafy-op this))
  IntegrationOperator
  (datafy [this] (datafy-op this))
  JoinOperator
  (datafy [this] (datafy-op this))
  AddOperator
  (datafy [this] (datafy-op this))
  ValIndex
  (datafy [this] [:idx (:idx this)]))

(comment
  (let [arr [4 6 7 1 3]
        next-idx (fn [pred idx arr]
                   (loop [i idx]
                     (if (and (< i (count arr))
                              (pred (nth arr i)))
                       i
                       (when (< i (count arr))
                         (recur (inc i))))))
        next-odd (partial next-idx odd?)
        next-even (partial next-idx even?)]
    (loop [o-idx 0 e-idx 0 odd-used #{} even-used #{}]
      (when (and o-idx e-idx (not= o-idx e-idx))
        (prn (nth arr o-idx) (nth arr e-idx)))
      (when (and (< o-idx (count arr)) (< e-idx (count arr)))
        (let [odd-used (conj odd-used o-idx)
              even-used (conj even-used e-idx)]
          (cond
            (= o-idx e-idx) (recur (next-odd o-idx) e-idx odd-used even-used)
            (> o-idx e-idx) (cond
                              (> (- o-idx e-idx) 1)
                              (recur (next-odd o-idx) e-idx odd-used even-used))))))))
