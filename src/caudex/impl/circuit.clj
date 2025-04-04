(ns caudex.impl.circuit
  "Simple implementation of circuit reification for testing purposes.
  ZSets are represented as maps e.g. {[[12 \"some-val\" :ad] [23]] true}. Values are booleans instead of numbers true -> 1, false -> -1"
  (:require [caudex.utils :as utils]
            [ubergraph.core :as uber]
            [caudex.dbsp :as dbsp]))

(defn- tx-data->zset [txs]
  (into {}
        (map (fn [[e a v tx add?]]
               [[e a v tx] add?]))
        txs))

(defn- is-idx? [v]
  (= caudex.dbsp.ValIndex (type v)))

#trace
 (defn reify-circuit
   "Constructs a map representing a circuit along with it's step order"
   [circuit]
   (let [order (utils/topsort-circuit circuit)
         root (some #(when (= :root (dbsp/-get-op-type %)) %) (uber/nodes circuit))
         last-op (last order)]
     (reduce
      (fn [g [idx {:keys [src dest] :as e}]]
        (let [arg-idx (uber/attr circuit e :arg)]
          (-> g
              (assoc-in [:streams idx] [])
              (update :op-stream-map
                      (fn [m]
                        (-> m
                            (update-in [(dbsp/-get-id src) :outputs] #(conj (or % []) idx))
                            (update-in [(dbsp/-get-id dest) :inputs]
                                       #(assoc (or % (sorted-map)) arg-idx idx))))))))
      {:t 0
       :streams {-1 [] -2 []}
       :op-stream-map {(dbsp/-get-id root) {:inputs (sorted-map 0 -1) :outputs []}
                       (dbsp/-get-id last-op) {:outputs [-2]}}
       :order order}
      (eduction
       (map-indexed vector)
       (uber/edges circuit)))))

#trace
 (defn- step-op [op zsets]
   (case (dbsp/-get-op-type op)
     :root (tx-data->zset (first zsets))
     :filter (into {}
                   (comp
                    (filter (fn [[row]]
                              (every?
                               #(dbsp/-satisfies? % row)
                               (:filters op))))
                    (map (fn [[k v]]
                           (if (seq (:projections op))
                             [(mapv #(nth k (:idx %)) (:projections op))
                              v]
                             [k v]))))
                   (first zsets))
     :map (into {}
                (map (fn [[row add?]]
                       (let [args (into []
                                        (map #(if (is-idx? %)
                                                (nth row (:idx %))
                                                %))
                                        (:args op))
                             res (apply (:mapping-fn op) args)]
                         [(conj row [res]) add?])))
                (first zsets))
     :neg (update-vals not (first zsets))
     :delay (first zsets)
     :join (into {}
                 (for [row-1 (first zsets) row-2 (second zsets)
                       :when (or (empty? (:join-conds op))
                                 (every?
                                  #(dbsp/-satisfies? % (into (key row-1) (key row-2)))
                                  (:join-conds op)))]
                   [(into (key row-1) (key row-2)) (and (val row-1) (val row-2))]))
     :add (reduce
           (fn [set-1 row]
             (if (contains? set-1 (key row))
               (if (not= (get set-1 row) (val row))
                 (dissoc set-1 (key row))
                 set-1)
               (conj set-1 row)))
           (first zsets)
           (second zsets))))

#trace
 (defn step
   "Steps through a reified circuit with transaction data, updating stream values and returning a updated circuit"
   [data tx-data]
   (let [data (update-in data [:streams -1] #(conj % tx-data))]
     (reduce
      (fn [{:keys [streams op-stream-map] :as data} op]
        (let [{:keys [inputs outputs]} (get op-stream-map (dbsp/-get-id op))
              input-vals (mapv #(last (get streams %)) (vals inputs))
              new-val (step-op op input-vals)]
          (update data :streams
                  (fn [s]
                    (reduce
                     #(update %1 %2 conj new-val)
                     s
                     outputs)))))
      (update data :t inc)
      (:order data))))

(defn get-output-stream [circuit]
  (get-in circuit [:streams -2]))

(defn prn-circuit [circuit]
  (doseq [t (range (:t circuit))]
    (prn "t: " t)
    (doseq [op (:order circuit)]
      (prn "op: " (dbsp/-get-id op)
           " inputs: " (mapv #(nth (get-in circuit [:streams %]) t)
                             (vals (get-in circuit [:op-stream-map (dbsp/-get-id op) :inputs])))
           " outputs: " (when-let [idx (first (get-in circuit [:op-stream-map (dbsp/-get-id op) :outputs]))]
                          (nth (get-in circuit [:streams idx]) t))))))

;(prn-circuit user/c)

