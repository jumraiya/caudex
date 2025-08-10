(ns caudex.impl.circuit
  "Simple implementation of circuit reification for testing purposes.
  ZSets are represented as maps e.g. {[[12 \"some-val\" :ad] [23]] true}. Values are booleans instead of numbers true -> 1, false -> -1"
  (:require [caudex.utils :as utils]
            [caudex.graph :as graph]
            [caudex.dbsp :as dbsp]))

(defn- tx-data->zset [txs]
  (into {}
        (map (fn [[e a v _tx add?]]
               [[e a v] add?]))
        txs))

(defn- is-idx? [v]
  (= caudex.dbsp.ValIndex (type v)))

(defn reify-circuit
  "Constructs a map representing a circuit along with it's step order"
  [circuit]
  (let [order (utils/topsort-circuit circuit)
        root (some #(when (= :root (dbsp/-get-op-type %)) %) (graph/nodes circuit))
        last-op (last order)]
    (reduce
     (fn [g [idx {:keys [src dest] :as e}]]
       (let [arg-idx (graph/attr circuit e :arg)]
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
      (graph/edges circuit)))))

(defn- add-zsets [zset-1 zset-2]
  (reduce
   (fn [set-1 row]
     (if (contains? set-1 (key row))
       (if (not= (get set-1 (key row)) (val row))
         (dissoc set-1 (key row))
         set-1)
       (conj set-1 row)))
   zset-1
   zset-2))
#trace
(defn- exec-filter-op [zsets op]
  (into {}
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
        (first zsets)))

(defn- step-op [op streams print?]
  (let [zsets (mapv last streams)
        res (case (dbsp/-get-op-type op)
              :root (tx-data->zset (first zsets))
              :filter (exec-filter-op zsets op)
              :map (into {}
                         (map (fn [[row add?]]
                                (let [args (into []
                                                 (map #(if (is-idx? %)
                                                         (nth row (:idx %))
                                                         %))
                                                 (:args op))
                                      indices-used? (some #(when (is-idx? %) %) (:args op))
                                      res (apply (:mapping-fn op) args)]
                                  [(if indices-used?
                                     (conj row res)
                                     ;; If no indices were used, simply return the result
                                     [res])
                                   add?])))
                         (first zsets))
              :neg (update-vals (first zsets) not)
              :delay (or (-> streams first butlast last) {})
              :delay-feedback (first zsets)
              :integrate (add-zsets (first zsets) (or (second zsets) {}))
              :join (into {}
                          (for [row-1 (first zsets) row-2 (second zsets)
                                :when (or (empty? (:join-conds op))
                                          (every?
                                           #(dbsp/-satisfies? % (into (key row-1) (key row-2)))
                                           (:join-conds op)))]
                            [(into (key row-1) (key row-2)) (and (val row-1) (val row-2))]))
              :anti-join (first zsets)
              #_(into {}
                      (filter (fn [row-1]
                                (every?
                                 (fn [row-2]
                                   (not-every?
                                    #(dbsp/-satisfies?
                                      %
                                      (into (key row-1) (key row-2)))
                                    (:join-conds op)))
                                 (second zsets))))
                      (first zsets))
              :add (add-zsets (first zsets) (second zsets)))]
    (when print?
      (prn (str "(" (:id op) " " (clojure.string/join " " (mapv #(with-out-str (clojure.pprint/pprint %)) zsets)) ") -> " res)))
    res))

(defn step
  "Steps through a reified circuit with transaction data, updating stream values and returning a updated circuit"
  [data tx-data & {:keys [print?] :or {print? false}}]
  (let [data (update-in data [:streams -1] #(conj % tx-data))]
    (reduce
     (fn [{:keys [streams op-stream-map] :as data} op]
       (let [{:keys [inputs outputs]} (get op-stream-map (dbsp/-get-id op))
             input-streams (mapv #(get streams %) (vals inputs))
             input-streams (if (= (dbsp/-get-op-type op) :integrate)
                             (conj input-streams
                                   (get streams (first outputs)))
                             input-streams)
             new-val (step-op op input-streams print?)]
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

(defn get-last-output [circuit]
  (last (get-output-stream circuit)))

(defn prn-circuit [{:keys [op-stream-map streams] :as circuit}]
  (doseq [t (range (:t circuit))]
    (prn "t: " t)
    (doseq [op (:order circuit)]
      (let [{:keys [inputs outputs]} (get op-stream-map (dbsp/-get-id op))
            input-vals (mapv #(nth (get streams %) t) (vals inputs))]
        (prn "op: " (dbsp/-get-id op)
             " inputs: " input-vals
             " outputs: " (when-let [idx (first outputs)]
                            (nth (get streams idx) t)))))))

;(prn-circuit user/c)

