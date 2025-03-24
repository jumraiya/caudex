(ns caudex.utils
  (:require
   [ubergraph.core :as uber]
   [caudex.dbsp :as dbsp]
   [com.phronemophobic.clj-graphviz :refer [render-graph]]))


(defn op->edn [op]
  (when (satisfies? dbsp/Operator op)
    {:id (dbsp/-get-id op)
     :type (dbsp/-get-op-type op)
     :inputs (dbsp/-get-input-types op)
     :output (dbsp/-get-output-type op)}))

(defn is-op? [in]
  (satisfies? dbsp/Operator in))

(defn get-root-node [graph]
  (some
   #(when (= :root (dbsp/-get-op-type %))
      %)
   (uber/nodes graph)))

(defn graph->edn [graph]
  (let [edn (uber/ubergraph->edn graph)]
    (-> edn
        (update :nodes (fn [nodes]
                         (mapv (fn [[n attrs]]
                                 [(if (uber/ubergraph? n)
                                    (graph->edn n)
                                    (or (op->edn n) n))
                                  attrs])
                               nodes)))
        (update :directed-edges (fn [edges]
                                  (mapv
                                   (fn [[src dest attrs]]
                                     [(if (uber/ubergraph? src)
                                        (graph->edn src)
                                        (or (op->edn src) src))
                                      (if (uber/ubergraph? dest)
                                        (graph->edn dest)
                                        (or (op->edn dest) dest))
                                      attrs])
                                   edges))))))

(defn prn-graph [g]
  (letfn [(display [n]
            (if n
              (if-let [op (or (op->edn n)
                              (uber/attr g n :op))]
                (str op (uber/attr g n :pattern))
                (str n))
              "nil"))]
    (render-graph
     (assoc
      {:nodes (mapv display (uber/nodes g))
       :edges (into []
                    (map #(hash-map :from (display (:src %)) :to (display (:dest %))
                                    :label (str (get-in (:attrs g) [(:id %) :label]))))
                    (uber/edges g))}
      :flags #{:directed} :default-attributes {:edge {:label "label"}}))))
#trace
 (defn topsort
   [circuit & {:keys [start visited cycle-check-fn] :or {start (get-root-node circuit) visited #{}}}]
   (loop [queue [start] order [] visited visited]
     (let [[cur & queue] queue
           visited (conj visited cur)
           queue (into (vec queue)
                       (comp (map :dest)
                             (remove #(contains? visited %))
                             (filter #(every?
                                       (fn [in]
                                         (if cycle-check-fn
                                          (or (contains? visited (:src in))
                                              (cycle-check-fn (:src in)))
                                          (contains? visited (:src in))))
                                       (uber/in-edges circuit %))))
                       (uber/out-edges circuit cur))]
       (if (seq queue)
         (recur queue
                (conj order cur)
                visited)
         (conj order cur)))))

 (defn stratified-topsort
  [circuit & {:keys [start visited cycle-check-fn] :or {start (get-root-node circuit) visited #{}}}]
  (loop [queue [start] order [[start]] visited visited]
    (let [visited (into visited queue)
          queue (transduce
                 (comp
                  (map #(uber/out-edges circuit %))
                  cat
                  (map :dest)
                  (remove #(contains? visited %))
                  (filter #(every?
                            (fn [in]
                              (if cycle-check-fn
                                (or (contains? visited (:src in))
                                    (cycle-check-fn (:src in)))
                                (contains? visited (:src in))))
                            (uber/in-edges circuit %))))
                 (completing conj)
                 []
                 queue)
          order (if (seq queue)
                  (conj order queue)
                  order)]
      (if (seq queue)
        (recur queue
               order
               visited)
        order))))

(defn topsort-circuit [circuit & {:keys [stratify?] :as opts}]
  ((if stratify? stratified-topsort topsort)
   circuit
   (assoc opts :cycle-check-fn
          #(= :delay (-> % op->edn :type)))))

(defn topsort-query-graph [query-graph & {:keys [stratify?] :as opts}]
  (prn opts)
  ((if stratify? stratified-topsort topsort)
   query-graph
   (assoc opts :cycle-check-fn
          #(= :delay (-> % op->edn :type)))))
