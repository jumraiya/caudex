(ns caudex.utils
  (:require
   [caudex.graph :as graph]
   [caudex.dbsp :as dbsp]
   [clojure.core.protocols :refer [datafy]]
   ;[com.phronemophobic.clj-graphviz :refer [render-graph]]
   ))


(defn is-op? [in]
  (satisfies? dbsp/Operator in))


(defn op->edn [op]
  (when (is-op? op)
    {:id (dbsp/-get-id op)
     :type (dbsp/-get-op-type op)
     :inputs (dbsp/-get-input-types op)
     :output (dbsp/-get-output-type op)}))


(defn get-root-node [graph]
  (some
   #(when (or (and (is-op? %)
                   (= :root (dbsp/-get-op-type %)))
              (= 0 (graph/in-degree graph %)))
      %)
   (graph/nodes graph)))

#_(defn graph->edn [graph]
  (let [edn (graph/ubergraph->edn graph)]
    (-> edn
        (update :nodes (fn [nodes]
                         (mapv (fn [[n attrs]]
                                 [(if (graph/ubergraph? n)
                                    (graph->edn n)
                                    (or (op->edn n) n))
                                  attrs])
                               nodes)))
        (update :directed-edges (fn [edges]
                                  (mapv
                                   (fn [[src dest attrs]]
                                     [(if (graph/ubergraph? src)
                                        (graph->edn src)
                                        (or (op->edn src) src))
                                      (if (graph/ubergraph? dest)
                                        (graph->edn dest)
                                        (or (op->edn dest) dest))
                                      attrs])
                                   edges))))))

#_(defn prn-graph [g]
  (letfn [(display [n]
            (if n
              (if-let [op (or (op->edn n)
                              (graph/attr g n :op))]
                (str op (graph/attr g n :pattern))
                (str n))
              "nil"))]
    (render-graph
     (assoc
      {:nodes (mapv display (graph/nodes g))
       :edges (into []
                    (map #(hash-map :from (display (:src %)) :to (display (:dest %))
                                    :label (str (get-in (:attrs g) [(:id %) :label]))))
                    (graph/edges g))}
      :flags #{:directed} :default-attributes {:edge {:label "label"}}))))

(defn topsort
  [circuit & {:keys [start visited visited-check-fn]
              :or {start (get-root-node circuit) visited #{}}}]
  (let [queue (into [start]
                    (filter #(and
                              (not= start %)
                              (= 0 (graph/in-degree circuit %))))
                    (graph/nodes circuit))]
    (loop [queue queue order [] visited visited]
      (let [[cur & queue] queue
            visited (conj visited cur)
            queue (into (vec queue)
                        (comp (map :dest)
                              (remove #(contains? visited %))
                              (remove #(contains? (set queue) %))
                              (filter #(every?
                                        (fn [in]
                                          (if visited-check-fn
                                            (or (contains? visited (:src in))
                                                (visited-check-fn (:src in) %))
                                            (contains? visited (:src in))))
                                        (graph/in-edges circuit %))))
                        (graph/out-edges circuit cur))]
        (if (seq queue)
          (recur queue
                 (conj order cur)
                 visited)
          (conj order cur))))))

(defn stratified-topsort
  [circuit & {:keys [start visited visited-check-fn] :or {start (get-root-node circuit) visited #{}}}]
  (let [queue (into [start]
                    (filter #(and
                              (not= start %)
                              (= 0 (graph/in-degree circuit %))))
                    (graph/nodes circuit))]
   (loop [queue queue order [[start]] visited visited]
     (let [visited (into visited queue)
           queue (transduce
                  (comp
                   (map #(graph/out-edges circuit %))
                   cat
                   (map :dest)
                   (remove #(contains? visited %))
                   (remove #(contains? (set queue) %))
                   (filter #(every?
                             (fn [in]
                               (if visited-check-fn
                                 (or (contains? visited (:src in))
                                     (visited-check-fn (:src in) %))
                                 (contains? visited (:src in))))
                             (graph/in-edges circuit %))))
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
         order)))))


(defn topsort-circuit [circuit & {:keys [stratify?] :as opts}]
  ((if stratify? stratified-topsort topsort)
   circuit
   (assoc opts :visited-check-fn
          (fn [dep _node]
            (= :delay (-> dep op->edn :type))))))

(defn topsort-query-graph [query-graph & {:keys [stratify?] :as opts}]
  ((if stratify? stratified-topsort topsort)
   query-graph
   (assoc opts :visited-check-fn
          (fn [dep node]
            (if (contains? #{:rule :or-join :not-join}
                           (graph/attr query-graph node :type))
              (not (graph/attr query-graph
                              (graph/find-edge query-graph dep node)
                              :required?))
              (not (symbol? dep)))))))
