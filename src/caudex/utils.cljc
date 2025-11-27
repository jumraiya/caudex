(ns caudex.utils
  (:require
   [caudex.graph :as graph]
   [caudex.dbsp :as dbsp]
   [clojure.string :as str]
   [caudex.graph :as g]
   [datascript.built-ins :as d.fns]
   [clojure.core.protocols :refer [datafy Datafiable]]
   #?(:clj [com.phronemophobic.clj-graphviz :refer [render-graph]])
   #?(:clj [clojure.data.json :as json])))

(defonce debug-data (atom nil))

(defn is-op? [in]
  (satisfies? dbsp/Operator in))

(defn- is-non-datom-clause? [graph node]
  (contains? #{:rule :or-join :not-join :fn :pred}
             (graph/attr graph node :type)))

(defn op->edn [op]
  (when (is-op? op)
    {:id (dbsp/-get-id op)
     :type (dbsp/-get-op-type op)
     :inputs (dbsp/-get-input-types op)
     #_(try
         (dbsp/-get-input-types op)
         (catch Exception ex
           "error"))
     :output (dbsp/-get-output-type op)
     #_(try
         (dbsp/-get-output-type op)
         (catch Exception ex
           "error"))}))


(defn get-root-node [graph]
  (or
   (some
    #(when (and (is-op? %)
                (= :root (dbsp/-get-op-type %)))
       %)
    (graph/nodes graph))
   (some
    #(when (= 0 (graph/in-degree graph %))
       %)
    (graph/nodes graph))))


(defn circuit->edn [gr]
  (let [to-edn #(if (graph/is-graph? %)
                  (circuit->edn %)
                  (if (satisfies? Datafiable %)
                    (datafy %)
                    %))]
   {:nodes (mapv (fn [n]
                   [(to-edn n)
                    (graph/attrs gr n)])
                 (graph/nodes gr))
    :directed-edges (mapv
                     (fn [{:keys [src dest] :as edge}]
                       (conj (mapv to-edn [src dest])
                             (graph/attrs gr edge)))
                     (graph/edges gr))}))

(defn- edn->op [edn]
  (let [resolve-arg #(if (and (vector? %) (= :idx (first %)))
                       (dbsp/->ValIndex (second %))
                       %)
        resolve-fn #?(:clj #(if-let [f (get d.fns/query-fns %)]
                              f
                              (-> % resolve var-get))
                      :cljs #(if-let [f (get d.fns/query-fns %)]
                               f
                               (throw (js/Error. (str "Could not find fn " %)))))
        resolve-constraint (fn [[pred & args]]
                             (into
                              [(resolve-fn pred)]
                              (mapv resolve-arg args)))]
    (if (and (map? edn) (:type edn))
      (case (:type edn)
        :root (dbsp/->RootOperator (:id edn))
        :filter (dbsp/->FilterOperator
                 (:id edn)
                 (first (:inputs edn))
                 (mapv resolve-constraint (:filters edn))
                 (mapv resolve-arg (:projections edn)))
        :map (dbsp/->MapOperator
              (:id edn)
              (-> edn :inputs first)
              (:output edn)
              (resolve-fn (:mapping-fn edn))
              (mapv resolve-arg (:args edn)))
        :neg (dbsp/->NegOperator (:id edn) (-> edn :inputs first))
        :delay (dbsp/->DelayOperator (:id edn) (-> edn :inputs first))
        :integrate (dbsp/->IntegrationOperator (:id edn) (-> edn :inputs first))
        :join (dbsp/->JoinOperator (:id edn) (-> edn :inputs first) (-> edn :inputs second) (mapv resolve-constraint (:join-conds edn)))
        :add (dbsp/->AddOperator (:id edn) (-> edn :inputs first)))
      edn)))

(defn edn->circuit [edn]
  (let [gr (graph/new-graph)]
    (reduce
     (fn [gr [src dest attrs]]
       (graph/add-directed-edges gr [(edn->op src) (edn->op dest) attrs]))
     (reduce
      (fn [gr [node attrs]]
        (graph/add-nodes-with-attrs gr [(edn->op node) attrs]))
      gr
      (:nodes edn))
     (:directed-edges edn))))

(defn- display-node [g n]
  (if n
    (if-let [op (or (op->edn n)
                    (graph/attr g n :op))]
      (str op (graph/attr g n :pattern))
      (str (if (is-op? n)
             (dbsp/-get-id n)
             n)))
    "nil"))

 (defn circuit->map [circuit]
  (let [ccircuit (if (and (map? circuit) (contains? circuit :circuit))
                   (:circuit circuit)
                   circuit)
        id #(str (if (is-op? %) (dbsp/-get-id %) %))
        label #(str (if (is-op? %) (str (dbsp/-get-id %)
                                        ;; (dbsp/-get-input-types %)
                                        " "
                                        (dbsp/-get-output-type %))
                        %))
        nodes (mapv #(hash-map "id" (id %)
                               #_(first (get ids (:id %)))
                               "label" (label %)
                               #_(display-node g (second (get ids (:id %)))))
                    (graph/nodes ccircuit))
        edges (mapv #(hash-map "from" (-> % :src id)
                               #_(first (get ids (-> % :src :id)))
                               "to" (-> % :dest id)
                               #_(first (get ids (->  % :dest :id))))
                    (graph/edges ccircuit))
        tx-data->zset #(into {}
                             (map (fn [[e a v _tx add?]]
                                    [[e a v] add?]))
                             %)
        data     (cond->
                  {:nodes nodes :edges edges}
                   (contains? circuit :streams)
                   (assoc :streams (update (:streams circuit) -1
                                           #(mapv (fn [c] (tx-data->zset c)) %))
                          :op-stream-map (:op-stream-map circuit)))]
    (reset! debug-data data)
    #?(:clj (spit "circuit_data.json" (json/write-str data))
       :cljs
       (let [json-str (js/JSON.stringify (clj->js data) nil 2)
             blob (js/Blob. #js [json-str] #js {:type "application/json"})
             url (js/URL.createObjectURL blob)
             link (.createElement js/document "a")]
         (set! (.-href link) url)
         (set! (.-download link) "circuit_data.json")
         (.click link)
         (js/URL.revokeObjectURL url)))
    data))



(defn prn-graph
  ([g]
   (prn-graph g "graph.png"))
  ([g filename]
   (let [;; {:keys [nodes edges] :as circuit-map}
         ;; (circuit->map g)
         ]
     #?(:clj
        (render-graph
         (assoc
          {:nodes (mapv #(display-node g %) (graph/nodes g))
           :edges (into []
                        (map #(hash-map :from (display-node g (:src %))
                                        :to (display-node g  (:dest %))
                                        :label (str (get-in (:attrs g) [(:id %) :label]))))
                        (graph/edges g))}
          :flags #{:directed} :default-attributes {:edge {:label "label"}} :layout-algorithm :neato)
         {:filename filename})))))

#trace
(defn topsort
  [circuit & {:keys [start visited visited-check-fn]
              :or {start (get-root-node circuit) visited #{}}}]
  (let [queue (into [start]
                    (if (seq visited)
                      visited
                      (filterv #(and
                                 (not= start %)
                                 (= 0 (graph/in-degree circuit %)))
                               (graph/nodes circuit))))]
    (loop [queue queue order [] visited visited]
      (let [[cur & queue] queue
            visited (conj visited cur)
            queue (into (vec queue)
                        (comp (map :dest)
                              (remove #(contains? visited %))
                              (remove #(contains? (set queue) %))
                              (filter #(every?
                                        (fn [in]
                                          (or (contains? visited (:src in))
                                              (and (fn? visited-check-fn)
                                                   (visited-check-fn (:src in) %))))
                                        (graph/in-edges circuit %))))
                        (graph/out-edges circuit cur))]
        (if (seq queue)
          (recur queue
                 (conj order cur)
                 visited)
          (conj order cur))))))


(defn stratified-topsort
  "Performs a stratified topological sort on a directed acyclic graph.
   
   Returns a sequence of strata, where each stratum is a collection of nodes
   that can be processed in parallel (no dependencies between them within the stratum).
   
   Options:
   - :start-nodes - Collection of nodes to start from (defaults to all root nodes)
   - :visited-check-fn - Function (dep-node current-node) -> boolean to determine
                        if a dependency should be ignored for ordering purposes"
  [g & {:keys [start-nodes visited-check-fn visited]
        :or {start-nodes [(get-root-node g)] visited #{}}}]
  (let [start-nodes (if (sequential? start-nodes) start-nodes [start-nodes])]
    (loop [queue (vec start-nodes)
           strata []
           visited visited]
      (if (empty? queue)
        strata
        (let [;; Add current stratum to result
              strata (conj strata queue)
              ;; Add current stratum to visited set
              visited (into visited queue)

              ;; Find next nodes whose dependencies are all satisfied
              next-candidates (transduce
                               (comp
                                (mapcat #(graph/out-edges g %))
                                (map :dest)
                                (remove #(contains? visited %))
                                (distinct))
                               conj
                               []
                               queue)
              next-queue (filter
                          (fn [node]
                            (every?
                             (fn [in-edge]
                               (let [dep-node (:src in-edge)]
                                 (or
                                  ;; Dependency is already processed
                                  (contains? visited dep-node)
                                  ;; Custom check allows ignoring this dependency
                                  (and visited-check-fn
                                       (visited-check-fn dep-node node)))))
                             (graph/in-edges g node)))
                          next-candidates)]

          (recur (vec next-queue)
                 strata
                 visited))))))


(defn get-stratified-hierarchy
  [circuit start]
  (loop [queue [start] order [[start]] visited #{}]
    (let [visited (into visited queue)
          queue (transduce
                 (comp
                  (map #(graph/in-edges circuit %))
                  cat
                  (map :src)
                  (remove #(contains? visited %))
                  (remove #(contains? (set queue) %))
                  (filter #(every?
                            (fn [in]
                              (or (contains? visited (:dest in))
                                  (and (#{:delay :delay-feedback}
                                        (-> (:dest in) op->edn :type))
                                       (some? (graph/find-edge circuit % (:dest in))))))
                            (graph/out-edges circuit %))))
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
   (assoc opts :visited-check-fn
          (fn [dep node]
            ;; Special handling for delay feedback loop
            ;; The delay should not count as a hard dependency
            (and (#{:delay :delay-feedback} (-> dep op->edn :type))
                 (some? (graph/find-edge circuit node dep)))))))

 #_(defn topsort-query-graph [query-graph & {:keys [stratify?] :as opts}]
     (let [nodes-with-no-unsatisifed-deps
           (filterv
            (fn [node]
              (or (and (not (symbol? node))
                       (not (is-non-datom-clause? query-graph node)))
                  (and (symbol? node)
                       (not (some #(when (true? (graph/attr query-graph % :required?))
                                     true)
                                  (graph/out-edges query-graph node))))
                  (and (is-non-datom-clause? query-graph node)
                       (every? #(not (true? (graph/attr query-graph % :required?)))
                               (graph/in-edges query-graph node)))))
            (graph/nodes query-graph))
        ;; opts (if (seq nodes-with-no-unsatisifed-deps)
        ;;        (assoc opts :start (first nodes-with-no-unsatisifed-deps)
        ;;               :visited (-> nodes-with-no-unsatisifed-deps rest set))
        ;;        opts)
           ]
       ((if stratify? stratified-topsort topsort)
        query-graph
        (assoc opts :visited-check-fn
               (fn [dep node]
                 (if (contains? #{:rule :or-join :not-join}
                                (graph/attr query-graph node :type))
                   (not (and (graph/attr
                              query-graph (graph/find-edge query-graph dep node) :required?)
                             (symbol? dep)))
                   (not (symbol? dep))))))))
#trace
(defn topsort-query-graph [query-graph]
  (let [dep-graph (reduce
                   (fn [gr {:keys [src dest] :as edge}]
                     (let [{:keys [label required?]} (g/attrs query-graph edge)]
                       (if (and (is-non-datom-clause? query-graph dest)
                                (= :arg (first label))
                                (not (true? required?)))
                         (g/add-directed-edges gr [dest src])
                         (g/add-directed-edges gr [src dest]))))
                   (g/new-graph)
                   (g/edges query-graph))
        nodes (topsort dep-graph)]
    (when (not (seq nodes))
      #?(:clj (throw (Exception. "Empty query graph"))
         :cljs (throw (js/Error. "Empty query graph"))))
    nodes))

(defn datafy-circuit [circuit]
  (mapv #(mapv datafy %)
        (topsort-circuit circuit :stratify? true)))

 (defn remap-nodes
   ([g rename-map]
    (remap-nodes g rename-map (keys rename-map)))
   ([g rename-map nodes]
    (reduce
     (fn [g node]
       (let [next-nodes (into []
                              (comp
                               (map :dest)
                               (filter #(contains? #{:or-join :not-join} (graph/attr g % :type)))
                               (map #(if (graph/is-graph? %)
                                       [%]
                                       (mapv :dest
                                             (filterv (fn [edge]
                                                        (= :conj (graph/attr g edge :label)))
                                                      (graph/out-edges g %)))))
                               cat)
                              (graph/out-edges g node))
             replacement (if (graph/is-graph? node)
                           (remap-nodes node rename-map)
                           (get rename-map node))
             g (graph/replace-node g node replacement)]
         (if (seq next-nodes)
           (remap-nodes g rename-map next-nodes)
           g)))
     g
     nodes))) 

#_(defn get-heirarchy [circuit op-id]
    (let [           ;strata (topsort-circuit circuit :stratify? true)
          parents (loop [parents (mapv
                                  :src
                                  (graph/in-edges
                                   circuit
                                   (some #(when (= op-id (dbsp/-get-id %))
                                            %)
                                         (graph/nodes circuit))))
                         t 0]
                    (let [parents (into parents queue)]
                      (prn (mapv #(dbsp/-get-id %) parents))
                      (if-let [new-edges (and
                                          (< t 5)
                                          (seq (into []
                                                     (comp
                                                      (map #(graph/in-edges circuit %))
                                                      cat
                                                      (remove #(= :delay-feedback
                                                                  (dbsp/-get-op-type (:src %)))))
                                                     queue)))]
                        (recur parents new-edges (inc t))
                        parents)))]
      parents))

(comment
  (doseq [view ["player-location"
                "move-action"
                "inspect-action"
                "pickup-action"
                "bowl-on-table"
                "open-safe"
                "set-safe-combination"
                "accessible-objects"
                "accessible-exits"
                "put-action"
                "open-action"]]
    (let [edn (slurp (str "/Users/jumraiya/projects/escape-room/public/views/" view ".edn"))]
      (edn->circuit edn))))
