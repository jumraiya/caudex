(ns caudex.graph
  "Facade namespace for Ubergraph and Loom. Only Loom supports cljs so that's what used for browser target."
  (:require
   [loom.graph :as loom]
   [loom.attr :as l.attr]
   [loom.alg :as l.alg]))

(defn- nodes-eq? [a b]
  (if (and (record? a) (record? b)
           (contains? a :id) (contains? b :id))
    (= (:id a) (:id b))
    (= a b)))

(defn new-graph []
  (loom/digraph))

(defn attr [graph node|edge attr-name]
  (l.attr/attr graph node|edge attr-name))

(defn attrs [graph node|edge]
  (if (and (map? node|edge) (contains? node|edge :src))
    (l.attr/attrs graph (:src node|edge) (:dest node|edge))
    (l.attr/attrs graph node|edge)))

(defn nodes [graph]
  (loom/nodes graph))

(defn edges [graph]
  (mapv #(hash-map :src (first %) :dest (second %)) (loom/edges graph)))

(defn in-edges [graph node]
  (into []
        (comp
         (filter (fn [[_ dest]]
                   (nodes-eq? dest node)))
         (map (fn [[src dest]]
                (hash-map :src src :dest dest))))
        (loom/edges graph)))

(defn in-degree [graph node]
  (count (in-edges graph node)))


(defn out-edges [graph node]
  (into []
        (comp
         (filter (fn [[src _dest]]
                   (nodes-eq? src node)))
         (map (fn [[src dest]]
                (hash-map :src src :dest dest))))
        (loom/edges graph)))

(defn out-degree [graph node]
  (count (out-edges graph node)))


(defn find-edge [graph node-1 node-2]
  (some #(when (and (nodes-eq? node-1 (first %))
                    (nodes-eq? node-2 (second %)))
           {:src node-1 :dest node-2})
        (loom/edges graph)))

(defn add-attr [graph node|edge attr value]
  (if (and (map? node|edge) (contains? node|edge :src))
    (apply l.attr/add-attr
           (conj [graph] (:src node|edge) (:dest node|edge) attr value))
    (l.attr/add-attr graph node|edge attr value)))

(defn add-attrs [graph node|edge attrs]
  (reduce
   (fn [g [attr value]]
     (if (and (map? node|edge) (contains? node|edge :src))
       (apply l.attr/add-attr
              (conj [g] (:src node|edge) (:dest node|edge) attr value))
       (l.attr/add-attr g node|edge attr value)))
   graph
   attrs))

(defn add-directed-edges [graph [src dest & [attrs]]]
  (let [g (loom/add-edges graph [src dest])]
    (if (map? attrs)
      (add-attrs g {:src src :dest dest} attrs)
      g)))

(defn topsort [graph]
  (l.alg/topsort graph))

;; For some reason loaded loom function does not work correctly
(defn- remove-nodes-cljs [graph nodes]
   (let [remove-adj-nodes (fn [m nodes adjacents remove-fn]
                            (reduce
                             (fn [m n]
                               (if (m n)
                                 (update-in m [n] #(apply remove-fn % nodes))
                                 m))
                             (apply dissoc m nodes)
                             adjacents))
         remove-nodes (fn [g nodes]
                        (let [ins (mapcat #(loom/predecessors g %) nodes)
                              outs (mapcat #(loom/successors g %) nodes)]
                          (-> g
                              (update-in [:nodeset] #(apply disj % nodes))
                              (assoc :adj (remove-adj-nodes (:adj g) nodes ins disj))
                              (assoc :in (remove-adj-nodes (:in g) nodes outs disj)))))]
     (remove-nodes graph nodes)))

(defn remove-nodes [graph & nodes]
  (let [g (if (seq nodes)
            (remove-nodes-cljs graph nodes)
            graph)]
            g))

(defn add-nodes [graph & nodes]
  (apply loom/add-nodes (into [graph] nodes)))


(defn add-nodes-with-attrs [graph & nodes]
  (reduce
   (fn [g [n attrs]]
     (-> g
         (add-nodes n)
         (add-attrs n attrs)))
   graph
   nodes))


(defn connected-components [graph]
  (l.alg/connected-components graph))

(defn loners [graph]
  (l.alg/loners graph))

(defn is-graph? [obj]
  (loom/graph? obj))

(defn graph->edn [g]
  {:nodes (vec (for [node (nodes g)] [node (attrs g node)]))
   :directed-edges (mapv (fn [{:keys [src dest] :as edge}]
                           (vector src dest (attrs g edge)))
                         (edges g))})
(defn terminal-nodes [g]
  (filterv #(= 0 (out-degree g %)) (nodes g)))


 (defn replace-node [g node replacement]
   (reduce
    (fn [g edge]
      ;; TODO move this out of graph ns somehow
      (if (= node (:label (attrs g edge)))
        (add-attr g edge :label replacement)
        g))
    (if (true?
         (some #(when (= % node) true) (nodes g)))
      (let [i-edges (in-edges g node)
            o-edges (out-edges g node)]
        (reduce
         #(add-directed-edges %1 [replacement (:dest %2) (attrs g %2)])
         (reduce
          #(add-directed-edges %1 [(:src %2) replacement (attrs g %2)])
          (cond-> (add-nodes-with-attrs g [replacement (attrs g node)])
            (not= node replacement) (remove-nodes node))
          i-edges)
         o-edges))
      g)
    (edges g)))

