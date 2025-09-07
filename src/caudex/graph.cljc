(ns caudex.graph
  "Facade namespace for Ubergraph and Loom. Only Loom supports cljs so that's what used for browser target."
  (:require
   #?@(:clj [[ubergraph.core :as uber]
             [ubergraph.alg :as alg]]
       :cljs [[loom.graph :as loom]
              [loom.attr :as l.attr]
              [loom.alg :as l.alg]])))

(defn new-graph []
  #?(:clj (uber/ubergraph false false)
     :cljs (loom/digraph)))

(defn attr [graph node|edge attr-name]
  #?(:clj (uber/attr graph node|edge attr-name)
     :cljs (l.attr/attr graph node|edge attr-name)))

(defn attrs [graph node|edge]
  #?(:clj (uber/attrs graph node|edge)
     :cljs (if (and (map? node|edge) (contains? node|edge :src))
             (l.attr/attrs graph (:src node|edge) (:dest node|edge))
             (l.attr/attrs graph node|edge))))

(defn nodes [graph]
  #?(:clj (uber/nodes graph)
     :cljs (loom/nodes graph)))

(defn edges [graph]
  #?(:clj (uber/edges graph)
     :cljs (mapv #(hash-map :src (first %) :dest (second %)) (loom/edges graph))))

(defn in-edges [graph node]
  #?(:clj (uber/in-edges graph node)
     :cljs (into []
                 (comp
                  (filter (fn [[_ dest]]
                            (= dest node)))
                  (map (fn [[src dest]]
                            (hash-map :src src :dest dest))))
                 (loom/edges graph))))

(defn in-degree [graph node]
  #?(:clj (uber/in-degree graph node)
     :cljs (count (in-edges graph node))))


(defn out-edges [graph node]
  #?(:clj (uber/out-edges graph node)
     :cljs (mapv (fn [[src dest]]
                   (hash-map :src src :dest dest))
                 (loom/out-edges graph node))))

(defn out-degree [graph node]
  #?(:clj (uber/out-degree graph node)
     :cljs (count (out-edges graph node))))


(defn find-edge [graph node-1 node-2]
  #?(:clj (uber/find-edge graph node-1 node-2)
     :cljs (some #(when (and (= node-1 (first %))
                             (= node-2 (second %)))
                    {:src node-1 :dest node-2})
                 (loom/edges graph))))

(defn add-attr [graph node|edge attr value]
  #?(:clj (uber/add-attr graph node|edge attr value)
     :cljs (if (and (map? node|edge) (contains? node|edge :src))
             (apply l.attr/add-attr
                    (conj [graph] (:src node|edge) (:dest node|edge) attr value))
             (l.attr/add-attr graph node|edge attr value))))

(defn add-attrs [graph node|edge attrs]
  #?(:clj (uber/add-attrs graph node|edge attrs)
     :cljs (reduce
            (fn [g [attr value]]
              (if (and (map? node|edge) (contains? node|edge :src))
                (apply l.attr/add-attr
                       (conj [g] (:src node|edge) (:dest node|edge) attr value))
                (l.attr/add-attr g node|edge attr value)))
            graph
            attrs)))

(defn add-directed-edges [graph [src dest & [attrs]]]
  #?(:clj (uber/add-directed-edges graph (cond-> [src dest] (map? attrs) (conj attrs)))
     :cljs (let [g (loom/add-edges graph [src dest])]
             (if (map? attrs)
               (add-attrs g {:src src :dest dest} attrs)
               g))))

(defn remove-nodes [graph & nodes]
  #?(:clj (apply uber/remove-nodes (into [graph] nodes))
     :cljs (apply loom/remove-nodes (into [graph] nodes))))

(defn add-nodes [graph & nodes]
  #?(:clj (apply uber/add-nodes (into [graph] nodes))
     :cljs (apply loom/add-nodes (into [graph] nodes))))


(defn add-nodes-with-attrs [graph & nodes]
  #?(:clj (apply uber/add-nodes-with-attrs (into [graph] nodes))
     :cljs (reduce
            (fn [g [n attrs]]
              (-> g
                  (add-nodes n)
                  (add-attrs n attrs)))
            graph
            nodes)))


(defn connected-components [graph]
  #?(:clj (alg/connected-components graph)
     :cljs (l.alg/connected-components graph)))

(defn loners [graph]
  #?(:clj (alg/loners graph)
     :cljs (l.alg/loners graph)))

(defn is-graph? [obj]
  #?(:clj (uber/ubergraph? obj)
     :cljs (loom/graph? obj)))

(defn graph->edn [g]
  #?(:clj (uber/ubergraph->edn g)
     :cljs {:nodes (vec (for [node (nodes g)] [node (attrs g node)]))
            :directed-edges (mapv (fn [{:keys [src dest] :as edge}]
                                    (vector src dest (attrs g edge)))
                                  (edges g))}))
(defn terminal-nodes [g]
  (filterv #(= 0 (out-degree g %)) (nodes g)))
