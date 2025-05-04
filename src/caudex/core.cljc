(ns caudex.core
  (:require [caudex.circuit :as c]))

(defn -main []
  (let [q '[:find ?a ?b
            :where
            [?a :attr-1 12]
            [?b :attr-2 ?a]]
        circuit (c/build-circuit q)]
    (prn circuit)))

(println "asdasdas")
#_(let [q '[:find ?a ?b
          :where
          [?a :attr-1 12]
          [?b :attr-2 ?a]]
      circuit (c/build-circuit q)]
  (prn circuit))
