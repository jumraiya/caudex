(ns caudex.impl.circuit-test
  (:require [clojure.test :refer [deftest is testing]]
            [caudex.circuit :as c]
            [caudex.impl.circuit :as impl]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]))


(deftest test-reify+step-circuit
  (let [q '[:find ?a ?b
            :where
            [?a :attr-1 12]
            [?b :attr-2 ?a]]
        circuit (impl/reify-circuit (c/build-circuit q))
        tx-data [[1 :attr-1 12 123 true]
                 [2 :attr-2 1 123 true]]
        circuit (impl/step circuit tx-data)
        output (impl/get-output-stream circuit)]
    (is (match?
         [{[1 2] true}]
         output))))
