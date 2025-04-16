(ns caudex.impl.circuit-test
  (:require [clojure.test :refer [deftest is testing]]
            [caudex.circuit :as c]
            [caudex.impl.circuit :as impl]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]))


(deftest test-reify+step-circuit
  (testing "Simple Join"
      (let [q '[:find ?a ?b
                :where
                [?a :attr-1 12]
                [?b :attr-2 ?a]]
            circuit (impl/reify-circuit (c/build-circuit q))
            tx-data [[1 :attr-1 12 123 true]
                     [2 :attr-2 1 123 true]
                     [3 :attr-1 10 123 true]
                     [4 :attr-2 3 123 true]]
            circuit (impl/step circuit tx-data)
            output (impl/get-output-stream circuit)]
        (is (match?
             [{[1 2] true}]
             output))))
  (testing "Simple Join with inputs"
      (let [q '[:find ?a ?b
                :in ?in ?in2
                :where
                [?a :attr-1 ?in]
                [?b :attr-2 ?a]
                [?b :attr-3 ?in2]]
            circuit (impl/reify-circuit (c/build-circuit q))
            tx-data [[1 :attr-1 12 123 true]
                     [2 :attr-2 1 123 true]
                     [2 :attr-3 "test" 123 true]
                     [3 :attr-1 10 123 true]
                     [4 :attr-2 3 123 true]
                     [:caudex.circuit/input '?in 12 123 true]
                     [:caudex.circuit/input '?in2 "test" 123 true]]
            circuit (impl/step circuit tx-data)
            output (impl/get-output-stream circuit)]
        (is (match?
             [{[1 2] true}]
             output))))
  (testing "Predicates and functions"
      (let [q '[:find ?a ?c
                :where
                [?a :attr-1 ?b]
                [(> ?b 4)]
                [(* ?b 100) ?c]]
            circuit (impl/reify-circuit (c/build-circuit q))
            tx-data [[1 :attr-1 2 123 true]
                     [3 :attr-1 10 123 true]]
            circuit (impl/step circuit tx-data)
            output (impl/get-output-stream circuit)]
        (is (match?
             [{[3 1000] true}]
             output))))
  (testing "Not joins"
    (let [q '[:find ?a
                :where
                [?a :attr-1 ?b]
                (not-join [?b]
                          [?b :attr-2 10])]
            ccircuit (c/build-circuit q)
            circuit (impl/reify-circuit ccircuit)
            tx-data [[1 :attr-1 2 123 true]
                     [2 :attr-2 12 123 true]
                     [3 :attr-1 11 123 true]
                     [11 :attr-2 10 123 true]]
            circuit (impl/step circuit tx-data)
            output (impl/get-output-stream circuit)]
        (is (match?
             (m/equals
              [{[1] true}])
             output)))
    #_(let [q '[:find ?b
              :in $ ?in
              :where
              (not-join [?b ?in]
                        [?b :attr-2 ?in])]
          ccircuit (c/build-circuit q)
          circuit (impl/reify-circuit ccircuit)
          tx-data [[2 :attr-2 12 123 true]
                   [11 :attr-2 10 123 true]
                   [:caudex.circuit/input '?in 10 123 true]]
          circuit (impl/step circuit tx-data)
          output (impl/get-output-stream circuit)]
      (prn output)
      (caudex.utils/prn-graph ccircuit)
      (impl/prn-circuit circuit)
      (is (match?
           [{[2] true [11] false}]
           output))))
  (testing "Or joins"
    (let [q '[:find ?a
              :where
              [?a :attr-1 ?b]
              (or-join [?a ?b]
                       [(> ?b 100)]
                       [?a :attr-2 "test"])]
          ccircuit (c/build-circuit q)
          circuit (impl/reify-circuit ccircuit)
          tx-data [[1 :attr-1 12 123 true]
                   [1 :attr-2 "test" 123 true]
                   [2 :attr-1 102 123 true]
                   [3 :attr-1 78 123 true]
                   [3 :attr-2 "asd" 123 true]]
          circuit (impl/step circuit tx-data)
          output (impl/get-output-stream circuit)]
      (is (match?
           [{[1] true [2] true}]
           output)))))
