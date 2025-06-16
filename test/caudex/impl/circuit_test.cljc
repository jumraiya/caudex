(ns caudex.impl.circuit-test
  (:require [clojure.test :refer [deftest is testing]]
            [caudex.circuit :as c]
            [caudex.impl.circuit :as impl]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]
            [caudex.utils :as utils]))


(deftest test-reify+step-circuit
  (testing "Simple Join"
    (let [q '[:find ?a ?b
              :where
              [?a :attr-1 ?b]
              [?b :attr-2 12]]
          circuit (impl/reify-circuit (c/build-circuit q))
          tx-data [[1 :attr-1 2 123 true]
                   [2 :attr-2 12 123 true]
                   [3 :attr-1 4 123 true]
                   [4 :attr-2 10 123 true]]
          circuit (impl/step circuit tx-data)
          output-1 (last (impl/get-output-stream circuit))
          circuit (impl/step circuit [[2 :attr-2 12 124 false]
                                      [2 :attr-2 13 124 false]
                                      [4 :attr-2 12 124 true]])
          output-2 (last (impl/get-output-stream circuit))]
      (is (match?
           {[1 2] true}
           output-1))
      (is (match?
           {[1 2] false
            [3 4] true}
           output-2))))

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
          c (c/build-circuit q)
          circuit (impl/reify-circuit c)
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

 (deftest test-or-join
   (let [q '[:find ?p ?wall ?dest
             :where
             [?p :object/description "player"]
             [?p :object/location ?loc]
             (or-join [?loc ?wall ?dest]
                      (and
                       [?exit :exit/location-1 ?loc]
                       [?exit :exit/location-1-wall ?wall]
                       [?exit :exit/location-2 ?dest])
                      (and
                       [?exit :exit/location-2 ?loc]
                       [?exit :exit/location-2-wall ?wall]
                       [?exit :exit/location-1 ?dest]))]
         ccircuit (c/build-circuit q)
         circuit (impl/reify-circuit ccircuit)
         tx-data [[1 :object/description "player" 123 true]
                  [1 :object/location "room-a" 123 true]
                  ["exit" :exit/location-1 "room-a" 123 true]
                  ["exit" :exit/location-1-wall :north 123 true]
                  ["exit" :exit/location-2 "room-b" 123 true]
                  ["exit" :exit/location-2-wall :south 123 true]]
         circuit (impl/step circuit tx-data)
         output (impl/get-output-stream circuit)
         tx-data [[1 :object/location "room-b" 124 true]
                  [1 :object/location "room-a" 124 false]]
         circuit (impl/step circuit tx-data)
         output-2 (last (impl/get-output-stream circuit))]
     (is (match?
          [{[1 :north "room-b"] true}]
          output))
     (is (match?
          {[1 :north "room-b"] false
           [1 :south "room-a"] true}
          output-2))))

(deftest test-refs
  (let [q '[:find ?d ?det
            :where
            [?p :object/description "player"]
            [?p :object/location ?l]
            [?o :object/description ?d]
            [?o :object/detailed-description ?det]
            (or-join [?l ?p ?o]
                     [?o :object/location ?p]
                     [?o :object/location ?l])]
        tx-data [[1 :object/description "player" 123 true]
                 [1 :object/location 2 123 true]
                 [3 :object/description "object" 123 true]
                 [3 :object/detailed-description "detailed description" 123 true]
                 [3 :object/location 1 123 true]]
        ccircuit (c/build-circuit q)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit tx-data)
        output (impl/get-output-stream circuit)]
    (is (match?
         [{["object" "detailed description"] true}]
         output))))
