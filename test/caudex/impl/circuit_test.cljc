(ns caudex.impl.circuit-test
  (:require [clojure.test :refer [deftest is testing]]
            [caudex.circuit :as c]
            [caudex.impl.circuit :as impl]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]
            [caudex.utils :as utils]))




(deftest simple-join
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



(deftest test-preds
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

(deftest test-not-join
  (let [q '[:find ?a
            :where
            [?a :attr-1 ?b]
            (not-join [?b]
                      [?b :attr-2 10])]
        ccircuit (c/build-circuit q)
        _ (utils/prn-graph ccircuit)
        circuit (impl/reify-circuit ccircuit)
        tx-data [[1 :attr-1 2 123 true]
                 [2 :attr-2 12 123 true]
                 [3 :attr-1 11 123 true]
                 [11 :attr-2 10 123 true]]
        circuit (impl/step circuit tx-data :print? true)
        ;_ (impl/prn-circuit circuit)
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


(deftest test-reify+step-circuit
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

(deftest test-or-join2
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
         output))))

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
#trace
 (deftest test-or-join-3
   (let [q '[:find ?a ?b
             :where
             [?a :attr 10]
             (or-join [?a ?b]
                      (and
                       [?a :attr-2 :asd]
                       [(ground :branch-1) ?b])
                      (and
                       [?a :attr-2 :qwe]
                       [(ground :branch-2) ?b])
                      (and
                       (not-join [?a]
                                 [?a :attr-2 :asd])
                       [(ground :branch-3) ?b]))]
         ccircuit (c/build-circuit q)
         circuit (impl/reify-circuit ccircuit)
         circuit (impl/step circuit [[1 :attr 10 123 true]
                                     [1 :attr-2 :asd 123 true]])
         output (last (impl/get-output-stream circuit))
         circuit (impl/step circuit [[2 :attr 10 124 true]])
         output-2 (last (impl/get-output-stream circuit))]
     (is (match?
          {[1 :branch-1] true}
          output))
     (is (match?
          {[2 :branch-3] true}
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
                 [2 :location/description "loc-1"]
                 [4 :location/description "loc-2"]
                 [3 :object/description "object-1" 123 true]
                 [3 :object/detailed-description "desc-1" 123 true]
                 [3 :object/location 4 123 true]
                 [5 :object/description "object-2" 123 true]
                 [5 :object/detailed-description "desc-2" 123 true]
                 [5 :object/location 4 123 true]]
        ccircuit (c/build-circuit q)
                                        ;_  (caudex.utils/prn-graph ccircuit)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit tx-data)
        circuit (impl/step circuit [[1 :object/location 2 124 true]])
        circuit (impl/step
                 circuit
                 [[1 :object/location 4 125 true]
                  [1 :object/location 2 125 false]])
        output (impl/get-output-stream circuit)
        circuit (impl/step
                 circuit
                 [[1 :object/location 4 126 false]
                  [1 :object/location 2 126 true]])
        output-2 (impl/get-output-stream circuit)]
    (is (match?
         {["object-1" "desc-1"] true
          ["object-2" "desc-2"] true}
         (last output)))
    (is (match?
         {["object-1" "desc-1"] false
          ["object-2" "desc-2"] false}
         (last output-2)))))

(deftest test-not+or-join
  (let [q '[:find ?dest
            :where
            [?p :object/description "player"]
            [?p :object/location ?loc]
            [?action :action/type :move]
            [?action :action/arg ?wall]
            (or-join [?loc ?wall ?dest ?locked]
                     (and
                      [?exit :exit/location-1 ?loc]
                      [?exit :exit/location-1-wall ?wall]
                      [?exit :exit/location-2 ?dest]
                      [?exit :exit/locked? ?locked])
                     (and
                      [?exit :exit/location-2 ?loc]
                      [?exit :exit/location-2-wall ?wall]
                      [?exit :exit/location-1 ?dest]
                      [?exit :exit/locked? ?locked]))
            [(false? ?locked)]]
        ccircuit (c/build-circuit q)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step
                 circuit
                 [[1 :object/description "player" 123 true]
                  ["exit" :exit/location-1 "room-a" 123 true]
                  ["exit" :exit/location-1-wall :north 123 true]
                  ["exit" :exit/location-2 "room-b" 123 true]
                  ["exit" :exit/location-2-wall :south 123 true]
                  ["exit" :exit/locked? false 123 true]])
        circuit (impl/step circuit [[1 :object/location "room-a" 123 true]])
        circuit (impl/step
                 circuit
                 [["action" :action/type :move 124 true]
                  ["action" :action/arg :north 124 true]])
        output (impl/get-output-stream circuit)]
    ;; (utils/prn-graph ccircuit)
    ;; (impl/prn-circuit circuit)
    (prn output)))
