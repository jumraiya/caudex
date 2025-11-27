(ns caudex.impl.circuit-test
  (:require [clojure.test :refer [deftest is]]
            [caudex.circuit :as c]
            [caudex.impl.circuit :as impl]
            [caudex.utils :as utils]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]))


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
        circuit (impl/reify-circuit ccircuit)
        tx-data [[1 :attr-1 2 123 true]
                 [2 :attr-2 12 123 true]
                 [3 :attr-1 11 123 true]
                 [11 :attr-2 10 123 true]]
        circuit (impl/step circuit tx-data)
        ;_ (impl/prn-circuit circuit)
        output (impl/get-output-stream circuit)]
    (is (match?
         (m/equals
          [{[1] true}])
         output))))

(deftest test-not-join-2
  (let [q '[:find ?a
            :where
            [?a :attr-2 10]
            (or-join [?a]
                     [(= ?a :b)]
                     (not-join [?a]
                               [_ :attr ?a]))]
        ccircuit (c/build-circuit q)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit
                           [[:a :attr-2 10 123 true]
                            [:b :attr-2 10 123 true]
                            [:c :attr :b 123 true]])
        output (impl/get-output-stream circuit)]
    (is (= {[:a] true, [:b] true}
           (last output)))))


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


(deftest test-or-join-4
  (let [q '[:find ?dest ?locked
            :where
            [?p :object/location ?loc]
            [?p :last-action/arg ?wall]
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
                      [?exit :exit/locked? ?locked])
                     (and
                      (not-join [?loc ?wall]
                                (or-join [?loc ?wall]
                                 (and
                                  [?e :exit/location-1 ?loc]
                                  [?e :exit/location-1-wall ?wall])
                                 (and
                                  [?e :exit/location-2 ?loc]
                                  [?e :exit/location-2-wall ?wall])))
                      [(ground :not-found) ?dest]
                      [(ground false) ?locked]))]
        ccircuit (c/build-circuit q)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit
                           [[:exit :exit/location-1 :loc 123 true]
                            [:exit :exit/location-1-wall :east 123 true]
                            [:exit :exit/location-2 :loc-2 123 true]
                            [:exit :exit/location-2-wall :west 123 true]
                            [:exit :exit/locked? false 123 true]])
        circuit (impl/step circuit
                           [[:player :object/location :loc 123 true]
                            [:player :last-action/arg :north 123 true]])
        output (last (impl/get-output-stream circuit))]
    (is (match? {[:not-found false] true} output))))

(deftest test-or-join-5
  (let [q '[:find ?a ?arg ?o ?det
            :where
            [?a :action/arg ?arg]
            [?a :action/type ?action-type]
            [?a :action/type :inspect]
            (not-join [?a]
                      [?a :action/inspect-processed? true])
            (or-join [?o ?arg ?det]
                     (and
                      [(not= ?arg "player")]
                      [?o :object/description ?arg]
                      [?o :object/detailed-description ?det]
                      [?p :object/description "player"]
                      [?p :object/location ?l]
                      (or-join [?l ?p ?o]
                               [?o :object/location ?p]
                               [?o :object/location ?l]))
                     (and
                      (or-join [?arg]
                               [(= ?arg "player")]
                               (not-join [?arg]
                                         [_ :object/description ?arg])
                               (and
                                [?o :object/description ?arg]
                                [(not= ?arg "player")]
                                (not-join [?o]
                                          [?p :object/description "player"]
                                          [?p :object/location ?l]
                                          (or-join [?l ?p ?o]
                                                   [?o :object/location ?p]
                                                   [?o :object/location ?l]))))
                      [(ground :object-not-found) ?o]
                      [(ground :no-description) ?det]))]
        ccircuit (c/build-circuit q)
        ;; _ (caudex.utils/prn-graph ccircuit)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit
                           [[:obj :object/description "desc" 123 true]
                            [:obj :object/detailed-description "detailed desc" 123 true]
                            [:obj :object/location :loc 123 true]
                            [:player :object/description "player" 123 true]])
        circuit (impl/step circuit
                           [[:player :object/location :loc 123 true]])
        circuit (impl/step circuit
                           [[:action-1 :action/type :move 124 true]
                            [:action-1 :action/arg :south 124 true]])
        circuit (impl/step circuit
                           [[:action-2 :action/type :inspect 124 true]
                            [:action-2 :action/arg "desc" 124 true]])
        output (last (impl/get-output-stream circuit))
        circuit (impl/step circuit
                           [[:action-2 :action/inspect-processed? true 124 true]])
        circuit (impl/step circuit
                           [[:player :object/location :loc 123 false]
                            [:player :object/location :loc-2 123 true]])
        circuit (impl/step circuit
                           [[:action-3 :action/type :inspect 124 true]
                            [:action-3 :action/arg "desc" 124 true]]
                           ;; :print? true
                           )
        output-2 (last (impl/get-output-stream circuit))]
    (is (match?
         {[:action-2 "desc" :obj "detailed desc"] true}
         output))

    (is (match?
           {[:action-3 "desc" :object-not-found :no-description] true}
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
                  ["action" :action/arg :north 124 true]])]
    (is (= {["room-b"] true}
           (last (impl/get-output-stream circuit))))))

(deftest test-rules
  (let [tx-data [[1 :attr :a 123 true]
                 [2 :attr :a 123 true]
                 [3 :attr :a 123 true]
                 [3 :attr-2 10 123 true]]
        q '[:find ?a
            :in $ %
            :where
            [?a :attr :a]
            (rule ?a)]
        rules '[[(rule ?b)
                 [(= ?b 1)]]
                [(rule ?b)
                 [?b :attr-2 10]]]
        ccircuit (c/build-circuit q rules)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit tx-data)
        output (last (impl/get-output-stream circuit))
        ccircuit (c/build-circuit q '[[(rule ?b)
                                       (not-join [?b]
                                        [(= ?b 1)])]])
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit tx-data)
        output' (last (impl/get-output-stream circuit))
        rules '[[(rule ?x)
                 (not-join [?x]
                           [?x :attr-2 10])]]
        ccircuit (c/build-circuit q rules)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit tx-data)
        output-2 (last (impl/get-output-stream circuit))]
    (is (match?
         {[1] true, [3] true}
         output))
    (is (match?
         {[2] true, [3] true}
         output'))
    (is (= {[1] true [2] true}
         output-2))))


(deftest test-rules-free-vars
  (let [q '[:find ?c ?a
            :in $ %
            :where
            (rule ?a :const)
            [?c :attr ?a]]
        rules '[[(rule ?c ?v)
                 [?c :attr-2 ?v]]]
        ccircuit (c/build-circuit q rules)
        circuit (impl/reify-circuit ccircuit)
        tx-data [[1 :attr 2 123 true]
                 [2 :attr-2 :const 123 true]
                 [3 :attr 4 123 true]]
        circuit (impl/step circuit tx-data)
        output (last (impl/get-output-stream circuit))

            ;; (rule ?a :const)
            ;; [?c :attr ?a]
        rules '[[(rule ?c ?v)
                 [?c :attr-2 10]
                 (or-join [?v]
                          [(= ?v :const)]
                          [(= ?v :val2)])]]
        ccircuit (c/build-circuit q rules)
        circuit (impl/reify-circuit ccircuit)
        tx-data [[1 :attr 2 123 true]
                 [2 :attr-2 10 123 true] ;;matches
                 ;; no match
                 [4 :attr 3 123 true]]
        circuit (impl/step circuit tx-data)
        output-2 (last (impl/get-output-stream circuit))]
    (is (= {[1 2] true} output))
    (is (= {[1 2] true} output-2))))


(deftest test-rule-dependency
  (let [rules '[[(rule-1 ?a ?b)
                 [?a :ref ?b]
                 [?a :attr 10]]
                [(rule-2 ?a)
                 (not-join [?a]
                           [?a :attr-2 12])]]
        q '[:find ?a
            :in $ %
            :where
            (rule-2 ?a)
            (rule-1 ?a :b)]
        tx-data [[:a :ref :b 123 true]
                 [:a :attr 10 123 true]]
        ccircuit (c/build-circuit q rules)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit tx-data)
        output (last (impl/get-output-stream circuit))]
    (is (= {[:a] true} output))))

                                        ;(clojure.test/run-test test-rules-free-vars)
                                        ;(clojure.test/run-test test-nested-rules)
(deftest test-nested-rules
  (let [q '[:find ?a ?b
            :in $ %
            :where
            [?a :attr 12]
            (rule ?a ?b)]
        rules '[[(rule ?p ?q)
                 [?p :attr-2 :a]
                 [?q :attr-3 ?p]
                 (nested-rule ?q)]
                [(nested-rule ?r)
                 [(= ?r 10)]]]
        tx-data [[1 :attr 12 123 true]
                 [1 :attr-2 :a 123 true]
                 [10 :attr-3 1 123 true]
                 [2 :attr 12 123 true]
                 [2 :attr-2 :a 123 true]
                 [11 :attr-3 2 123 true]]
        ccircuit (c/build-circuit q rules)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit tx-data)
        output (last (impl/get-output-stream circuit))]
    (is (match? {[1 10] true} output))))

(deftest test-disjoint-not-join
  (let [q '[:find ?o ?accessible
            :where
            [?o :object/desc ?d]
            (not-join [?o]
                      [?o :object/desc "player"])
            (or-join [?o ?accessible]
                     (and
                      [?p :object/loc ?l]
                      [?p :object/desc "player"]
                      (or-join [?l ?p ?o]
                               [?o :object/loc ?p]
                               [?o :object/loc ?l])
                      [(ground :accessible) ?accessible])
                     (and
                      (not-join [?o]
                                [?p :object/loc ?l]
                                [?p :object/desc "player"]
                                (or-join [?l ?p ?o]
                                         [?o :object/loc ?p]
                                         [?o :object/loc ?l]))
                      [(ground :not-accessible) ?accessible]))]
        ccircuit (c/build-circuit q)
                                        ;_ (caudex.utils/prn-graph ccircuit)
        circuit (impl/reify-circuit ccircuit)
        circuit (impl/step circuit
                           [[:obj :object/desc "desc" 123 true]
                            [:obj :object/loc :loc 123 true]
                            [:player :object/desc "player" 123 true]
                            [:player :object/loc :loc-2 123 true]] 
                                        ;:print? true
                           )
                                        ;not-accessible
        output (last (impl/get-output-stream circuit))
        circuit (impl/step circuit
                           [[:player :object/loc :loc 123 true]
                            [:player :object/loc :loc-2 123 false]]
                           ;; :print? true
                           )
                                        ;accessible
        output-2 (last (impl/get-output-stream circuit))]
    (is (match? {[:obj :not-accessible] true} output))
    (is (match? {[:obj :accessible] true, [:obj :not-accessible] false} output-2))))
