(ns caudex.circuit-test
  (:require [clojure.test :refer [deftest is testing]]
            [caudex.circuit :as c]
            [caudex.utils :as utils]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]
            [clojure.core.protocols :refer [datafy]]))


 (deftest test-build-circuit
  (testing "Only pattern clauses"
      (let [q '[:find ?a ?b
                :where
                [?a :attr-1 12]
                [?b :attr-2 ?a]]
            circuit (c/build-circuit q)
            sorted-ops (mapv #(mapv datafy %)
                             (utils/topsort-circuit circuit :stratify? true))]
        (is (match?
             [[{:type :root}]
              (m/in-any-order
               [{:type :filter :output '[?b ?a]}
                {:type :filter :output '[?a]}])
              (m/in-any-order
               [{:type :add :inputs '[[?b ?a] [?b ?a]] :output '[?b ?a]}
                {:type :add :inputs '[[?a] [?a]] :output '[?a]}
                {:type :join :inputs '[[?a] [?b ?a]] :output '[?a ?b ?a]}])
              (m/in-any-order
               [{:type :delay :inputs '[[?b ?a]] :output '[?b ?a]}
                {:type :delay :inputs '[[?b ?a]] :output '[?b ?a]}
                {:type :delay :inputs '[[?a]] :output '[?a]}
                {:type :join :inputs '[[?a] [?b ?a]] :output '[?a ?b ?a]}])
              [{:type :add :inputs '[[?a ?b ?a] [?a ?b ?a]]
                :output '[?a ?b ?a]}]
              [{:type :filter,
                :inputs '[[?a ?b ?a]]
                :output '[?a ?b]}]]
             sorted-ops))))
  (testing "Pattern and pred clauses"
      (let [q '[:find ?a ?c
                :in $ % ?in
                :where
                [?a :attr-1 ?in]
                [?in :attr-2 ?b]
                [(+ ?b 10) ?c]
                [(> ?c 23)]]
            circuit (c/build-circuit q)
            sorted-ops (mapv #(mapv datafy %)
                             (utils/topsort-circuit circuit :stratify? true))]
        (is (match?
             [[{:type :root :inputs [] :output []}]
              [{:type :filter
                :inputs '[[:caudex.circuit/input ?in ?in]]
                :output '[?in]
                :filters
                [[= :caudex.circuit/input [:idx 0]]
                 [= '?in [:idx 1]]]
                :projections [[:idx 2]]}
               {:type :filter
                :inputs '[[?a :attr-1 ?in]]
                :output '[?a ?in]
                :filters [[= [:idx 1] :attr-1]]
                :projections [[:idx 0] [:idx 2]]}
               {:type :filter
                :inputs '[[?in :attr-2 ?b]]
                :output '[?in ?b]
                :filters [[= [:idx 1] :attr-2]]
                :projections [[:idx 0] [:idx 2]]}]
              [{:type :add :inputs '[[?in] [?in]] :output '[?in]}
               {:type :add
                :inputs '[[?a ?in] [?a ?in]]
                :output '[?a ?in]}
               {:type :join
                :inputs '[[?a ?in] [?in]]
                :output '[?a ?in ?in]}
               {:type :add
                :inputs '[[?a ?in] [?a ?in]]
                :output '[?a ?in]}
               {:type :add
                :inputs '[[?in ?b] [?in ?b]]
                :output '[?in ?b]}
               {:type :join
                :inputs '[[?in ?b] [?a ?in]]
                :output '[?in ?b ?a ?in]}]
              [{:type :delay :inputs '[[?in]] :output '[?in]}
               {:type :delay :inputs '[[?in]] :output '[?in]}
               {:type :delay :inputs '[[?a ?in]] :output '[?a ?in]}
               {:type :join
                :inputs '[[?a ?in] [?in]]
                :output '[?a ?in ?in]}
               {:type :delay :inputs '[[?a ?in]] :output '[?a ?in]}
               {:type :delay :inputs '[[?a ?in]] :output '[?a ?in]}
               {:type :delay :inputs '[[?in ?b]] :output '[?in ?b]}
               {:type :join
                :inputs '[[?in ?b] [?a ?in]]
                :output '[?in ?b ?a ?in]}]
              [{:type :add
                :inputs '[[?a ?in ?in] [?a ?in ?in]]
                :output '[?a ?in ?in]}
               {:type :add
                :inputs '[[?in ?b ?a ?in] [?in ?b ?a ?in]]
                :output '[?in ?b ?a ?in]}]
              [{:type :map
                :inputs '[[?in ?b ?a ?in]]
                :output '[?in ?b ?a ?in ?c]
                :mapping-fn (m/pred #(= + %))
                :args [[:idx 1] 10]}]
              [{:type :filter
                :inputs '[[?in ?b ?a ?in ?c]]
                :output '[?in ?b ?a ?in ?c]
                :filters [[> [:idx 4] 23]]}]
              [{:type :filter
                :inputs '[[?in ?b ?a ?in ?c]]
                :output '[?a ?c]
                :projections [[:idx 2] [:idx 4]]}]]
             sorted-ops))))
  (testing "Not, or joins"
    #_(let [q '[:find ?a
                :in $ % ?a
                :where
                (not-join [?a]
                          [?a :attr _])]
            circuit (c/build-circuit q)
            sorted-ops (mapv #(mapv datafy %)
                             (utils/topsort-circuit circuit :stratify? true))]
        (prn sorted-ops))
    (let [q '[:find ?a
              :in $ % ?a
              :where
              [?a :attr ?b]
              (not-join [?b]
                        [?b :attr2 10])]
          circuit (c/build-circuit q)
          sorted-ops (mapv #(mapv datafy %)
                           (utils/topsort-circuit circuit :stratify? true))]
      (is (match?
           '[[{:type :root :inputs [] :output []}]
             [{:type :filter
               :inputs [[:caudex.circuit/input ?a ?a]]
               :output [?a]
               :projections [[:idx 2]]}
              {:type :filter
               :inputs [[?a :attr ?b]]
               :output [?a ?b]
               :projections [[:idx 0] [:idx 2]]}
              {:type :filter
               :inputs [[?b :attr2 10]]
               :output [?b]
               :projections [[:idx 0]]}]
             [{:type :add :inputs [[?a] [?a]] :output [?a]}
              {:type :add
               :inputs [[?a ?b] [?a ?b]]
               :output [?a ?b]}
              {:type :join
               :inputs [[?a ?b] [?a]]
               :output [?a ?b ?a]}
              {:type :filter
               :inputs [[?b]]
               :output [?b]
               :filters []
               :projections [[:idx 0]]}]
             [{:type :delay :inputs [[?a]] :output [?a]}
              {:type :delay :inputs [[?a]] :output [?a]}
              {:type :delay :inputs [[?a ?b]] :output [?a ?b]}
              {:type :join
               :inputs [[?a ?b] [?a]]
               :output [?a ?b ?a]}
              {:type :add :inputs [[?b] [?b]] :output [?b]}
              {:type :join
               :inputs [[?b] [?b]]
               :output [?b ?b]}]
             [{:type :add
               :inputs [[?a ?b ?a] [?a ?b ?a]]
               :output [?a ?b ?a]}
              {:type :delay :inputs [[?b]] :output [?b]}]
             [{:type :filter
               :inputs [[?a ?b ?a]]
               :output [?b]
               :filters []
               :projections [[:idx 1]]}]
             [{:type :join :inputs [[?b] [?b]] :output [?b ?b]}
              {:type :add :inputs [[?b] [?b]] :output [?b]}]
             [{:type :add
               :inputs [[?b ?b] [?b ?b]]
               :output [?b ?b]}
              {:type :delay :inputs [[?b]] :output [?b]}
              {:type :delay :inputs [[?b]] :output [?b]}]
             [{:type :neg :inputs [[?b ?b]] :output [?b ?b]}]
             [{:type :add
               :inputs [[?a ?b ?a] [?a ?b ?a]]
               :output [?a ?b ?a]}]
             [{:type :filter
               :inputs [[?a ?b ?a]]
               :output [?a]
               :projections [[:idx 0]]}]]
           sorted-ops)))))
