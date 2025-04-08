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
           [[{:type :root}]
            [{:type :filter
              :inputs [[:caudex.circuit/input '?in '?in]]
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
             {:type :add
              :inputs '[[?in ?b] [?in ?b]]
              :output '[?in ?b]}
             {:type :join
              :inputs '[[?in ?b] [?a ?in]]
              :output '[?in ?b ?a ?in]}]
            [{:type :delay :inputs '[[?in]] :output '[?in]}
             {:type :delay :inputs '[[?in]] :output '[?in]}
             {:type :delay
              :inputs '[[?a ?in]]
              :output '[?a ?in]}
             {:type :delay
              :inputs '[[?a ?in]]
              :output '[?a ?in]}
             {:type :delay
              :inputs '[[?in ?b]]
              :output '[?in ?b]}
             {:type :join
              :inputs '[[?in ?b] [?a ?in]]
              :output '[?in ?b ?a ?in]}]
            [{:type :add
              :inputs '[[?in ?b ?a ?in] [?in ?b ?a ?in]]
              :output '[?in ?b ?a ?in]}]
            [{:type :add
              :inputs '[[?in ?b ?a ?in] [?in ?b ?a ?in]]
              :output '[?in ?b ?a ?in]}
             {:type :join
              :inputs '[[?in ?b ?a ?in] [?in]]
              :output '[?in ?b ?a ?in ?in]}]
            [{:type :delay
              :inputs '[[?in ?b ?a ?in]]
              :output '[?in ?b ?a ?in]}
             {:type :join
              :inputs '[[?in ?b ?a ?in] [?in]]
              :output '[?in ?b ?a ?in ?in]}]
            [{:type :add
              :inputs '[[?in ?b ?a ?in ?in] [?in ?b ?a ?in ?in]]
              :output '[?in ?b ?a ?in ?in]}]
            [{:type :map
              :inputs '[[?in ?b ?a ?in ?in]]
              :output '[?in ?b ?a ?in ?in ?c]
              :mapping-fn (m/pred #(= % +))
              :args [[:idx 1] 10]}]
            [{:type :filter
              :inputs '[[?in ?b ?a ?in ?in ?c]]
              :output '[?in ?b ?a ?in ?in ?c]
              :filters [[> [:idx 5] 23]]
              :projections []}]
            [{:type :filter
              :inputs '[[?in ?b ?a ?in ?in ?c]]
              :output '[?a ?c]
              :projections [[:idx 2] [:idx 5]]}]]
           sorted-ops))))
  #_(testing "Not, or joins"
      (let [q '[:find ?a
                :in $ % ?a
                :where
                (not-join [?a]
                          [?a :attr _])]
            circuit (c/build-circuit q)
            sorted-ops (mapv #(mapv datafy %)
                             (utils/topsort-circuit circuit :stratify? true))]
        (prn sorted-ops))))
