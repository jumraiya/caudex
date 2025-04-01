(ns caudex.circuit-test
  (:require [clojure.test :refer [deftest is testing]]
            [caudex.circuit :as c]
            [caudex.utils :as utils]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]
            [clojure.core.protocols :refer [datafy]]))


#_(defn- find-op-nodes* [circuit op-type inputs output]
    (let [nodes (into []
                      (comp
                       (filter utils/is-op?)
                       (filter
                        #(and (= (dbsp/-get-op-type %) op-type)
                              (= inputs (dbsp/-get-input-types %))
                              (= output (dbsp/-get-output-type %)))))
                      (uber/nodes circuit))]
      (if (= (count nodes) 1) (first nodes) nodes)))

 (deftest test-build-circuit
  (testing "Only pattern clauses"
    (let [q '[:find ?a ?b
              :where
              [?a :attr-1 12]
              [?b :attr-2 ?a]]
          circuit (c/build-circuit q)
          sorted-ops (mapv #(mapv utils/op->edn %)
                           (utils/topsort-circuit circuit :stratify? true))]
      (is (match?
           [[{:type :root}]
            (m/in-any-order
             [{:type :filter :output '[[?b ?a]]}
              {:type :filter :output '[[?a]]}])
            (m/in-any-order
             [{:type :add :inputs '[[[?b ?a]] [[?b ?a]]] :output '[[?b ?a]]}
              {:type :add :inputs '[[[?a]] [[?a]]] :output '[[?a]]}
              {:type :join :inputs '[[[?a]] [[?b ?a]]] :output '[[?a] [?b ?a]]}])
            (m/in-any-order
             [{:type :delay :inputs '[[[?b ?a]]] :output '[[?b ?a]]}
              {:type :delay :inputs '[[[?b ?a]]] :output '[[?b ?a]]}
              {:type :delay :inputs '[[[?a]]] :output '[[?a]]}
              {:type :join :inputs '[[[?a]] [[?b ?a]]] :output '[[?a] [?b ?a]]}])
            [{:type :add :inputs '[[[?a] [?b ?a]] [[?a] [?b ?a]]]
              :output '[[?a] [?b ?a]]}]
            [{:type :filter,
              :inputs '[[[?a] [?b ?a]]]
              :output '[[?a] [?b]]}]]
           sorted-ops))))
  (testing "Pattern and pred clauses"
    (let [q '[:find ?a ?c
              :in $ %
              :where
              [?a :attr-1 ?b]
              [(+ ?b 10) ?c]
              [(> ?c 23)]]
          circuit (c/build-circuit q)
          sorted-ops (mapv #(mapv datafy %)
                           (utils/topsort-circuit circuit :stratify? true))]
      (is (match?
           [[{:type :root}]
            [{:type :filter :inputs [] :output '[[?a ?b]]
              :filters
              [[= [0 1] :attr-1]]
              :projections
              [[0 0] [0 2]]}]
            [{:type :map
              :inputs '[[[?a ?b]]]
              :output '[[?a ?b] [?c]]
              :mapping-fn (m/pred #(= + %))
              :args [[0 1] 10]}]
            [{:type :filter
              :inputs '[[[?a ?b] [?c]]]
              :output '[[?a ?b] [?c]]
              :filters [[> [1 0] 23]]}]
            [{:type :filter
              :inputs '[[[?a ?b] [?c]]]
              :output '[[?a] [?c]]
              :projections [[0 0] [1 0]]}]]
           sorted-ops)))))
