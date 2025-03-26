(ns caudex.circuit-test
  (:require [clojure.test :refer [deftest is testing]]
            [caudex.circuit :as c]
            [caudex.utils :as utils]
            [caudex.dbsp :as dbsp]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]
            [ubergraph.alg :as alg]
            [ubergraph.core :as uber]))


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
  #_(testing "Only pattern clauses"
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
               [{:type :map :output '[[?b ?a]]}
                {:type :map :output '[[?a]]}])
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
                :output '[[?a] [?b ?a]]}]]
             sorted-ops))))
  (testing "Pattern and pred clauses"
    (let [q '[:find ?a ?c
              :in $ %
              :where
              [?a :attr-1 ?b]
              [?b :attr-2 ?c]
              [?c :attr-3 ?d]
              [(+ ?d 10) ?e]
              [(> ?e 10)]
              (rule ?d ?e)]
          circuit (c/build-circuit q)])))
