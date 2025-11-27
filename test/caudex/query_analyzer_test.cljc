(ns caudex.query-analyzer-test
  (:require [clojure.test :refer [deftest is testing]]
            [caudex.graph :as graph]
            [caudex.query-analyzer :as q]
            [caudex.utils :as utils]
            [matcher-combinators.test]
            [matcher-combinators.matchers :as m]))


(deftest test-analyze
  #_(testing "Simple clause"
    (let [{:keys [inputs graph projections]} (q/analyze
                                              '[:find ?b
                                                :in ?in
                                                :where
                                                [?a :attr ?in]
                                                [?b :attr2 ?a]])]
      (is (= [{:type :rel, :idx 0, :symbol '?b}] projections))
      (is (match? ['?in] inputs))
      (is (match? #{'?in '?a '?b} (set (graph/nodes graph))))
      (is (match? (m/in-any-order [{:src '?a :dest '?in}
                                   {:src '?b :dest '?a}])
                  (graph/edges graph)))))
  #_(testing "Predicates and functions"
    (let [{:keys [graph]} (q/analyze
                           '[:find ?b ?bind
                             :in ?in
                             :where
                             [?a :attr ?in]
                             [?in :attr2 ?b]
                             [(pos? ?a)]
                             [(inc ?b) ?bind]
                             [(dec ?b) ?in]])
          edges (mapv #(into % (graph/attrs graph %)) (graph/edges graph))]
      (is (match? (m/in-any-order
                   [{:src '?a :dest '?in :label :attr :clause-type :pattern}
                    {:src '?in :dest '?b :label :attr2 :clause-type :pattern}
                    {:src '?a :dest "pos?-0" :label [:arg 0] :clause-type :pred-arg}
                    {:src '?b :dest "inc-0" :label [:arg 0] :clause-type :fn-arg}
                    {:src "inc-0" :dest '?bind :label :binding}
                    {:src '?b :dest "dec-0" :label [:arg 0]}
                    {:src "dec-0" :dest '?in :label :binding}])
                  edges))))
  (testing "Or, not joins"
    (let [{:keys [graph]} (q/analyze
                           '[:find ?b
                             :where
                             [?a :attr ?b]
                             (or-join [?b]
                                      [?b :attr2 :test]
                                      (and
                                       (not-join [?b]
                                                 [?b :attr2 :test])
                                       [?b :attr3 :test2]))])

          edn (utils/circuit->edn graph)]
      (is (match?
           {:directed-edges
            (m/in-any-order
             [['?a '?b {:label :attr}]
              ['?b "or-0" {:label [:arg 0]}]
              ["or-0"
               {:directed-edges [['?b :test {:label :attr2, :clause-type :pattern}]]}
               {:label :conj}]
              ["or-0" {:directed-edges
                       [['?b {:nodes
                              (m/in-any-order [['?b {}] [:test {}]])
                              :directed-edges
                              [['?b :test {:label :attr2, :clause-type :pattern}]]}
                         {:label [:arg 0]}]
                        ['?b :test2 {:label :attr3, :clause-type :pattern}]]}
               {:label :conj}]])}
           edn))))

  #_(testing "Rules non-recursive"
    (let [{:keys [graph rules]} (q/analyze '[:find ?a
                                             :in $ % ?in
                                             :where
                                             [?in :asd ?a]
                                             [?a :attr ?b]
                                             (rule ?a ?b)]
                                           '[[(rule ?a ?b)
                                              [?a :attr2 :test]
                                              [?b :attr3 :val]]])
          edges (mapv #(into % (graph/attrs graph %)) (graph/edges graph))
          r-graph (-> rules vals first :branches first :graph)
          rule-edges (mapv #(into % (graph/attrs r-graph %)) (graph/edges r-graph))]
      (is (false? (get-in rules ['rule :recursive?])))
      (is (match? (m/in-any-order
                   [{:src '?in :dest '?a}
                    {:src '?a :dest '?b}
                    {:src '?a :dest "rule-0" :label [:arg 0] :clause-type :rule-arg}
                    {:src '?b :dest "rule-0" :label [:arg 1] :clause-type :rule-arg}])
                  edges))
      (is (match? (m/in-any-order
                   [{:src '?a :dest :test :label :attr2}
                    {:src '?b :dest :val :label :attr3}])
                  rule-edges))))

  #_(testing "Rules recursive"
    (let [{:keys [rules]} (q/analyze '[:find ?a
                                       :in $ % ?in
                                       :where
                                       (rule ?a ?in)]
                                     '[[(rule ?a ?p)
                                        [?a :parent ?p]]
                                       [(rule ?a ?p)
                                        [?a :parent ?ap]
                                        (rule ?ap ?p)]])
          {:keys [args graph recursive?]} (-> rules vals first :branches second)
          rule-edges (mapv #(into % (graph/attrs graph %)) (graph/edges graph))]
      (is (true? (get-in rules ['rule :recursive?])))
      (is (true? recursive?))
      (is (match? '[?a ?p] args))
      (is (match? (m/in-any-order
                   [{:src '?a :dest '?ap}
                    {:src '?ap :dest "rule-0" :label [:arg 0]}
                    {:src '?p :dest "rule-0" :label [:arg 1]}])
                  rule-edges))))
  #_(testing "Marking required args to or, not joins and rules"
    (let [{:keys [graph]} (q/analyze
                           '[:find ?a ?b
                             :where
                             [?a :attr "asd"]
                             (or-join [?a ?b]
                                      [?a :attr-2 ?b]
                                      (and [?a :attr-3 ?c]
                                           [(< ?b ?c)]))])
          edges (mapv #(vector % (graph/attr graph % :required?))
                      (graph/in-edges graph "or-0"))
          {:keys [graph]} (q/analyze
                           '[:find ?a ?b
                             :where
                             [?a :attr "asd"]
                             (not-join [?a ?b]
                                       [?a :attr-3 ?c]
                                       [(< ?b ?c)])])
          edges-2 (mapv #(vector % (graph/attr graph % :required?))
                        (graph/in-edges graph (some #(when (graph/is-graph? %) %)
                                                    (graph/nodes graph))))
          {:keys [graph]} (q/analyze
                           '[:find ?a ?c
                             :in $ %
                             :where
                             [?a :attr "asd"]
                             [?a :attr-2 ?c]
                             (rule ?c)]
                           '[[(rule ?b)
                              [(< ?b 10)]]])
          edges-3 (mapv #(vector % (graph/attr graph % :required?))
                        (graph/in-edges graph
                                        (some #(when (= 'rule (graph/attr graph % :fn)) %)
                                              (graph/nodes graph))))]
      (is (match?
           (m/in-any-order
            [[{:src '?a} nil] [{:src '?b} true]])
           edges))
      (is (match?
           (m/in-any-order
            [[{:src '?a} nil] [{:src '?b} true]])
           edges-2))
      (is (match? [[{:src '?c} true]] edges-3)))))
#trace
(deftest test-remap-nodes
  (let [query '[:find ?a ?b
                :in $ %
                :where
                [?a :attr 10]
                (rule ?a ?b)]
        rules '[[(rule ?p ?q)
                 [?q :attr-2 :test]
                 (or-join [?p]
                          [(= ?p :a)]
                          [(= ?p :b)])
                 #_(not-join [?p]
                             [?p :attr-3 ?r]
                             [(> ?r 1)])]]
        {:keys [graph rules]} (q/analyze query rules)
        graph (-> rules (get 'rule) :branches first :graph)
        graph (utils/remap-nodes graph {'?a '?p '?b '?q})]
    (utils/prn-graph graph)))
