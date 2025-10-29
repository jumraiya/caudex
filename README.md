# Caudex

A Clojure(script) library for building abstract datalog incremental view DBSP circuits https://arxiv.org/abs/2203.16684.
The circuits are mostly based on the theory described in the paper, but it is not a exact implementation.

## Overview

Caudex compiles Datomic-style queries into circuit graphs that can be executed incrementally. It supports pattern matching, joins, predicates, functions, rule, or-joins and not-joins

## Quick Start

### Building a Simple Circuit

```clojure
(require '[caudex.circuit :as c])

;; Define a simple query
(def query '[:find ?person ?friend
             :where
             [?person :name ?name]
             [?person :friend ?friend]])

;; Build the circuit
(def circuit (c/build-circuit query))
```

See test/caudex/impl/circuit_test.cljc for advanced usage

