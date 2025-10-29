(ns build
  (:require [clojure.tools.build.api :as b]))

(def lib 'net.clojars.jumraiya/caudex)
(def version "0.1.0")
(def class-dir "target/classes")
(def jar-file (format "target/%s-%s.jar" (name lib) version))

(defn clean [_]
  (b/delete {:path "target"}))

(defn jar [_]
  (clean nil)
  (b/copy-dir {:src-dirs ["src"]
               :target-dir class-dir})
  (b/compile-clj {:basis (b/create-basis {:project "deps.edn"})
                  :class-dir class-dir})
  (b/jar {:class-dir class-dir
          :jar-file jar-file}))