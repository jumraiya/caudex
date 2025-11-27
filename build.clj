(ns build
  (:require [clojure.tools.build.api :as b]))

(def lib 'net.clojars.jumraiya/caudex)
(def version "0.1.3")
(def class-dir "target/classes")
(def basis (b/create-basis {:project "deps.edn"}))
(def jar-file (format "target/%s-%s.jar" (name lib) version))

(defn clean [_]
  (b/delete {:path "target"}))

(defn jar [_]
  (clean nil)
  (b/copy-dir {:src-dirs ["src"]
               :target-dir class-dir})
  (b/jar {:class-dir class-dir
          :jar-file jar-file
          :scm {:tag (str "v" version)}
          :pom-data [[:description "A Clojure library for building DBSP circuits from Datalog queries"]
                     [:url "https://github.com/jumraiya/caudex"]
                     [:licenses
                      [:license
                       [:name "MIT License"]
                       [:url "https://opensource.org/licenses/MIT"]]]
                     [:developers
                      [:developer
                       [:name "Jaideep Umraiya"]]]
                     [:scm
                      [:url "https://github.com/jumraiya/caudex"]
                      [:connection "scm:git:https://github.com/jumraiya/caudex.git"]
                      [:developerConnection "scm:git:ssh://git@github.com/jumraiya/caudex.git"]
                      [:tag (str "v" version)]]]}))

(defn install [_]
  (jar nil)
  (b/install {:basis basis
              :lib lib
              :version version
              :jar-file jar-file
              :class-dir class-dir}))

(defn deploy [_]
  (jar nil)
  (try
    ((requiring-resolve 'deps-deploy.deps-deploy/deploy)
     {:installer :remote
      :artifact jar-file
      :pom-file (b/pom-path {:lib lib :class-dir class-dir})})
    (catch Exception e
      (println "Deploy failed. Make sure you have valid Clojars credentials.")
      (println "Set CLOJARS_USERNAME and CLOJARS_PASSWORD environment variables")
      (println "or configure them in ~/.clojars/config.edn")
      (throw e))))
