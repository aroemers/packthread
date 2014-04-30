(ns packthread.core
  (:require [clojure.core.match :refer [match]]))

(def if-like? #{'if 'if-not 'if-let})
(def if-for-when {'when 'if,
                  'when-not 'if-not
                  'when-let 'if-let})

(defn thread
  [value form]
  (match [form]
    [([if :guard if-like? test then] :seq)]
    (let [value-symbol (gensym)]
      `(let [~value-symbol ~value]
         (~if ~test
           ~(thread value-symbol then)
           (identity ~value-symbol))))

    [([if :guard if-like? test then else] :seq)]
    (let [value-symbol (gensym)]
      `(let [~value-symbol ~value]
         (~if ~test
           ~(thread value-symbol then)
           ~(thread value-symbol else))))

    [(['cond & clauses] :seq)]
    (let [value-symbol (gensym)
          threaded-clauses (->> clauses
                                (partition 2)
                                (map (fn [[test branch]]
                                       [test
                                        (thread value-symbol branch)]))
                                (apply concat))
          has-else? (->> threaded-clauses
                         (partition 2)
                         (filter (fn [[test _]] (= :else test)))
                         first)
          clauses-with-else (if has-else?
                              threaded-clauses
                              (concat threaded-clauses [:else value-symbol]))]
      `(let [~value-symbol ~value]
         (cond ~@clauses-with-else)))

    [([when :guard if-for-when test & body] :seq)]
    (let [value-symbol (gensym)
          threaded-body (reduce thread value-symbol body)
          if (if-for-when when)]
      `(let [~value-symbol ~value]
         (~if ~test
           ~threaded-body
           ~value-symbol)))

    [(['do & body] :seq)]
    (reduce thread value body)

    [([f & r] :seq :guard list?)]
    (apply list f value r)

    :else
    (list form value)))

(defmacro +>
  [value & forms]
  (reduce thread value forms))
