(ns packthread.core)


;;; Helper definitions.

(def ^:private if-like? #{'if 'if-not 'if-let})
(def ^:private if-for-when {'when 'if
                            'when-not 'if-not
                            'when-let 'if-let})


(defmacro match-form
  [form bindings test & body]
  `(when (and (list? ~form) (vector? '~bindings))
     (when ((if (get (set '~bindings) '&) >= =)
            (count ~form)
            (count (take-while #(not= % '&) '~bindings)))
       (let [~bindings ~form]
         (when ~test
           ~@body)))))


(defmacro in
  "Threads inner expressions through a projection of value.

  projector is a function which takes two arguments: a value and a function.
  It should apply the function to a _projection_ of the value, take the
  function's result, and reassemble from that result a value which can be
  used again in the outer context.

  For example,

    (+> 42
        (in (fn [v f]
              (* 2 (f (/ v 2))))
          inc)) ;=> 42.5

  This can be thought of as 'lifting' the body expressions into the 'world
  where things are twice as large'.

  As a special case, if projector is a keyword, in assumes that value is a
  map and that sub-key are threaded through the inner expressions.

  For example,

    (+> {:hello 42}
        (in :hello
          (+ 5))) ;=> {:hello 47}

  This macro can only be used inside +> or +>>.
  "
  [value projector & body]
  (throw (Exception. "packthread.core/in must be used inside `+>` or `+>>`")))

(defn -lift-into-projection
  [value projector into-fn]
  (let [projector (if (keyword? projector)
                    #(update-in %1 [projector] %2)
                    projector)]
    (projector value into-fn)))

(defn- thread-first-list
  [value form]
  (apply list (first form) value (rest form)))

(defn- thread-last-list
  [value form]
  (concat form [value]))

(defn- thread
  [thread-list value form]
  (or (match-form form [if test then] (if-like? if)
        (let [value-symbol (gensym)]
          `(let [~value-symbol ~value]
             (~if ~test
               ~(thread thread-list value-symbol then)
               (identity ~value-symbol)))))

      (match-form form [if test then else] (if-like? if)
        (let [value-symbol (gensym)]
          `(let [~value-symbol ~value]
             (~if ~test
               ~(thread thread-list value-symbol then)
               ~(thread thread-list value-symbol else)))))

      (match-form form [cond & clauses] (= cond 'cond)
        (let [value-symbol (gensym)
              threaded-clauses (->> clauses
                                    (partition 2)
                                    (map (fn [[test branch]]
                                           [test
                                            (thread thread-list value-symbol branch)]))
                                    (apply concat))
              has-else? (->> threaded-clauses
                             (partition 2)
                             (filter (fn [[test _]] (= :else test)))
                             first)
              clauses-with-else (if has-else?
                                  threaded-clauses
                                  (concat threaded-clauses [:else value-symbol]))]
          `(let [~value-symbol ~value]
             (cond ~@clauses-with-else))))

      (match-form form [condp f v & clauses] (= condp 'condp)
        (let [value-symbol (gensym)
              threaded-clauses (loop [clauses clauses
                                      threaded []]
                                 (let [[a b c & rest] clauses]
                                   (cond
                                    (= b :>>) (recur rest (conj threaded a :>> c))
                                    b (recur (cons c rest)
                                             (conj threaded a (thread thread-list value-symbol b)))
                                    a (conj threaded (thread thread-list value-symbol a))
                                    :else threaded)))]
          `(let [~value-symbol ~value]
             (condp ~f ~v ~@threaded-clauses))))

      (match-form form [case expr & clauses] (= case 'case)
        (let [value-symbol (gensym)
              threaded-clauses (->> clauses
                                    (partition-all 2)
                                    (map (fn [[test branch]]
                                           (if branch
                                             [test (thread thread-list value-symbol branch)]
                                             [(thread thread-list value-symbol test)])))
                                    (apply concat))]
          `(let [~value-symbol ~value]
             (case ~expr ~@threaded-clauses))))

      (match-form form [when test & body] (if-for-when when)
        (let [value-symbol (gensym)
              threaded-body (reduce (partial thread thread-list) value-symbol body)
              if (if-for-when when)]
          `(let [~value-symbol ~value]
             (~if ~test
               ~threaded-body
               ~value-symbol))))

      (match-form form [sym & body] (= sym 'do)
        (reduce (partial thread thread-list) value body))

      (match-form form [sym bindings & body] (= sym 'let)
        (let [value-symbol (gensym)
              threaded-body (reduce (partial thread thread-list) value body)
              new-bindings (concat [value-symbol value] bindings)]
          `(let [~@new-bindings]
             ~threaded-body)))

      (match-form form [sym projector & body] (= sym 'in)
        (let [projection-symbol (gensym)
              threaded-body (reduce (partial thread thread-list) projection-symbol body)]
          `(-lift-into-projection ~value ~projector
                                  (fn [~projection-symbol]
                                    ~threaded-body))))

      (when (list? form)
        (thread-list value form))

      (list form value)))


;;; Public API

(defmacro +>
  "Threads value through forms in much the same way as ->, except for special
  handling of the following forms:

  if, if-not, if-let, when, when-not, when-let:

    The value is threaded through the then and else clauses independently,
    leaving the test conditions alone.  If an else clause is missing, it is
    will be supplied as though the value had been threaded through identity
    in that case.

    For example,

      (+> 42 (if true inc)) ;=> 43
      (+> 42 (if false inc)) ;=> 42

    In when, when-not, and when-let forms, the value is threaded through each
    form in the body, not just the last.

  cond:

    The test clauses are left untouched and the value is threaded through
    the expr clauses of each condition.  If no :else condition was supplied,
    +> pretends as though it has been (identity), and threads the value
    through that.

    For example,

      (+> 42
          (cond
            (= 1 2)
            inc)) ;=> 42

      (+> 42
          (cond
            (= 1 1)
            dec)) ;=> 41

  do:

    The current expr is threaded through the body forms of the do.
  "
  [value & forms]
  (reduce (partial thread thread-first-list) value forms))

(defmacro +>>
  "Threads value through forms in much the same way as ->>, except for special
  handling of several forms.  These forms are documented in (doc +>)
  "
  [value & forms]
  (reduce (partial thread thread-last-list) value forms))
