\\ TPTP THF backend with higher-order SCC leastness.

(define shenlogic.thf.render
  [theory Declarations Rules SCCs] _ ->
    (if (shenlogic.thf.supported? Rules)
        [ok (@s "% ShenLogic typed higher-order specification" (n->string 10)
                (shenlogic.thf.declarations Declarations)
                (shenlogic.thf.rules Rules)
                (shenlogic.thf.leastness SCCs Rules Declarations))]
        [error unsupported-thf])
  _ _ -> [error invalid-theory])

(define shenlogic.thf.supported?
  [] -> true
  [[rule _ _ _ Bound Premises Result] | Rs] ->
    (and (shenlogic.thf.term-supported? Result Bound)
         (shenlogic.thf.premises-supported? Premises Bound)
         (shenlogic.thf.supported? Rs)))

(define shenlogic.thf.premises-supported?
  [] _ -> true
  [[match _ _] | _] _ -> false
  [[not-applicable | _] | _] _ -> false
  [[call _ Args Result] | Ps] Bound ->
    (and (shenlogic.thf.terms-supported? (append Args [Result]) Bound)
         (shenlogic.thf.premises-supported? Ps Bound))
  [[constraint E] | Ps] Bound ->
    (and (shenlogic.thf.formula-supported? E Bound)
         (shenlogic.thf.premises-supported? Ps Bound))
  [[= A B] | Ps] Bound ->
    (and (shenlogic.thf.term-supported? A Bound)
         (and (shenlogic.thf.term-supported? B Bound)
              (shenlogic.thf.premises-supported? Ps Bound)))
  [[!= A B] | Ps] Bound ->
    (and (shenlogic.thf.term-supported? A Bound)
         (and (shenlogic.thf.term-supported? B Bound)
              (shenlogic.thf.premises-supported? Ps Bound)))
  [_ | _] _ -> false)

(define shenlogic.thf.terms-supported?
  [] _ -> true
  [X | Xs] Bound ->
    (and (shenlogic.thf.term-supported? X Bound)
         (shenlogic.thf.terms-supported? Xs Bound)))

(define shenlogic.thf.term-supported?
  X Bound ->
    (if (number? X)
        true
        (if (element? X Bound)
            true
            (if (cons? X)
                (shenlogic.thf.compound-term-supported? X Bound)
                false))))

(define shenlogic.thf.compound-term-supported?
  [add A B] Bound -> (shenlogic.thf.terms-supported? [A B] Bound)
  [sub A B] Bound -> (shenlogic.thf.terms-supported? [A B] Bound)
  [mul A B] Bound -> (shenlogic.thf.terms-supported? [A B] Bound)
  [ite C T F] Bound ->
    (and (shenlogic.thf.formula-supported? C Bound)
         (shenlogic.thf.terms-supported? [T F] Bound))
  _ _ -> false)

(define shenlogic.thf.formula-supported?
  true _ -> true
  false _ -> true
  [eq A B] Bound -> (shenlogic.thf.terms-supported? [A B] Bound)
  [lt A B] Bound -> (shenlogic.thf.terms-supported? [A B] Bound)
  [gt A B] Bound -> (shenlogic.thf.terms-supported? [A B] Bound)
  [le A B] Bound -> (shenlogic.thf.terms-supported? [A B] Bound)
  [ge A B] Bound -> (shenlogic.thf.terms-supported? [A B] Bound)
  [not A] Bound -> (shenlogic.thf.formula-supported? A Bound)
  _ _ -> false)

(define shenlogic.thf.declarations
  [] -> ""
  [[relation Name Sorts Result] | Ds] ->
    (@s "thf(" (shenlogic.thf.atom Name) "_type,type,("
        (shenlogic.thf.signature (+ 1 (length Sorts))) " > $o))."
        (n->string 10) (shenlogic.thf.declarations Ds)))

(define shenlogic.thf.signature
  1 -> "$int"
  N -> (@s "$int > " (shenlogic.thf.signature (- N 1))))

(define shenlogic.thf.rules
  [] -> ""
  [R | Rs] ->
    (@s "thf(" (shenlogic.thf.rule-id R) ",axiom,("
        (shenlogic.thf.rule-formula R []) "))." (n->string 10)
        (shenlogic.thf.rules Rs)))

(define shenlogic.thf.rule-id
  [rule Id _ _ _ _ _] -> (@s "rule_" (shenlogic.thf.atom Id)))

(define shenlogic.thf.rule-formula
  [rule _ Function Args Bound Premises Result] Map ->
    (@s "! [" (shenlogic.thf.binders Bound) "] : ("
        (shenlogic.thf.implication
          (shenlogic.thf.body Premises Map)
          (shenlogic.thf.call Function (append Args [Result]) Map)) ")"))

(define shenlogic.thf.implication
  "true" Q -> Q
  P Q -> (@s "(" P " => " Q ")"))

(define shenlogic.thf.body
  [] _ -> "true"
  [P] Map -> (shenlogic.thf.premise P Map)
  Ps Map -> (@s "(" (shenlogic.thf.premises Ps Map) ")"))

(define shenlogic.thf.premises
  [] _ -> "$true"
  [P] Map -> (shenlogic.thf.premise P Map)
  [P | Ps] Map -> (@s (shenlogic.thf.premise P Map) " & "
                       (shenlogic.thf.premises Ps Map)))

(define shenlogic.thf.premise
  [call Name Args Result] Map ->
    (shenlogic.thf.call Name (append Args [Result]) Map)
  [constraint E] Map -> (shenlogic.thf.expr E)
  [= A B] _ -> (@s "(" (shenlogic.thf.expr A) " = " (shenlogic.thf.expr B) ")")
  [!= A B] _ -> (@s "(" (shenlogic.thf.expr A) " != " (shenlogic.thf.expr B) ")")
  X _ -> (shenlogic.thf.expr X))

(define shenlogic.thf.call
  Name Args Map ->
    (@s "(" (shenlogic.thf.relation Name Map) " @ "
        (shenlogic.thf.arguments Args) ")"))

(define shenlogic.thf.relation
  Name Map ->
    (let Found (shenlogic.thf.lookup Name Map)
      (if (= Found not-found) (shenlogic.thf.atom Name) (hd (tl Found)))))

(define shenlogic.thf.arguments
  [X] -> (shenlogic.thf.expr X)
  [X | Xs] -> (@s (shenlogic.thf.expr X) " @ "
                  (shenlogic.thf.arguments Xs)))

(define shenlogic.thf.expr
  true -> "$true"
  false -> "$false"
  [add A B] -> (@s "$sum(" (shenlogic.thf.expr A) "," (shenlogic.thf.expr B) ")")
  [sub A B] -> (@s "$difference(" (shenlogic.thf.expr A) "," (shenlogic.thf.expr B) ")")
  [mul A B] -> (@s "$product(" (shenlogic.thf.expr A) "," (shenlogic.thf.expr B) ")")
  [eq A B] -> (@s "(" (shenlogic.thf.expr A) " = " (shenlogic.thf.expr B) ")")
  [lt A B] -> (@s "$less(" (shenlogic.thf.expr A) "," (shenlogic.thf.expr B) ")")
  [gt A B] -> (@s "$greater(" (shenlogic.thf.expr A) "," (shenlogic.thf.expr B) ")")
  [le A B] -> (@s "$lesseq(" (shenlogic.thf.expr A) "," (shenlogic.thf.expr B) ")")
  [ge A B] -> (@s "$greatereq(" (shenlogic.thf.expr A) "," (shenlogic.thf.expr B) ")")
  [not A] -> (@s "~(" (shenlogic.thf.expr A) ")")
  X -> (if (number? X) (str X) (shenlogic.thf.variable X)))

(define shenlogic.thf.binders
  [] -> "Dummy:$int"
  [X] -> (@s (shenlogic.thf.variable X) ":$int")
  [X | Xs] -> (@s (shenlogic.thf.variable X) ":$int,"
                  (shenlogic.thf.binders Xs)))

(define shenlogic.thf.leastness
  [] _ _ -> ""
  [[scc Names] | Ss] Rules Declarations ->
    (let Map (shenlogic.thf.candidates Names [])
      (@s "thf(least_" (shenlogic.thf.join-atoms Names) ",axiom,("
          "! [" (shenlogic.thf.candidate-binders Names Declarations Map) "] : ("
          (shenlogic.thf.implication
            (shenlogic.thf.closures Names Rules Map)
            (shenlogic.thf.containments Names Declarations Map)) ")))."
          (n->string 10)
          (shenlogic.thf.leastness Ss Rules Declarations))))

(define shenlogic.thf.candidates
  [] Acc -> (reverse Acc)
  [N | Ns] Acc ->
    (shenlogic.thf.candidates Ns
      [[N (@s "R_" (shenlogic.thf.atom N))] | Acc]))

(define shenlogic.thf.candidate-binders
  [N] Ds Map ->
    (@s (shenlogic.thf.relation N Map) ":("
        (shenlogic.thf.signature (+ 1 (shenlogic.thf.arity N Ds))) " > $o)")
  [N | Ns] Ds Map ->
    (@s (shenlogic.thf.relation N Map) ":("
        (shenlogic.thf.signature (+ 1 (shenlogic.thf.arity N Ds))) " > $o),"
        (shenlogic.thf.candidate-binders Ns Ds Map)))

(define shenlogic.thf.closures
  Names Rules Map ->
    (let Selected (shenlogic.thf.select-rules Names Rules)
      (if (= Selected []) "$true" (shenlogic.thf.rule-formulas Selected Map))))

(define shenlogic.thf.rule-formulas
  [R] Map -> (shenlogic.thf.rule-formula R Map)
  [R | Rs] Map -> (@s "(" (shenlogic.thf.rule-formula R Map) " & "
                      (shenlogic.thf.rule-formulas Rs Map) ")"))

(define shenlogic.thf.select-rules
  _ [] -> []
  Names [R | Rs] ->
    (if (element? (shenlogic.thf.rule-function R) Names)
        [R | (shenlogic.thf.select-rules Names Rs)]
        (shenlogic.thf.select-rules Names Rs)))

(define shenlogic.thf.rule-function
  [rule _ F _ _ _ _] -> F)

(define shenlogic.thf.containments
  [N] Ds Map -> (shenlogic.thf.containment N (shenlogic.thf.arity N Ds) Map)
  [N | Ns] Ds Map ->
    (@s "(" (shenlogic.thf.containment N (shenlogic.thf.arity N Ds) Map)
        " & " (shenlogic.thf.containments Ns Ds Map) ")"))

(define shenlogic.thf.containment
  Name Arity Map ->
    (let Args (shenlogic.thf.generic-args Arity 0)
      (let All (append Args [(intern "Result")])
        (@s "! [" (shenlogic.thf.binders All) "] : ("
            (shenlogic.thf.call Name All []) " => "
            (shenlogic.thf.call Name All Map) ")"))))

(define shenlogic.thf.generic-args
  0 _ -> []
  N I -> [(intern (@s "A" (str I))) |
          (shenlogic.thf.generic-args (- N 1) (+ I 1))])

(define shenlogic.thf.arity
  _ [] -> 0
  N [[relation N Sorts _] | _] -> (length Sorts)
  N [_ | Ds] -> (shenlogic.thf.arity N Ds))

(define shenlogic.thf.lookup
  _ [] -> not-found
  X [[X V] | _] -> [found V]
  X [_ | Xs] -> (shenlogic.thf.lookup X Xs))

(define shenlogic.thf.join-atoms
  [X] -> (shenlogic.thf.atom X)
  [X | Xs] -> (@s (shenlogic.thf.atom X) "_" (shenlogic.thf.join-atoms Xs)))

(define shenlogic.thf.atom
  X -> (@s "sl_" (shenlogic.thf.clean (str X))))

(define shenlogic.thf.variable
  X -> (@s "V_" (shenlogic.thf.clean (str X))))

\\ The verified source fragment currently restricts names to portable atoms.
(define shenlogic.thf.clean
  "" -> ""
  S -> (let C (pos S 0)
         (@s (shenlogic.thf.clean-char C)
             (shenlogic.thf.clean (tlstr S)))))

(define shenlogic.thf.clean-char
  "?" -> "_q"
  "-" -> "_"
  "." -> "_"
  "/" -> "_slash"
  "<" -> "_lt"
  ">" -> "_gt"
  "=" -> "_eq"
  "*" -> "_mul"
  "+" -> "_add"
  C -> C)
