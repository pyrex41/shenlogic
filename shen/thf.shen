\\ TPTP THF backend with higher-order SCC leastness.

(define shenlogic.thf.render
  [theory [value-signature Constructors] Relations Rules SCCs NameMap] Profile ->
    (let Names (shenlogic.thf.v2-namemap-entries NameMap)
      (if (shenlogic.thf.v2-valid? Constructors Relations Rules SCCs Names)
        [ok (shenlogic.thf.v2-output Constructors Relations Rules SCCs Names)]
        [error invalid-thf-ir])
      )
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
  " " -> "_"
  ":" -> "_colon"
  "," -> "_comma"
  "!" -> "_bang"
  "(" -> "_lp"
  ")" -> "_rp"
  "[" -> "_lb"
  "]" -> "_rb"
  "_" -> "_under"
  C -> C)

\\ ---------------------------------------------------------------------------
\\ Value IR (v2).  This dialect is deliberately kept separate from the old
\\ integer-only renderer above.  Every entry point first validates the complete
\\ tree; malformed data therefore has one stable result instead of a partial
\\ TPTP document.

(define shenlogic.thf.v2-valid?
  Constructors Relations Rules SCCs NameMap ->
    (and (shenlogic.thf.v2-constructors-valid? Constructors)
      (and (shenlogic.thf.v2-relations-valid? Relations)
        (and (shenlogic.thf.v2-rules-valid? Rules Relations)
          (and (shenlogic.thf.v2-sccs-valid? SCCs Relations)
            (and (shenlogic.thf.v2-namemap-valid? NameMap)
                 (shenlogic.thf.v2-known-rules? Rules Constructors)))))))

(define shenlogic.thf.v2-constructors-valid?
  [] -> true
  [[constructor _ _ Arity] | Cs] ->
    (and (number? Arity)
      (and (>= Arity 0) (shenlogic.thf.v2-constructors-valid? Cs)))
  _ -> false)

(define shenlogic.thf.v2-relations-valid?
  [] -> true
  [[relation _ Sorts value] | Rs] ->
    (and (shenlogic.thf.v2-sorts-valid? Sorts)
         (shenlogic.thf.v2-relations-valid? Rs))
  _ -> false)

(define shenlogic.thf.v2-sorts-valid?
  [] -> true
  [value | Ss] -> (shenlogic.thf.v2-sorts-valid? Ss)
  _ -> false)

(define shenlogic.thf.v2-rules-valid?
  [] _ -> true
  [[rule _ Function Clause Path Args Bound Premises Result] | Rs] Relations ->
    (and (number? Clause)
      (and (shenlogic.thf.v2-path-valid? Path)
        (and (shenlogic.thf.v2-relation-name? Function Relations)
          (and (shenlogic.thf.v2-terms-valid? Args Bound)
            (and (shenlogic.thf.v2-bound-valid? Bound)
              (and (shenlogic.thf.v2-premises-valid? Premises Bound Relations)
                (and (shenlogic.thf.v2-term-valid? Result Bound)
                     (shenlogic.thf.v2-rules-valid? Rs Relations))))))))
  _ _ -> false)

\\ A path is metadata, but it must remain a proper finite list (or an integer
\\ path id, as emitted by early v2 producers).
(define shenlogic.thf.v2-path-valid?
  X -> (if (number? X) true (shenlogic.thf.v2-proper-list? X)))

(define shenlogic.thf.v2-proper-list?
  [] -> true
  [_ | Xs] -> (shenlogic.thf.v2-proper-list? Xs)
  _ -> false)

(define shenlogic.thf.v2-bound-valid?
  [] -> true
  [[v-var _] | Bs] -> (shenlogic.thf.v2-bound-valid? Bs)
  [[i-var _] | Bs] -> (shenlogic.thf.v2-bound-valid? Bs)
  [[s-var _] | Bs] -> (shenlogic.thf.v2-bound-valid? Bs)
  _ -> false)

(define shenlogic.thf.v2-terms-valid?
  [] _ -> true
  [T | Ts] Bound ->
    (and (shenlogic.thf.v2-term-valid? T Bound)
         (shenlogic.thf.v2-terms-valid? Ts Bound))
  _ _ -> false)

(define shenlogic.thf.v2-term-valid?
  [v-var X] Bound -> (shenlogic.thf.v2-bound-has? v-var X Bound)
  [v-int I] Bound -> (shenlogic.thf.v2-int-valid? I Bound)
  v-true _ -> true
  v-false _ -> true
  [v-symbol S] Bound -> (shenlogic.thf.v2-symbol-valid? S Bound)
  [v-string S] Bound -> (shenlogic.thf.v2-string-valid? S Bound)
  [v-ctor _ Args] Bound -> (shenlogic.thf.v2-terms-valid? Args Bound)
  _ _ -> false)

(define shenlogic.thf.v2-symbol-valid?
  [s-var X] Bound -> (shenlogic.thf.v2-bound-has? s-var X Bound)
  [s-lit _] _ -> true
  X _ -> (if (cons? X) false true)
  _ _ -> false)

(define shenlogic.thf.v2-string-valid?
  [s-var X] Bound -> (shenlogic.thf.v2-bound-has? s-var X Bound)
  [s-lit _] _ -> true
  X _ -> (if (cons? X) false true)
  _ _ -> false)

(define shenlogic.thf.v2-int-valid?
  [i-var X] Bound -> (shenlogic.thf.v2-bound-has? i-var X Bound)
  [i-lit N] _ -> (number? N)
  [i-add A B] Bound -> (and (shenlogic.thf.v2-int-valid? A Bound)
                            (shenlogic.thf.v2-int-valid? B Bound))
  [i-sub A B] Bound -> (and (shenlogic.thf.v2-int-valid? A Bound)
                            (shenlogic.thf.v2-int-valid? B Bound))
  [i-mul A B] Bound -> (and (shenlogic.thf.v2-int-valid? A Bound)
                            (shenlogic.thf.v2-int-valid? B Bound))
  _ _ -> false)

(define shenlogic.thf.v2-bound-has?
  _ _ [] -> false
  Tag X [[Tag X] | _] -> true
  Tag X [_ | Bs] -> (shenlogic.thf.v2-bound-has? Tag X Bs))

(define shenlogic.thf.v2-premises-valid?
  [] _ _ -> true
  [[call F Args R] | Ps] Bound Relations ->
    (and (shenlogic.thf.v2-relation-name? F Relations)
      (and (shenlogic.thf.v2-terms-valid? Args Bound)
        (and (shenlogic.thf.v2-term-valid? R Bound)
             (shenlogic.thf.v2-premises-valid? Ps Bound Relations))))
  [[value-eq A B] | Ps] Bound Relations ->
    (and (shenlogic.thf.v2-term-valid? A Bound)
      (and (shenlogic.thf.v2-term-valid? B Bound)
           (shenlogic.thf.v2-premises-valid? Ps Bound Relations)))
  [[value-neq A B] | Ps] Bound Relations ->
    (and (shenlogic.thf.v2-term-valid? A Bound)
      (and (shenlogic.thf.v2-term-valid? B Bound)
           (shenlogic.thf.v2-premises-valid? Ps Bound Relations)))
  [[decompose V _ Fields] | Ps] Bound Relations ->
    (and (shenlogic.thf.v2-term-valid? V Bound)
      (and (shenlogic.thf.v2-terms-valid? Fields Bound)
           (shenlogic.thf.v2-premises-valid? Ps Bound Relations)))
  [[not-tag V _] | Ps] Bound Relations ->
    (and (shenlogic.thf.v2-term-valid? V Bound)
         (shenlogic.thf.v2-premises-valid? Ps Bound Relations))
  [[int-test Op A B] | Ps] Bound Relations ->
    (and (shenlogic.thf.v2-int-op? Op)
      (and (shenlogic.thf.v2-int-valid? A Bound)
        (and (shenlogic.thf.v2-int-valid? B Bound)
             (shenlogic.thf.v2-premises-valid? Ps Bound Relations))))
  _ _ _ -> false)

(define shenlogic.thf.v2-int-op?
  eq -> true
  neq -> true
  lt -> true
  gt -> true
  le -> true
  ge -> true
  _ -> false)

(define shenlogic.thf.v2-relation-name?
  X [] -> false
  X [[relation X _ value] | _] -> true
  X [_ | Rs] -> (shenlogic.thf.v2-relation-name? X Rs))

(define shenlogic.thf.v2-sccs-valid?
  [] _ -> true
  [[scc Names] | Ss] Relations ->
    (and (shenlogic.thf.v2-scc-names-valid? Names Relations)
         (shenlogic.thf.v2-sccs-valid? Ss Relations))
  _ _ -> false)

(define shenlogic.thf.v2-scc-names-valid?
  [] _ -> true
  [N | Ns] Relations ->
    (and (shenlogic.thf.v2-relation-name? N Relations)
         (shenlogic.thf.v2-scc-names-valid? Ns Relations)))

(define shenlogic.thf.v2-namemap-valid?
  [] -> true
  [[_ _] | Ms] -> (shenlogic.thf.v2-namemap-valid? Ms)
  _ -> false)

(define shenlogic.thf.v2-namemap-entries
  [name-map Entries] -> Entries
  Entries -> Entries)

(define shenlogic.thf.v2-known-rules?
  [] _ -> true
  [[rule _ _ _ _ Args _ Premises Result] | Rs] Constructors ->
    (and (shenlogic.thf.v2-known-terms? Args Constructors)
      (and (shenlogic.thf.v2-known-terms? [Result] Constructors)
        (and (shenlogic.thf.v2-known-premises? Premises Constructors)
             (shenlogic.thf.v2-known-rules? Rs Constructors))))
  _ _ -> false)
(define shenlogic.thf.v2-known-terms?
  [] _ -> true
  [[v-ctor Tag Args] | Ts] Constructors ->
    (and (shenlogic.thf.v2-known-tag? Tag Constructors)
      (and (shenlogic.thf.v2-known-terms? Args Constructors)
           (shenlogic.thf.v2-known-terms? Ts Constructors)))
  [T | Ts] Constructors -> (and (shenlogic.thf.v2-known-term? T Constructors)
    (shenlogic.thf.v2-known-terms? Ts Constructors)))
(define shenlogic.thf.v2-known-term?
  [v-int _] _ -> true
  [v-ctor Tag Args] Constructors -> (and (shenlogic.thf.v2-known-tag? Tag Constructors)
    (shenlogic.thf.v2-known-terms? Args Constructors))
  _ _ -> true)
(define shenlogic.thf.v2-known-premises?
  [] _ -> true
  [[decompose V Tag Fields] | Ps] Cs ->
    (and (shenlogic.thf.v2-known-term? V Cs)
      (and (shenlogic.thf.v2-known-tag? Tag Cs)
        (and (shenlogic.thf.v2-known-terms? Fields Cs)
             (shenlogic.thf.v2-known-premises? Ps Cs))))
  [[not-tag V Tag] | Ps] Cs ->
    (and (shenlogic.thf.v2-known-term? V Cs)
      (and (shenlogic.thf.v2-known-tag? Tag Cs)
           (shenlogic.thf.v2-known-premises? Ps Cs)))
  [_ | Ps] Cs -> (shenlogic.thf.v2-known-premises? Ps Cs))
(define shenlogic.thf.v2-known-tag?
  _ [] -> false
  Tag [[constructor Tag _ _] | _] -> true
  Tag [[constructor _ Tag _] | _] -> true
  Tag [_ | Cs] -> (shenlogic.thf.v2-known-tag? Tag Cs))

(define shenlogic.thf.v2-output
  Constructors Relations Rules SCCs NameMap ->
    (let Literals (shenlogic.thf.v2-literals Rules [])
    (@s "% ShenLogic typed value specification" (n->string 10)
      (shenlogic.thf.v2-value-decl)
      (shenlogic.thf.v2-constructor-decls Constructors NameMap)
      (shenlogic.thf.v2-relation-decls Relations NameMap)
      (shenlogic.thf.v2-literal-decls Literals NameMap)
      (shenlogic.thf.v2-literal-distinctness Literals NameMap)
      (shenlogic.thf.v2-constructor-axioms Constructors NameMap)
      (shenlogic.thf.v2-induction Constructors NameMap)
      (shenlogic.thf.v2-rules Rules Constructors NameMap)
      (shenlogic.thf.v2-leastness SCCs Rules Relations Constructors NameMap))))

\\ Literal payloads are first-class individuals in THF.  Every emitted
\\ constant therefore receives a declaration, and unequal payload literals
\\ are axiomatized as unequal.  This keeps the model faithful to Shen's
\\ symbol/string equality rather than relying on accidental model choices.
(define shenlogic.thf.v2-literals
  [] Acc -> (reverse Acc)
  [[rule _ _ _ _ Args _ Premises Result] | Rs] Acc ->
    (let A (shenlogic.thf.v2-literals-terms Args Acc)
      (let B (shenlogic.thf.v2-literals-terms [Result] A)
        (let C (shenlogic.thf.v2-literals-premises Premises B)
          (shenlogic.thf.v2-literals Rs C)))))

(define shenlogic.thf.v2-literals-terms
  [] Acc -> Acc
  [T | Ts] Acc ->
    (shenlogic.thf.v2-literals-terms Ts
      (shenlogic.thf.v2-literals-term T Acc)))

(define shenlogic.thf.v2-literals-term
  [v-symbol S] Acc -> (shenlogic.thf.v2-literal-add symbol S Acc)
  [v-string S] Acc -> (shenlogic.thf.v2-literal-add string S Acc)
  [v-ctor _ Args] Acc -> (shenlogic.thf.v2-literals-terms Args Acc)
  _ Acc -> Acc)

(define shenlogic.thf.v2-literals-premises
  [] Acc -> Acc
  [[call _ Args Result] | Ps] Acc ->
    (shenlogic.thf.v2-literals-premises Ps
      (shenlogic.thf.v2-literals-terms [Result | Args] Acc))
  [[value-eq A B] | Ps] Acc ->
    (shenlogic.thf.v2-literals-premises Ps
      (shenlogic.thf.v2-literals-terms [A B] Acc))
  [[value-neq A B] | Ps] Acc ->
    (shenlogic.thf.v2-literals-premises Ps
      (shenlogic.thf.v2-literals-terms [A B] Acc))
  [[decompose V _ Fields] | Ps] Acc ->
    (shenlogic.thf.v2-literals-premises Ps
      (shenlogic.thf.v2-literals-terms [V | Fields] Acc))
  [[not-tag V _] | Ps] Acc ->
    (shenlogic.thf.v2-literals-premises Ps
      (shenlogic.thf.v2-literals-terms [V] Acc))
  [_ | Ps] Acc -> (shenlogic.thf.v2-literals-premises Ps Acc))

(define shenlogic.thf.v2-literal-add
  Kind S Acc -> (if (element? [Kind S] Acc) Acc (cons [Kind S] Acc)))

(define shenlogic.thf.v2-literal-decls
  [] _ -> ""
  [[Kind S] | Ls] Map ->
    (let Head (@s "sl_" (shenlogic.thf.v2-literal-prefix Kind) "_"
      (shenlogic.thf.v2-safe S))
      (@s "thf(" Head "_type,type," Head ": $i)." (n->string 10)
        (shenlogic.thf.v2-literal-decls Ls Map))))

(define shenlogic.thf.v2-literal-distinctness
  Lits Map -> (shenlogic.thf.v2-literal-distinctness-kinds Lits Map))

(define shenlogic.thf.v2-literal-distinctness-kinds
  [] _ -> ""
  [[Kind S] | Ls] Map ->
    (@s (shenlogic.thf.v2-literal-distinctness-one Kind S Ls Map)
      (shenlogic.thf.v2-literal-distinctness-kinds Ls Map)))

(define shenlogic.thf.v2-literal-distinctness-one
  _ _ [] _ -> ""
  Kind S [[Kind T] | Ls] Map ->
    (let A (@s "sl_" (shenlogic.thf.v2-literal-prefix Kind) "_"
      (shenlogic.thf.v2-safe S))
      (let B (@s "sl_" (shenlogic.thf.v2-literal-prefix Kind) "_"
        (shenlogic.thf.v2-safe T))
        (@s "thf(sl_literal_" (shenlogic.thf.v2-safe Kind) "_"
          (shenlogic.thf.v2-safe S) "_neq_" (shenlogic.thf.v2-safe T)
          ",axiom,(" A " != " B "))." (n->string 10)
          (shenlogic.thf.v2-literal-distinctness-one Kind S Ls Map))))
  Kind S [_ | Ls] Map ->
    (shenlogic.thf.v2-literal-distinctness-one Kind S Ls Map))

(define shenlogic.thf.v2-literal-prefix
  symbol -> "sym"
  string -> "str")

(define shenlogic.thf.v2-value-decl
  -> (@s "thf(sl_value_type,type,value: $tType)." (n->string 10)))

(define shenlogic.thf.v2-all-constructors
  Constructors ->
    (shenlogic.thf.v2-add-builtin
      [constructor int int 1]
      (shenlogic.thf.v2-add-builtin
        [constructor true true 0]
        (shenlogic.thf.v2-add-builtin
          [constructor false false 0]
          (shenlogic.thf.v2-add-builtin
            [constructor symbol symbol 1]
            (shenlogic.thf.v2-add-builtin
              [constructor string string 1]
              (shenlogic.thf.v2-add-builtin
                [constructor nil nil 0]
                (shenlogic.thf.v2-add-builtin
                  [constructor cons cons 2] Constructors))))))))

(define shenlogic.thf.v2-add-builtin
  [constructor Source Target Arity] Cs ->
    (if (shenlogic.thf.v2-has-constructor? Source Target Cs)
        Cs
        [[constructor Source Target Arity] | Cs]))

(define shenlogic.thf.v2-has-constructor?
  _ _ [] -> false
  Source Target [[constructor Source Target _] | _] -> true
  Source Target [[constructor Source _ _] | _] -> true
  Source Target [[constructor _ Target _] | _] -> true
  Source Target [_ | Cs] ->
    (shenlogic.thf.v2-has-constructor? Source Target Cs))

(define shenlogic.thf.v2-constructor-decls
  Constructors Map ->
    (shenlogic.thf.v2-constructor-decls-list
      (shenlogic.thf.v2-all-constructors Constructors) Map))

(define shenlogic.thf.v2-constructor-decls-list
  [] _ -> ""
  [[constructor Source Target Arity] | Cs] Map ->
    (let Head (@s "sl_ctor_" (shenlogic.thf.v2-safe (shenlogic.thf.v2-name Target Map)))
      (@s "thf(" Head "_type,type," Head ": ("
        (shenlogic.thf.v2-ctor-type Source Arity) "))." (n->string 10)
      (shenlogic.thf.v2-constructor-decls-list Cs Map))))

(define shenlogic.thf.v2-ctor-type
  int _ -> "$int > value"
  symbol _ -> "$i > value"
  string _ -> "$i > value"
  _ Arity -> (shenlogic.thf.v2-fun-type Arity "value"))

(define shenlogic.thf.v2-ctor-arg-type
  int -> "$int"
  symbol -> "$i"
  string -> "$i"
  _ -> "value")

(define shenlogic.thf.v2-fun-type
  0 Result -> Result
  N Result -> (@s "value > " (shenlogic.thf.v2-fun-type (- N 1) Result)))

(define shenlogic.thf.v2-relation-decls
  [] _ -> ""
  [[relation Name Sorts value] | Rs] Map ->
    (let Head (@s "sl_rel_" (shenlogic.thf.v2-safe (shenlogic.thf.v2-name Name Map)))
      (@s "thf(" Head "_type,type," Head ": ("
        (shenlogic.thf.v2-fun-type (+ 1 (length Sorts)) "$o") "))."
      (n->string 10) (shenlogic.thf.v2-relation-decls Rs Map))))

(define shenlogic.thf.v2-constructor-axioms
  Constructors Map ->
    (let All (shenlogic.thf.v2-all-constructors Constructors)
      (shenlogic.thf.v2-injectivity All Map
        (shenlogic.thf.v2-disjoint All Map))))

(define shenlogic.thf.v2-injectivity
  [] _ Tail -> Tail
  [[constructor Source Target Arity] | Cs] Map Tail ->
    (@s (shenlogic.thf.v2-injective Source Target Arity Map)
      (shenlogic.thf.v2-injectivity Cs Map Tail)))

(define shenlogic.thf.v2-injective
  _ _ 0 _ -> ""
  Source Target Arity Map ->
    (let L (shenlogic.thf.v2-vars Arity 0 "X")
      (let R (shenlogic.thf.v2-vars Arity 0 "Y")
        (@s "thf(sl_ctor_" (shenlogic.thf.v2-safe (shenlogic.thf.v2-name Target Map)) "_injective,axiom,(! ["
          (shenlogic.thf.v2-typed-binders L (shenlogic.thf.v2-ctor-arg-type Source)) ","
          (shenlogic.thf.v2-typed-binders R (shenlogic.thf.v2-ctor-arg-type Source)) "] : ("
          (shenlogic.thf.v2-eq-term (shenlogic.thf.v2-apply-raw Target L Map)
            (shenlogic.thf.v2-apply-raw Target R Map)) " => "
          (shenlogic.thf.v2-equalities L R) ")))." (n->string 10)))))

(define shenlogic.thf.v2-disjoint
  [] _ -> ""
  [C | Cs] Map ->
    (@s (shenlogic.thf.v2-disjoint-with C Cs Map)
      (shenlogic.thf.v2-disjoint Cs Map)))

(define shenlogic.thf.v2-disjoint-with
  _ [] _ -> ""
  [constructor A TargetA ArityA] [[constructor B TargetB ArityB] | Cs] Map ->
    (@s "thf(sl_ctor_" (shenlogic.thf.v2-safe (shenlogic.thf.v2-name TargetA Map)) "_" (shenlogic.thf.v2-safe (shenlogic.thf.v2-name TargetB Map))
      "_disjoint,axiom,(! [" (shenlogic.thf.v2-disjoint-binders ArityA ArityB
        (shenlogic.thf.v2-ctor-arg-type A) (shenlogic.thf.v2-ctor-arg-type B))
      "] : (" (shenlogic.thf.v2-not-eq-term
        (shenlogic.thf.v2-apply-raw TargetA (shenlogic.thf.v2-vars ArityA 0 "X") Map)
        (shenlogic.thf.v2-apply-raw TargetB (shenlogic.thf.v2-vars ArityB 0 "Y") Map)) ")))." (n->string 10)
      (shenlogic.thf.v2-disjoint-with [constructor A TargetA ArityA] Cs Map))
  _ _ _ -> "")

(define shenlogic.thf.v2-vars
  0 _ _ -> []
  N I Prefix ->
    [(intern (@s Prefix (str I))) |
      (shenlogic.thf.v2-vars (- N 1) (+ I 1) Prefix)])

(define shenlogic.thf.v2-typed-binders
  [] _ -> "Dummy:value"
  [X] Type -> (@s (shenlogic.thf.v2-var X) ":" Type)
  [X | Xs] Type -> (@s (shenlogic.thf.v2-var X) ":" Type ","
    (shenlogic.thf.v2-typed-binders Xs Type)))

(define shenlogic.thf.v2-bound-binders
  [] -> "Dummy:value"
  [[v-var X] | Bs] -> (@s (shenlogic.thf.v2-var X) ":value"
    (shenlogic.thf.v2-v2-comma-bound Bs))
  [[i-var X] | Bs] -> (@s (shenlogic.thf.v2-ivar X) ":$int"
    (shenlogic.thf.v2-v2-comma-bound Bs))
  [[s-var X] | Bs] -> (@s (shenlogic.thf.v2-svar X) ":$i"
    (shenlogic.thf.v2-v2-comma-bound Bs)))

(define shenlogic.thf.v2-v2-comma-bound
  [] -> ""
  [[v-var X] | Bs] -> (@s "," (shenlogic.thf.v2-var X) ":value"
    (shenlogic.thf.v2-v2-comma-bound Bs))
  [[i-var X] | Bs] -> (@s "," (shenlogic.thf.v2-ivar X) ":$int"
    (shenlogic.thf.v2-v2-comma-bound Bs))
  [[s-var X] | Bs] -> (@s "," (shenlogic.thf.v2-svar X) ":$i"
    (shenlogic.thf.v2-v2-comma-bound Bs)))

(define shenlogic.thf.v2-var
  X -> (@s "V_" (shenlogic.thf.v2-safe X)))
(define shenlogic.thf.v2-ivar
  X -> (@s "I_" (shenlogic.thf.v2-safe X)))
(define shenlogic.thf.v2-svar
  X -> (@s "S_" (shenlogic.thf.v2-safe X)))

(define shenlogic.thf.v2-term
  [v-var X] _ _ -> (shenlogic.thf.v2-var X)
  [v-int I] Bound Map -> (@s "(sl_ctor_int @ " (shenlogic.thf.v2-int I Bound Map) ")")
  v-true _ _ -> "sl_ctor_true"
  v-false _ _ -> "sl_ctor_false"
  [v-symbol S] Bound Map -> (@s "(sl_ctor_symbol @ "
    (shenlogic.thf.v2-symbol S Bound Map) ")")
  [v-string S] Bound Map -> (@s "(sl_ctor_string @ "
    (shenlogic.thf.v2-string S Bound Map) ")")
  [v-ctor Tag Args] Bound Map ->
    (shenlogic.thf.v2-apply Tag Args Bound Map)
  X _ _ -> (shenlogic.thf.v2-var X))

(define shenlogic.thf.v2-int
  [i-var X] _ _ -> (shenlogic.thf.v2-ivar X)
  [i-lit N] _ _ -> (str N)
  [i-add A B] Bound Map -> (@s "$sum(" (shenlogic.thf.v2-int A Bound Map) ","
    (shenlogic.thf.v2-int B Bound Map) ")")
  [i-sub A B] Bound Map -> (@s "$difference(" (shenlogic.thf.v2-int A Bound Map) ","
    (shenlogic.thf.v2-int B Bound Map) ")")
  [i-mul A B] Bound Map -> (@s "$product(" (shenlogic.thf.v2-int A Bound Map) ","
    (shenlogic.thf.v2-int B Bound Map) ")"))

(define shenlogic.thf.v2-symbol
  [s-var X] _ _ -> (shenlogic.thf.v2-svar X)
  [s-lit S] _ _ -> (@s "sl_sym_" (shenlogic.thf.v2-safe S))
  S _ _ -> (@s "sl_sym_" (shenlogic.thf.v2-safe S)))

(define shenlogic.thf.v2-string
  [s-var X] _ _ -> (shenlogic.thf.v2-svar X)
  [s-lit S] _ _ -> (@s "sl_str_" (shenlogic.thf.v2-safe S))
  S _ _ -> (@s "sl_str_" (shenlogic.thf.v2-safe S)))

(define shenlogic.thf.v2-apply
  Tag Args Bound Map ->
    (let Head (shenlogic.thf.v2-ctor-head Tag Map)
      (shenlogic.thf.v2-apply-args Head Args Bound Map)))

(define shenlogic.thf.v2-apply-raw
  Tag Args Map ->
    (let Head (shenlogic.thf.v2-ctor-head Tag Map)
      (shenlogic.thf.v2-apply-raw-args Head Args)))
(define shenlogic.thf.v2-apply-raw-args
  Head [] -> Head
  Head [A | As] -> (@s "(" Head " @ " (shenlogic.thf.v2-var A)
    (shenlogic.thf.v2-apply-raw-tail As) ")"))
(define shenlogic.thf.v2-apply-raw-tail
  [] -> ""
  [A | As] -> (@s " @ " (shenlogic.thf.v2-var A)
    (shenlogic.thf.v2-apply-raw-tail As)))

(define shenlogic.thf.v2-apply-args
  Head [] _ _ -> Head
  Head [A | As] Bound Map ->
    (@s "(" Head " @ " (shenlogic.thf.v2-term A Bound Map)
      (shenlogic.thf.v2-apply-args-tail As Bound Map) ")"))

(define shenlogic.thf.v2-apply-args-tail
  [] _ _ -> ""
  [A | As] Bound Map -> (@s " @ " (shenlogic.thf.v2-term A Bound Map)
    (shenlogic.thf.v2-apply-args-tail As Bound Map)))

(define shenlogic.thf.v2-ctor-head
  Tag Map -> (@s "sl_ctor_" (shenlogic.thf.v2-safe
    (shenlogic.thf.v2-name Tag Map))))

(define shenlogic.thf.v2-eq-term
  A B -> (@s "(" A " = " B ")"))
(define shenlogic.thf.v2-not-eq-term
  A B -> (@s "(" A " != " B ")"))

(define shenlogic.thf.v2-equalities
  [] _ -> "$true"
  [X] [Y] -> (shenlogic.thf.v2-eq-term (shenlogic.thf.v2-var X)
    (shenlogic.thf.v2-var Y))
  [X | Xs] [Y | Ys] -> (@s "(" (shenlogic.thf.v2-eq-term
    (shenlogic.thf.v2-var X) (shenlogic.thf.v2-var Y)) " & "
    (shenlogic.thf.v2-equalities Xs Ys) ")")
  _ _ -> "$false")

(define shenlogic.thf.v2-name
  X Map ->
    (let Found (shenlogic.thf.v2-name-find X Map)
      (if (= Found not-found) X Found)))

(define shenlogic.thf.v2-name-find
  _ [] -> not-found
  X [[X Y] | _] -> Y
  X [_ | Ms] -> (shenlogic.thf.v2-name-find X Ms))

(define shenlogic.thf.v2-safe
  X -> (if (string? X)
          (shenlogic.thf.clean
            (shenlogic.thf.drop-final-quote (tlstr (str X))))
          (shenlogic.thf.clean (str X))))

(define shenlogic.thf.drop-final-quote
  "" -> ""
  S -> (let T (tlstr S)
         (if (= T "") ""
             (cn (pos S 0) (shenlogic.thf.drop-final-quote T)))))

(define shenlogic.thf.v2-disjoint-binders
  0 0 _ _ -> "Dummy:value"
  A B TypeA TypeB -> (@s (shenlogic.thf.v2-disjoint-binders-1 A "X" TypeA)
    (if (= B 0) ""
      (if (= A 0) (shenlogic.thf.v2-disjoint-binders-1 B "Y" TypeB)
        (@s "," (shenlogic.thf.v2-disjoint-binders-1 B "Y" TypeB))))))
(define shenlogic.thf.v2-disjoint-binders-1
  0 _ _ -> ""
  N Prefix Type -> (@s (shenlogic.thf.v2-var (intern (@s Prefix (str (- N 1))))) ":" Type
    (if (= N 1) "" (@s "," (shenlogic.thf.v2-disjoint-binders-1 (- N 1) Prefix Type)))))

(define shenlogic.thf.v2-rules
  [] _ _ -> ""
  [R | Rs] Constructors Map ->
    (@s (shenlogic.thf.v2-rule R Constructors Map)
      (shenlogic.thf.v2-rules Rs Constructors Map)))

(define shenlogic.thf.v2-rule
  [rule Id Function Clause Path Args Bound Premises Result] Constructors Map ->
    (@s "thf(sl_rule_" (shenlogic.thf.v2-safe Id) ",axiom,(! ["
      (shenlogic.thf.v2-bound-binders Bound) "] : ("
      (shenlogic.thf.v2-implication
        (shenlogic.thf.v2-premises Premises Bound Constructors Map [])
        (shenlogic.thf.v2-call Function Args Result Bound Map [])) ")))." (n->string 10)))

(define shenlogic.thf.v2-implication
  "$true" Q -> Q
  P Q -> (@s "(" P " => " Q ")"))

(define shenlogic.thf.v2-premises
  [] _ _ _ _ -> "$true"
  [P] Bound Constructors Map Overrides ->
    (shenlogic.thf.v2-premise P Bound Constructors Map Overrides)
  [P | Ps] Bound Constructors Map Overrides ->
    (@s "(" (shenlogic.thf.v2-premise P Bound Constructors Map Overrides)
      " & " (shenlogic.thf.v2-premises Ps Bound Constructors Map Overrides) ")"))

(define shenlogic.thf.v2-premise
  [call F Args R] Bound Constructors Map Overrides ->
    (shenlogic.thf.v2-call F Args R Bound Map Overrides)
  [value-eq A B] Bound _ Map _ -> (shenlogic.thf.v2-eq-term
    (shenlogic.thf.v2-term A Bound Map) (shenlogic.thf.v2-term B Bound Map))
  [value-neq A B] Bound _ Map _ -> (shenlogic.thf.v2-not-eq-term
    (shenlogic.thf.v2-term A Bound Map) (shenlogic.thf.v2-term B Bound Map))
  [decompose V Tag Fields] Bound _ Map _ -> (shenlogic.thf.v2-eq-term
    (shenlogic.thf.v2-term V Bound Map)
    (shenlogic.thf.v2-apply Tag Fields Bound Map))
  [not-tag V Tag] Bound Constructors Map _ ->
    (let Arity (shenlogic.thf.v2-constructor-arity Tag Constructors)
      (@s "~(? [" (shenlogic.thf.v2-raw-binders Arity 0) "] : ("
        (shenlogic.thf.v2-eq-term (shenlogic.thf.v2-term V Bound Map)
          (shenlogic.thf.v2-apply-raw Tag (shenlogic.thf.v2-vars Arity 0 "N") Map))
        "))"))
  [int-test Op A B] Bound _ Map _ ->
    (shenlogic.thf.v2-int-test Op (shenlogic.thf.v2-int A Bound Map)
      (shenlogic.thf.v2-int B Bound Map)))

(define shenlogic.thf.v2-call
  F Args Result Bound Map Overrides ->
    (let Head (shenlogic.thf.v2-relation-head F Map Overrides)
      (@s "(" Head (shenlogic.thf.v2-call-args Args Result Bound Map) ")")))

\\ Append a closed conjecture to a rendered v2 artifact.  Keeping this next
\\ to v2-call ensures relation/constructor names use the same safe renderer
\\ as axioms and rules.
(define shenlogic.thf.query-fact
  Artifact Relation Args Expected NameMap ->
    (@s Artifact (n->string 10)
        "thf(shenlogic_query,conjecture,"
        (shenlogic.thf.v2-call Relation Args Expected [] NameMap []) ")."
        (n->string 10)))
(define shenlogic.thf.v2-call-args
  [] Result Bound Map -> (@s " @ " (shenlogic.thf.v2-term Result Bound Map))
  [A | As] Result Bound Map -> (@s " @ " (shenlogic.thf.v2-term A Bound Map)
    (shenlogic.thf.v2-call-args As Result Bound Map)))
(define shenlogic.thf.v2-relation-head
  F Map Overrides ->
    (let C (shenlogic.thf.v2-name-find F Overrides)
      (if (= C not-found)
          (@s "sl_rel_" (shenlogic.thf.v2-safe (shenlogic.thf.v2-name F Map)))
          C)))

(define shenlogic.thf.v2-int-test
  eq A B -> (shenlogic.thf.v2-eq-term A B)
  neq A B -> (shenlogic.thf.v2-not-eq-term A B)
  lt A B -> (@s "$less(" A "," B ")")
  gt A B -> (@s "$greater(" A "," B ")")
  le A B -> (@s "$lesseq(" A "," B ")")
  ge A B -> (@s "$greatereq(" A "," B ")"))

(define shenlogic.thf.v2-constructor-arity
  Tag [[constructor Tag _ Arity] | _] -> Arity
  Tag [[constructor _ Tag Arity] | _] -> Arity
  Tag [_ | Cs] -> (shenlogic.thf.v2-constructor-arity Tag Cs)
  _ _ -> 0)

(define shenlogic.thf.v2-raw-binders
  0 _ -> "Dummy:value"
  N I -> (@s (shenlogic.thf.v2-var (intern (@s "N" (str I)))) ":value"
    (if (= N 1) "" (@s "," (shenlogic.thf.v2-raw-binders (- N 1) (+ I 1))))))

(define shenlogic.thf.v2-induction
  Constructors Map ->
    (@s "thf(sl_value_induction,axiom,(! [P:(value > $o)] : (("
      (shenlogic.thf.v2-induction-closure
        (shenlogic.thf.v2-all-constructors Constructors) Map "P") ") => (! [X:value] : (P @ X)))))." (n->string 10)))

(define shenlogic.thf.v2-induction-closure
  [] _ _ -> "$true"
  [[constructor Source Target Arity] | Cs] Map P ->
    (@s "(" (shenlogic.thf.v2-induction-one Source Target Arity Map P) " & "
      (shenlogic.thf.v2-induction-closure Cs Map P) ")"))

(define shenlogic.thf.v2-induction-one
  _ Target 0 Map P -> (@s "P @ " (shenlogic.thf.v2-ctor-head Target Map))
  int Target Arity Map P ->
    (shenlogic.thf.v2-induction-scalar Target Arity "$int" Map P)
  symbol Target Arity Map P ->
    (shenlogic.thf.v2-induction-scalar Target Arity "$i" Map P)
  string Target Arity Map P ->
    (shenlogic.thf.v2-induction-scalar Target Arity "$i" Map P)
  Source Target Arity Map P ->
    (let Args (shenlogic.thf.v2-vars Arity 0 "A")
      (@s "(! [" (shenlogic.thf.v2-typed-binders Args (shenlogic.thf.v2-ctor-arg-type Source)) "] : ("
        (shenlogic.thf.v2-pred-args Args) " => (P @ "
        (shenlogic.thf.v2-apply-raw Target Args Map) ")))")))

(define shenlogic.thf.v2-induction-scalar
  Target Arity Type Map P ->
    (let Args (shenlogic.thf.v2-vars Arity 0 "A")
      (@s "(! [" (shenlogic.thf.v2-typed-binders Args Type) "] : (P @ "
        (shenlogic.thf.v2-apply-raw Target Args Map) "))")))

(define shenlogic.thf.v2-pred-args
  [] -> "$true"
  [A] -> (@s "(P @ " (shenlogic.thf.v2-var A) ")")
  [A | As] -> (@s "((P @ " (shenlogic.thf.v2-var A) ") & "
    (shenlogic.thf.v2-pred-args As) ")"))

(define shenlogic.thf.v2-leastness
  [] _ _ _ _ -> ""
  [[scc Names] | Ss] Rules Relations Constructors Map ->
    (let Overrides (shenlogic.thf.v2-candidates Names Map)
      (@s "thf(sl_least_" (shenlogic.thf.v2-join Names Map)
        ",axiom,(! [" (shenlogic.thf.v2-candidate-binders Names Relations Map)
        "] : (" (shenlogic.thf.v2-implication
          (shenlogic.thf.v2-scc-closures Names Rules Constructors Map Overrides)
          (shenlogic.thf.v2-containments Names Relations Map Overrides))
        ")))." (n->string 10) (shenlogic.thf.v2-leastness Ss Rules Relations Constructors Map))))

(define shenlogic.thf.v2-candidates
  [] _ -> []
  [N | Ns] Map -> (cons [N (@s "R_" (shenlogic.thf.v2-safe
    (shenlogic.thf.v2-name N Map)))] (shenlogic.thf.v2-candidates Ns Map)))

(define shenlogic.thf.v2-candidate-binders
  [] _ _ -> "Dummy:(value > $o)"
  [N] Relations Map -> (@s (shenlogic.thf.v2-candidate N Map) ":("
    (shenlogic.thf.v2-rel-type N Relations) ")")
  [N | Ns] Relations Map -> (@s (shenlogic.thf.v2-candidate N Map) ":("
    (shenlogic.thf.v2-rel-type N Relations) "),"
    (shenlogic.thf.v2-candidate-binders Ns Relations Map)))

(define shenlogic.thf.v2-candidate
  N Map -> (@s "R_" (shenlogic.thf.v2-safe (shenlogic.thf.v2-name N Map))))

(define shenlogic.thf.v2-rel-type
  N [[relation N Sorts value] | _] -> (shenlogic.thf.v2-fun-type (+ 1 (length Sorts)) "$o")
  N [_ | Rs] -> (shenlogic.thf.v2-rel-type N Rs)
  _ _ -> "$o")

(define shenlogic.thf.v2-scc-closures
  Names Rules Constructors Map Overrides ->
    (let Selected (shenlogic.thf.v2-select-rules Names Rules)
      (shenlogic.thf.v2-rule-formulas Selected Constructors Map Overrides)))
(define shenlogic.thf.v2-select-rules
  _ [] -> []
  Names [R | Rs] ->
    (if (shenlogic.thf.v2-rule-in-names? R Names)
        [R | (shenlogic.thf.v2-select-rules Names Rs)]
        (shenlogic.thf.v2-select-rules Names Rs)))
(define shenlogic.thf.v2-rule-in-names?
  [rule _ F _ _ _ _ _ _] Names -> (element? F Names)
  _ _ -> false)

(define shenlogic.thf.v2-rule-formulas
  [] _ _ _ -> "$true"
  [R] Constructors Map Overrides -> (shenlogic.thf.v2-rule-candidate R Constructors Map Overrides)
  [R | Rs] Constructors Map Overrides -> (@s "(" (shenlogic.thf.v2-rule-candidate R Constructors Map Overrides)
    " & " (shenlogic.thf.v2-rule-formulas Rs Constructors Map Overrides) ")"))

(define shenlogic.thf.v2-rule-candidate
  [rule Id Function Clause Path Args Bound Premises Result] Constructors Map Overrides ->
    (@s "(! [" (shenlogic.thf.v2-bound-binders Bound) "] : ("
      (shenlogic.thf.v2-implication
        (shenlogic.thf.v2-premises Premises Bound Constructors Map Overrides)
        (shenlogic.thf.v2-call Function Args Result Bound Map Overrides)) "))"))

(define shenlogic.thf.v2-containments
  [] _ _ _ -> "$true"
  [N] Relations Map Overrides -> (shenlogic.thf.v2-containment N Relations Map Overrides)
  [N | Ns] Relations Map Overrides -> (@s "(" (shenlogic.thf.v2-containment N Relations Map Overrides)
    " & " (shenlogic.thf.v2-containments Ns Relations Map Overrides) ")"))

(define shenlogic.thf.v2-containment
  N Relations Map Overrides ->
    (let Arity (- (shenlogic.thf.v2-rel-arity N Relations) 1)
      (let Args (shenlogic.thf.v2-vars Arity 0 "A")
        (let All (append Args [(intern "Result")])
          (@s "(! [" (shenlogic.thf.v2-typed-binders All "value") "] : ("
            (shenlogic.thf.v2-implication
              (shenlogic.thf.v2-call N Args (intern "Result") All Map [])
              (shenlogic.thf.v2-call N Args (intern "Result") All Map Overrides)) "))")))))

(define shenlogic.thf.v2-rel-arity
  N [[relation N Sorts value] | _] -> (+ 1 (length Sorts))
  N [_ | Rs] -> (shenlogic.thf.v2-rel-arity N Rs)
  _ _ -> 1)

(define shenlogic.thf.v2-join
  [N] Map -> (shenlogic.thf.v2-safe (shenlogic.thf.v2-name N Map))
  [N | Ns] Map -> (@s (shenlogic.thf.v2-safe (shenlogic.thf.v2-name N Map)) "_"
    (shenlogic.thf.v2-join Ns Map)))
