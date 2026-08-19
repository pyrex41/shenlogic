\\ SMT-LIB2 constrained Horn clause backend.

(define shenlogic.chc.render
  [theory [value-signature Constructors] Relations Rules SCCs NameMap] Profile ->
    (if (element? Profile [linear nonlinear])
        (if (shenlogic.chc.v2-supported? Constructors Relations Rules SCCs NameMap)
            [ok (shenlogic.chc.v2-artifact Constructors Relations Rules SCCs NameMap)]
            [error unsupported-chc-v2])
        [error invalid-profile Profile])
  [theory Declarations Rules SCCs] Profile ->
    (if (element? Profile [linear nonlinear])
        (if (shenlogic.chc.supported? Rules)
            [ok (@s "(set-logic HORN)" (n->string 10)
                    (shenlogic.chc.declarations Declarations)
                    (shenlogic.chc.variables Rules [])
                    (shenlogic.chc.rules Rules)
                    "(check-sat)" (n->string 10))]
            [error unsupported-chc])
        [error invalid-profile Profile])
  _ _ -> [error invalid-theory])

(define shenlogic.chc.declarations
  [] -> ""
  [[relation Name Sorts Result] | Ds] ->
    (@s "(declare-rel " (shenlogic.chc.symbol Name) " ("
        (shenlogic.chc.types (+ 1 (length Sorts))) "))" (n->string 10)
        (shenlogic.chc.declarations Ds)))

(define shenlogic.chc.types
  0 -> ""
  1 -> "Int"
  N -> (@s "Int " (shenlogic.chc.types (- N 1))))

(define shenlogic.chc.variables
  [] Seen -> ""
  [[rule _ _ _ Bound _ _] | Rs] Seen ->
    (let Fresh (shenlogic.chc.minus Bound Seen)
      (@s (shenlogic.chc.declare-vars Fresh)
          (shenlogic.chc.variables Rs (append Fresh Seen)))))

(define shenlogic.chc.declare-vars
  [] -> ""
  [X | Xs] -> (@s "(declare-var " (shenlogic.chc.symbol X) " Int)"
                  (n->string 10) (shenlogic.chc.declare-vars Xs)))

(define shenlogic.chc.rules
  [] -> ""
  [R | Rs] -> (@s (shenlogic.chc.rule R) (shenlogic.chc.rules Rs)))

(define shenlogic.chc.rule
  [rule _ Function Args _ Premises Result] ->
    (@s "(rule (=> " (shenlogic.chc.body Premises) " ("
        (shenlogic.chc.symbol Function) " "
        (shenlogic.chc.exprs (append Args [Result])) ")))" (n->string 10))
  _ -> "")

(define shenlogic.chc.body
  [] -> "true"
  [P] -> (shenlogic.chc.premise P)
  Ps -> (@s "(and " (shenlogic.chc.premises Ps) ")"))

(define shenlogic.chc.premises
  [] -> ""
  [P] -> (shenlogic.chc.premise P)
  [P | Ps] -> (@s (shenlogic.chc.premise P) " "
                   (shenlogic.chc.premises Ps)))

(define shenlogic.chc.premise
  [call Name Args Result] ->
    (@s "(" (shenlogic.chc.symbol Name) " "
        (shenlogic.chc.exprs (append Args [Result])) ")")
  [constraint E] -> (shenlogic.chc.expr E)
  [= A B] -> (@s "(= " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [!= A B] -> (@s "(not (= " (shenlogic.chc.expr A) " "
                 (shenlogic.chc.expr B) "))")
  X -> (shenlogic.chc.expr X))

(define shenlogic.chc.expr
  true -> "true"
  false -> "false"
  [add A B] -> (@s "(+ " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [sub A B] -> (@s "(- " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [mul A B] -> (@s "(* " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [eq A B] -> (@s "(= " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [lt A B] -> (@s "(< " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [gt A B] -> (@s "(> " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [le A B] -> (@s "(<= " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [ge A B] -> (@s "(>= " (shenlogic.chc.expr A) " " (shenlogic.chc.expr B) ")")
  [not A] -> (@s "(not " (shenlogic.chc.expr A) ")")
  X -> (if (number? X) (str X) (shenlogic.chc.symbol X)))

(define shenlogic.chc.exprs
  [] -> ""
  [X] -> (shenlogic.chc.expr X)
  [X | Xs] -> (@s (shenlogic.chc.expr X) " " (shenlogic.chc.exprs Xs)))

(define shenlogic.chc.supported?
  [] -> true
  [[rule _ _ _ Bound Premises Result] | Rs] ->
    (and (shenlogic.chc.term-supported? Result Bound)
         (shenlogic.chc.premises-supported? Premises Bound)
         (shenlogic.chc.supported? Rs)))

(define shenlogic.chc.premises-supported?
  [] _ -> true
  [[match _ _] | _] _ -> false
  [[not-applicable | _] | _] _ -> false
  [[call _ Args Result] | Ps] Bound ->
    (and (shenlogic.chc.terms-supported? (append Args [Result]) Bound)
         (shenlogic.chc.premises-supported? Ps Bound))
  [[constraint E] | Ps] Bound ->
    (and (shenlogic.chc.formula-supported? E Bound)
         (shenlogic.chc.premises-supported? Ps Bound))
  [[= A B] | Ps] Bound ->
    (and (shenlogic.chc.term-supported? A Bound)
         (and (shenlogic.chc.term-supported? B Bound)
              (shenlogic.chc.premises-supported? Ps Bound)))
  [[!= A B] | Ps] Bound ->
    (and (shenlogic.chc.term-supported? A Bound)
         (and (shenlogic.chc.term-supported? B Bound)
              (shenlogic.chc.premises-supported? Ps Bound)))
  [_ | _] _ -> false)

(define shenlogic.chc.terms-supported?
  [] _ -> true
  [X | Xs] Bound ->
    (and (shenlogic.chc.term-supported? X Bound)
         (shenlogic.chc.terms-supported? Xs Bound)))

(define shenlogic.chc.term-supported?
  X Bound ->
    (if (number? X)
        true
        (if (element? X Bound)
            true
            (if (cons? X)
                (shenlogic.chc.compound-term-supported? X Bound)
                false))))

(define shenlogic.chc.compound-term-supported?
  [add A B] Bound -> (shenlogic.chc.terms-supported? [A B] Bound)
  [sub A B] Bound -> (shenlogic.chc.terms-supported? [A B] Bound)
  [mul A B] Bound -> (shenlogic.chc.terms-supported? [A B] Bound)
  [ite C T F] Bound ->
    (and (shenlogic.chc.formula-supported? C Bound)
         (shenlogic.chc.terms-supported? [T F] Bound))
  _ _ -> false)

(define shenlogic.chc.formula-supported?
  true _ -> true
  false _ -> true
  [eq A B] Bound -> (shenlogic.chc.terms-supported? [A B] Bound)
  [lt A B] Bound -> (shenlogic.chc.terms-supported? [A B] Bound)
  [gt A B] Bound -> (shenlogic.chc.terms-supported? [A B] Bound)
  [le A B] Bound -> (shenlogic.chc.terms-supported? [A B] Bound)
  [ge A B] Bound -> (shenlogic.chc.terms-supported? [A B] Bound)
  [not A] Bound -> (shenlogic.chc.formula-supported? A Bound)
  _ _ -> false)

(define shenlogic.chc.minus
  [] _ -> []
  [X | Xs] Seen -> (if (element? X Seen) (shenlogic.chc.minus Xs Seen)
                       [X | (shenlogic.chc.minus Xs Seen)]))

(define shenlogic.chc.symbol
  X -> (str X))

\\ Value-Horn (v2) backend.  The v2 path is intentionally separate from the
\\ old integer-only renderer above: this keeps old clients readable while the
\\ new renderer consumes the tagged, closed Value IR.

(define shenlogic.chc.v2-artifact
  Constructors Relations Rules SCCs NameMap ->
    (@s "; Horn fixedpoint rules over boxed Value; ALL required by Z3 String/datatype combination"
        (n->string 10) "(set-logic ALL)" (n->string 10)
        (shenlogic.chc.v2-datatype Constructors)
        (shenlogic.chc.v2-relations Relations NameMap)
        (shenlogic.chc.v2-variables Rules [])
        (shenlogic.chc.v2-rules Rules Relations Constructors NameMap)
        "(check-sat)" (n->string 10)))

\\ Query helpers intentionally remain separate from the base artifact: callers
\\ can ask Z3 for a relation derivability result without changing its rules.
(define shenlogic.chc.v2-query
  Name -> (@s "(query " (shenlogic.chc.v2-name Name) ")"))

(define shenlogic.chc.query
  Artifact Name -> (@s Artifact (n->string 10) (shenlogic.chc.v2-query Name)))

(define shenlogic.chc.v2-datatype
  Constructors ->
    (@s "(declare-datatypes () ((Value "
        (shenlogic.chc.v2-constructors Constructors)
        ")))" (n->string 10)))

(define shenlogic.chc.v2-constructors
  Constructors ->
    (@s "(VInt (VInt_value Int)) VTrue VFalse "
        "(VSymbol (VSymbol_value String)) "
        "(VString (VString_value String)) VNil "
        "(VCons (VCons_head Value) (VCons_tail Value))"
        (shenlogic.chc.v2-user-constructors Constructors)))

(define shenlogic.chc.v2-user-constructors
  [] -> ""
  [[constructor int _ _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor true _ _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor false _ _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor symbol _ _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor string _ _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor nil _ _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor cons _ _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor int _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor true _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor false _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor symbol _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor string _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor nil _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor cons _] | Cs] -> (shenlogic.chc.v2-user-constructors Cs)
  [[constructor _ Target Arity] | Cs] ->
    (@s " " (shenlogic.chc.v2-ctor-decl Target Arity)
        (shenlogic.chc.v2-user-constructors Cs))
  [[constructor Target Arity] | Cs] ->
    (@s " " (shenlogic.chc.v2-ctor-decl Target Arity)
        (shenlogic.chc.v2-user-constructors Cs)))

(define shenlogic.chc.v2-ctor-decl
  Target 0 -> (shenlogic.chc.v2-name Target)
  Target Arity ->
    (@s "(" (shenlogic.chc.v2-name Target) " "
        (shenlogic.chc.v2-ctor-fields Target Arity 0) ")"))

(define shenlogic.chc.v2-ctor-fields
  _ 0 _ -> ""
  Target N I ->
    (if (= I 0)
        (@s "(" (shenlogic.chc.v2-accessor Target I) " Value) "
            (shenlogic.chc.v2-ctor-fields Target (- N 1) (+ I 1)))
        (@s "(" (shenlogic.chc.v2-accessor Target I) " Value) "
            (shenlogic.chc.v2-ctor-fields Target (- N 1) (+ I 1)))))

(define shenlogic.chc.v2-relations
  [] _ -> ""
  [[relation Name Sorts Result] | Rs] NameMap ->
    (@s "(declare-rel " (shenlogic.chc.v2-relation-name Name NameMap)
        " (" (shenlogic.chc.v2-sort-slots Sorts Result) "))"
        (n->string 10)
        (shenlogic.chc.v2-relations Rs NameMap)))

(define shenlogic.chc.v2-sort-slots
  [] Result -> (shenlogic.chc.v2-sort Result)
  [S | Ss] Result ->
    (@s (shenlogic.chc.v2-sort S) " "
        (shenlogic.chc.v2-sort-slots Ss Result)))

(define shenlogic.chc.v2-sort
  value -> "Value"
  _ -> "Value")

(define shenlogic.chc.v2-rules
  [] _ _ _ -> ""
  [[rule Id Function Clause Path Args Bound Premises Result] | Rs]
    Relations Constructors NameMap ->
    (@s "(rule (=> "
        (shenlogic.chc.v2-body Premises Relations Constructors Bound NameMap)
        " (" (shenlogic.chc.v2-relation-name Function NameMap) " "
        (shenlogic.chc.v2-values (append Args [Result]) Relations Constructors Bound NameMap)
        ")))" (n->string 10)
        (shenlogic.chc.v2-rules Rs Relations Constructors NameMap))
  [_ | Rs] Relations Constructors NameMap ->
    (shenlogic.chc.v2-rules Rs Relations Constructors NameMap))

(define shenlogic.chc.v2-body
  [] _ _ _ _ -> "true"
  [P] Relations Constructors Bound NameMap ->
    (shenlogic.chc.v2-premise P Relations Constructors Bound NameMap)
  Ps Relations Constructors Bound NameMap ->
    (@s "(and " (shenlogic.chc.v2-premises Ps Relations Constructors Bound NameMap) ")"))

(define shenlogic.chc.v2-premises
  [] _ _ _ _ -> ""
  [P] Relations Constructors Bound NameMap ->
    (shenlogic.chc.v2-premise P Relations Constructors Bound NameMap)
  [P | Ps] Relations Constructors Bound NameMap ->
    (@s (shenlogic.chc.v2-premise P Relations Constructors Bound NameMap) " "
        (shenlogic.chc.v2-premises Ps Relations Constructors Bound NameMap)))

(define shenlogic.chc.v2-premise
  [call F Args Result] Relations Constructors Bound NameMap ->
    (@s "(" (shenlogic.chc.v2-relation-name F NameMap) " "
        (shenlogic.chc.v2-values (append Args [Result]) Relations Constructors [] NameMap) ")")
  [value-eq A B] _ Constructors _ _ ->
    (@s "(= " (shenlogic.chc.v2-value A Constructors []) " "
        (shenlogic.chc.v2-value B Constructors []) ")")
  [value-neq A B] _ Constructors _ _ ->
    (@s "(not (= " (shenlogic.chc.v2-value A Constructors []) " "
        (shenlogic.chc.v2-value B Constructors []) "))")
  [decompose V Tag Fields] _ Constructors _ _ ->
    (shenlogic.chc.v2-decompose V Tag Fields Constructors)
  [not-tag V Tag] _ Constructors _ _ ->
    (@s "(not ((_ is " (shenlogic.chc.v2-ctor-symbol Tag Constructors) ") "
        (shenlogic.chc.v2-value V Constructors []) "))")
  [int-test Op A B] _ Constructors _ _ ->
    (@s "(" (shenlogic.chc.v2-op Op) " "
        (shenlogic.chc.v2-int A) " " (shenlogic.chc.v2-int B) ")")
  _ _ _ _ _ -> "false")

(define shenlogic.chc.v2-decompose
  V Tag Fields Constructors ->
    (@s "(and ((_ is " (shenlogic.chc.v2-ctor-symbol Tag Constructors) ") "
        (shenlogic.chc.v2-value V Constructors []) ") "
        (shenlogic.chc.v2-decompose-fields Tag V Fields Constructors 0) ")"))

(define shenlogic.chc.v2-decompose-fields
  _ _ [] _ _ -> "true"
  Tag V [F | Fs] Constructors I ->
    (if (= Fs [])
        (@s "(= (" (shenlogic.chc.v2-accessor-for Tag I Constructors) " "
            (shenlogic.chc.v2-value V Constructors []) ") "
            (shenlogic.chc.v2-value F Constructors []) ")")
        (@s "(and (= (" (shenlogic.chc.v2-accessor-for Tag I Constructors) " "
            (shenlogic.chc.v2-value V Constructors []) ") "
            (shenlogic.chc.v2-value F Constructors []) ") "
            (shenlogic.chc.v2-decompose-fields Tag V Fs Constructors (+ I 1)) ")")))

\\ Decomposition fields are values; equations are emitted separately so that
\\ constructor accessors remain ordinary SMT terms.  This helper is retained
\\ for malformed-field recovery and is overridden by the relation below.
(define shenlogic.chc.v2-decompose-value
  X -> X)

(define shenlogic.chc.v2-values
  [] _ _ _ _ -> ""
  [X] _ Constructors _ _ -> (shenlogic.chc.v2-value X Constructors [])
  [X | Xs] Relations Constructors Bound NameMap ->
    (@s (shenlogic.chc.v2-value X Constructors Bound) " "
        (shenlogic.chc.v2-values Xs Relations Constructors Bound NameMap)))

(define shenlogic.chc.v2-value
  [v-var X] _ _ -> (shenlogic.chc.v2-var "v" X)
  [v-int X] _ _ -> (@s "(VInt " (shenlogic.chc.v2-int X) ")")
  v-true _ _ -> "VTrue"
  v-false _ _ -> "VFalse"
  [v-symbol X] _ _ -> (@s "(VSymbol " (shenlogic.chc.v2-string X) ")")
  [v-string X] _ _ -> (@s "(VString " (shenlogic.chc.v2-string X) ")")
  v-nil _ _ -> "VNil"
  [v-cons H T] Constructors _ ->
    (@s "(VCons " (shenlogic.chc.v2-value H Constructors []) " "
        (shenlogic.chc.v2-value T Constructors []) ")")
  [v-ctor Tag Args] Constructors _ ->
    (if (= Args [])
        (shenlogic.chc.v2-ctor-symbol Tag Constructors)
        (@s "(" (shenlogic.chc.v2-ctor-symbol Tag Constructors) " "
            (shenlogic.chc.v2-values Args [] Constructors [] []) ")"))
  _ _ _ -> "VNil")

(define shenlogic.chc.v2-int
  [i-var X] -> (shenlogic.chc.v2-var "i" X)
  [i-lit X] -> (if (number? X) (str X) "0")
  [i-add A B] -> (@s "(+ " (shenlogic.chc.v2-int A) " " (shenlogic.chc.v2-int B) ")")
  [i-sub A B] -> (@s "(- " (shenlogic.chc.v2-int A) " " (shenlogic.chc.v2-int B) ")")
  [i-mul A B] -> (@s "(* " (shenlogic.chc.v2-int A) " " (shenlogic.chc.v2-int B) ")")
  X -> (if (number? X) (str X) "0"))

(define shenlogic.chc.v2-string
  [s-var X] -> (shenlogic.chc.v2-var "s" X)
  [s-lit X] -> (shenlogic.chc.v2-quote X)
  X -> (if (string? X) (shenlogic.chc.v2-quote X)
          (shenlogic.chc.v2-quote (str X))))

(define shenlogic.chc.v2-quote
  S -> (let Q (pos (serialize.canonical "") 0)
         (@s Q (shenlogic.chc.v2-escape S) Q)))

(define shenlogic.chc.v2-escape
  "" -> ""
  S -> (let C (pos S 0)
         (@s (shenlogic.chc.v2-escape-char C)
             (shenlogic.chc.v2-escape (tlstr S)))))

(define shenlogic.chc.v2-escape-char
  C -> C)

(define shenlogic.chc.v2-op
  = -> "="
  != -> "distinct"
  < -> "<"
  > -> ">"
  <= -> "<="
  >= -> ">="
  X -> (str X))

(define shenlogic.chc.v2-accessor
  Target I -> (@s (shenlogic.chc.v2-name Target) "_f" (str I)))

(define shenlogic.chc.v2-accessor-for
  Tag I Constructors ->
    (let Target (shenlogic.chc.v2-ctor-target Tag Constructors)
      (shenlogic.chc.v2-accessor Target I)))

(define shenlogic.chc.v2-ctor-symbol
  Tag Constructors -> (shenlogic.chc.v2-name (shenlogic.chc.v2-ctor-target Tag Constructors)))

(define shenlogic.chc.v2-var
  Kind X -> (@s "sl_" Kind "_" (shenlogic.chc.v2-clean (str X))))

(define shenlogic.chc.v2-name
  X -> (let S (shenlogic.chc.v2-clean (str X))
         (if (= S "") "sl_anon" S)))

(define shenlogic.chc.v2-clean
  "" -> ""
  S -> (let C (pos S 0)
         (@s (shenlogic.chc.v2-clean-char C)
             (shenlogic.chc.v2-clean (tlstr S)))))

(define shenlogic.chc.v2-clean-char
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
  C -> C)

(define shenlogic.chc.v2-relation-name
  Name [name-map Pairs] ->
    (shenlogic.chc.v2-name (shenlogic.chc.v2-map-name Name Pairs))
  Name _ -> (shenlogic.chc.v2-name Name))

(define shenlogic.chc.v2-map-name
  X [] -> X
  X [[X Y] | _] -> Y
  X [_ | Xs] -> (shenlogic.chc.v2-map-name X Xs))

(define shenlogic.chc.v2-ctor-target
  int _ -> (intern "VInt")
  true _ -> (intern "VTrue")
  false _ -> (intern "VFalse")
  symbol _ -> (intern "VSymbol")
  string _ -> (intern "VString")
  nil _ -> (intern "VNil")
  cons _ -> (intern "VCons")
  Tag [] -> Tag
  Tag [[constructor Source Target _] | Cs] ->
    (if (or (= Tag Source) (= Tag Target)) Target
        (shenlogic.chc.v2-ctor-target Tag Cs))
  Tag [[constructor Target _] | Cs] ->
    (if (= Tag Target) Target (shenlogic.chc.v2-ctor-target Tag Cs))
  Tag _ -> Tag)

(define shenlogic.chc.v2-variables
  [] _ -> ""
  [[rule _ _ _ _ _ Bound _ _] | Rs] Seen ->
    (let Vars (shenlogic.chc.v2-bound-vars Bound Seen)
      (@s (shenlogic.chc.v2-declare-vars Vars)
          (shenlogic.chc.v2-variables Rs (append Vars Seen)))))

(define shenlogic.chc.v2-bound-vars
  [] _ -> []
  [[v-var X] | Xs] Seen ->
    (if (element? [v X] Seen) (shenlogic.chc.v2-bound-vars Xs Seen)
        [[v X] | (shenlogic.chc.v2-bound-vars Xs (append Seen [[v X]]))])
  [[i-var X] | Xs] Seen ->
    (if (element? [i X] Seen) (shenlogic.chc.v2-bound-vars Xs Seen)
        [[i X] | (shenlogic.chc.v2-bound-vars Xs (append Seen [[i X]]))])
  [[s-var X] | Xs] Seen ->
    (if (element? [s X] Seen) (shenlogic.chc.v2-bound-vars Xs Seen)
        [[s X] | (shenlogic.chc.v2-bound-vars Xs (append Seen [[s X]]))])
  [_ | Xs] Seen -> (shenlogic.chc.v2-bound-vars Xs Seen))

(define shenlogic.chc.v2-declare-vars
  [] -> ""
  [[v X] | Xs] -> (@s "(declare-var " (shenlogic.chc.v2-var "v" X) " Value)" (n->string 10)
                         (shenlogic.chc.v2-declare-vars Xs))
  [[i X] | Xs] -> (@s "(declare-var " (shenlogic.chc.v2-var "i" X) " Int)" (n->string 10)
                         (shenlogic.chc.v2-declare-vars Xs))
  [[s X] | Xs] -> (@s "(declare-var " (shenlogic.chc.v2-var "s" X) " String)" (n->string 10)
                         (shenlogic.chc.v2-declare-vars Xs)))

\\ Conservative validation is done before rendering.  In particular, an
\\ unknown tagged term never gets silently rendered as a Value constant.
(define shenlogic.chc.v2-supported?
  Constructors Relations Rules SCCs NameMap ->
    (and (shenlogic.chc.v2-constructors-ok? Constructors [])
      (and (shenlogic.chc.v2-relations-ok? Relations [])
        (and (shenlogic.chc.v2-rules-ok? Rules Relations Constructors NameMap)
          (shenlogic.chc.v2-name-map-ok? NameMap)))))

(define shenlogic.chc.v2-constructors-ok?
  [] _ -> true
  [[constructor Source Target Arity] | Cs] Seen ->
    (and (number? Arity)
      (and (>= Arity 0)
        (and (not (shenlogic.chc.v2-reserved-ctor? Target))
          (and (not (element? Target Seen))
            (shenlogic.chc.v2-constructors-ok? Cs [Target | Seen])))))
  [[constructor Target Arity] | Cs] Seen ->
    (and (number? Arity)
      (and (>= Arity 0)
        (and (not (shenlogic.chc.v2-reserved-ctor? Target))
          (and (not (element? Target Seen))
            (shenlogic.chc.v2-constructors-ok? Cs [Target | Seen])))))
  _ _ -> false)

(define shenlogic.chc.v2-reserved-ctor?
  Target -> (or (= Target (intern "VInt"))
    (or (= Target (intern "VTrue"))
      (or (= Target (intern "VFalse"))
        (or (= Target (intern "VSymbol"))
          (or (= Target (intern "VString"))
            (or (= Target (intern "VNil")) (= Target (intern "VCons")))))))))

(define shenlogic.chc.v2-relations-ok?
  [] _ -> true
  [[relation Name Sorts Result] | Rs] Seen ->
    (and (not (element? Name Seen))
      (and (shenlogic.chc.v2-sorts-ok? Sorts)
        (and (= Result value)
          (shenlogic.chc.v2-relations-ok? Rs [Name | Seen]))))
  _ _ -> false)

(define shenlogic.chc.v2-sorts-ok?
  [] -> true
  [value | Ss] -> (shenlogic.chc.v2-sorts-ok? Ss)
  _ -> false)

(define shenlogic.chc.v2-name-map-ok?
  [] -> true
  [name-map Pairs] -> (shenlogic.chc.v2-name-pairs-ok? Pairs [])
  _ -> false)

(define shenlogic.chc.v2-name-pairs-ok?
  [] _ -> true
  [[Source Target] | Ps] Seen ->
    (and (not (element? Source Seen))
      (shenlogic.chc.v2-name-pairs-ok? Ps [Source | Seen]))
  _ _ -> false)

(define shenlogic.chc.v2-rules-ok?
  [] _ _ _ -> true
  [[rule _ Function _ _ Args Bound Premises Result] | Rs]
    Relations Constructors NameMap ->
    (and (shenlogic.chc.v2-relation-present? Function Relations)
      (and (shenlogic.chc.v2-bound-ok? Bound [])
        (and (shenlogic.chc.v2-terms-ok? Args Bound Constructors)
          (and (shenlogic.chc.v2-term-ok? Result Bound Constructors)
            (and (shenlogic.chc.v2-premises-ok? Premises Relations Constructors Bound NameMap)
              (shenlogic.chc.v2-rules-ok? Rs Relations Constructors NameMap))))))
  _ _ _ _ -> false)

(define shenlogic.chc.v2-bound-ok?
  [] _ -> true
  [[v-var X] | Xs] Seen ->
    (if (element? [v-var X] Seen) (shenlogic.chc.v2-bound-ok? Xs Seen)
        (shenlogic.chc.v2-bound-ok? Xs (append Seen [[v-var X]])))
  [[i-var X] | Xs] Seen ->
    (if (element? [i-var X] Seen) (shenlogic.chc.v2-bound-ok? Xs Seen)
        (shenlogic.chc.v2-bound-ok? Xs (append Seen [[i-var X]])))
  [[s-var X] | Xs] Seen ->
    (if (element? [s-var X] Seen) (shenlogic.chc.v2-bound-ok? Xs Seen)
        (shenlogic.chc.v2-bound-ok? Xs (append Seen [[s-var X]])))
  _ _ -> false)

(define shenlogic.chc.v2-terms-ok?
  [] _ _ -> true
  [X | Xs] Bound Constructors ->
    (and (shenlogic.chc.v2-term-ok? X Bound Constructors)
      (shenlogic.chc.v2-terms-ok? Xs Bound Constructors)))

(define shenlogic.chc.v2-term-ok?
  [v-var X] Bound _ -> (element? [v-var X] Bound)
  [v-int X] Bound _ -> (shenlogic.chc.v2-int-ok? X Bound)
  v-true _ _ -> true
  v-false _ _ -> true
  [v-symbol _] _ _ -> true
  [v-string X] Bound _ -> (shenlogic.chc.v2-string-ok? X Bound)
  v-nil _ _ -> true
  [v-cons H T] Bound Constructors ->
    (and (shenlogic.chc.v2-term-ok? H Bound Constructors)
      (shenlogic.chc.v2-term-ok? T Bound Constructors))
  [v-ctor Tag Args] Bound Constructors ->
    (let Arity (shenlogic.chc.v2-ctor-arity Tag Constructors)
      (and (>= Arity 0)
        (and (= Arity (length Args))
          (shenlogic.chc.v2-terms-ok? Args Bound Constructors))))
  _ _ _ -> false)

(define shenlogic.chc.v2-string-ok?
  [s-var X] Bound -> (element? [s-var X] Bound)
  [s-lit _] _ -> true
  X _ -> (if (cons? X) false true))

(define shenlogic.chc.v2-int-ok?
  [i-var X] Bound -> (element? [i-var X] Bound)
  [i-lit X] _ -> (number? X)
  [i-add A B] Bound -> (and (shenlogic.chc.v2-int-ok? A Bound)
                            (shenlogic.chc.v2-int-ok? B Bound))
  [i-sub A B] Bound -> (and (shenlogic.chc.v2-int-ok? A Bound)
                            (shenlogic.chc.v2-int-ok? B Bound))
  [i-mul A B] Bound -> (and (shenlogic.chc.v2-int-ok? A Bound)
                            (shenlogic.chc.v2-int-ok? B Bound))
  _ _ -> false)

(define shenlogic.chc.v2-premises-ok?
  [] _ _ _ _ -> true
  [[call F Args Result] | Ps] Relations Constructors Bound NameMap ->
    (and (shenlogic.chc.v2-relation-present? F Relations)
      (and (= (+ (length Args) 1) (shenlogic.chc.v2-relation-arity F Relations))
        (and (shenlogic.chc.v2-terms-ok? Args Bound Constructors)
          (and (shenlogic.chc.v2-term-ok? Result Bound Constructors)
            (shenlogic.chc.v2-premises-ok? Ps Relations Constructors Bound NameMap)))))
  [[value-eq A B] | Ps] Relations Constructors Bound NameMap ->
    (and (shenlogic.chc.v2-term-ok? A Bound Constructors)
      (and (shenlogic.chc.v2-term-ok? B Bound Constructors)
        (shenlogic.chc.v2-premises-ok? Ps Relations Constructors Bound NameMap)))
  [[value-neq A B] | Ps] Relations Constructors Bound NameMap ->
    (and (shenlogic.chc.v2-term-ok? A Bound Constructors)
      (and (shenlogic.chc.v2-term-ok? B Bound Constructors)
        (shenlogic.chc.v2-premises-ok? Ps Relations Constructors Bound NameMap)))
  [[decompose V Tag Fields] | Ps] Relations Constructors Bound NameMap ->
    (and (shenlogic.chc.v2-term-ok? V Bound Constructors)
      (and (= (length Fields) (shenlogic.chc.v2-ctor-arity Tag Constructors))
        (and (shenlogic.chc.v2-terms-ok? Fields Bound Constructors)
          (shenlogic.chc.v2-premises-ok? Ps Relations Constructors Bound NameMap))))
  [[not-tag V Tag] | Ps] Relations Constructors Bound NameMap ->
    (and (shenlogic.chc.v2-term-ok? V Bound Constructors)
      (and (>= (shenlogic.chc.v2-ctor-arity Tag Constructors) 0)
        (shenlogic.chc.v2-premises-ok? Ps Relations Constructors Bound NameMap)))
  [[int-test Op A B] | Ps] Relations Constructors Bound NameMap ->
    (and (shenlogic.chc.v2-op-ok? Op)
      (and (shenlogic.chc.v2-int-ok? A Bound)
        (and (shenlogic.chc.v2-int-ok? B Bound)
          (shenlogic.chc.v2-premises-ok? Ps Relations Constructors Bound NameMap))))
  _ _ _ _ _ -> false)

(define shenlogic.chc.v2-op-ok?
  = -> true
  != -> true
  < -> true
  > -> true
  <= -> true
  >= -> true
  _ -> false)

(define shenlogic.chc.v2-relation-present?
  _ [] -> false
  Name [[relation Name _ _] | _] -> true
  Name [_ | Rs] -> (shenlogic.chc.v2-relation-present? Name Rs))

(define shenlogic.chc.v2-relation-arity
  _ [] -> -1
  Name [[relation Name Sorts _] | _] -> (+ 1 (length Sorts))
  Name [_ | Rs] -> (shenlogic.chc.v2-relation-arity Name Rs))

(define shenlogic.chc.v2-ctor-arity
  int _ -> 1
  true _ -> 0
  false _ -> 0
  symbol _ -> 1
  string _ -> 1
  nil _ -> 0
  cons _ -> 2
  Tag [[constructor Source Target Arity] | Cs] ->
    (if (or (= Tag Source) (= Tag Target)) Arity
        (shenlogic.chc.v2-ctor-arity Tag Cs))
  Tag [[constructor Target Arity] | Cs] ->
    (if (= Tag Target) Arity (shenlogic.chc.v2-ctor-arity Tag Cs))
  _ _ -> -1)
