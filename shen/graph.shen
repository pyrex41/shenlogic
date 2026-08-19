\\ Readable, lossless least-graph rendering.  The graph is a review artifact:
\\ its source of truth remains the v2 Rule IR and its explicit premises.

(define graph.render
  [theory [value-signature Constructors] Relations Rules SCCs NameMap] ->
    (@s "; ShenLogic typed evaluation graph v2~%"
          (graph.value-signature Constructors)
          (graph.relations Relations)
          (graph.rules Rules)
          (graph.sccs SCCs)
          (graph.name-map NameMap))
  [theory Declarations Rules SCCs] ->
    (@s "; ShenLogic typed evaluation graph v1~%"
          (graph.declarations Declarations)
          (graph.rules Rules)
          (graph.sccs SCCs))
  X -> (@s "; invalid theory: " (serialize.canonical X)))

(define render-graph
  Theory -> (graph.render Theory))

(define graph.value-signature
  Constructors ->
    (@s "(value-signature (constructors "
          (graph.constructor-list Constructors) "))~%"))

(define graph.constructor-list
  [] -> ""
  [C] -> (graph.constructor C)
  [C | Cs] -> (@s (graph.constructor C) " "
                  (graph.constructor-list Cs)))

(define graph.constructor
  [constructor Source Target Arity] ->
    (@s "(constructor " (graph.atom Source) " "
         (graph.atom Target) " " (graph.atom Arity) ")")
  C -> (serialize.canonical C))

(define graph.relations
  [] -> ""
  [R | Rs] -> (@s (graph.relation R) (graph.relations Rs)))

(define graph.relation
  [relation Name Sorts Result] ->
    (@s "(relation " (graph.atom Name) " ("
         (graph.term-list Sorts) ") " (graph.term Result) ")~%")
  R -> (@s (serialize.canonical R) "~%"))

\\ v1 declaration spelling retained for callers of the old graph API.
(define graph.declarations
  [] -> ""
  [[relation Name Sorts Result] | Ds] ->
    (@s "(relation " (graph.atom Name) " ("
          (graph.term-list (append Sorts [Result])) "))~%"
          (graph.declarations Ds))
  [D | Ds] -> (@s (serialize.canonical D) "~%"
                (graph.declarations Ds)))

(define graph.rules
  [] -> ""
  [R | Rs] -> (cn (graph.rule R) (graph.rules Rs)))

(define graph.rule
  [rule Id Function Clause Path Args Bound Premises Result] ->
    (@s "(rule " (graph.atom Id) " (function " (graph.atom Function)
         ") (clause " (graph.atom Clause) ") (path "
         (graph.term Path) ")~%  (args (" (graph.term-list Args)
         "))~%  (bound (" (graph.term-list Bound) "))~%  (when "
         (graph.premises Premises) ")~%  (derive (" (graph.atom Function)
         " " (graph.term-list (append Args [Result])) "))~%)~%")
  [rule Id Function Args Bound Premises Result] ->
    (@s "(rule " (graph.atom Id) " (when " (graph.premises Premises)
         ") (derive (" (graph.atom Function) " "
         (graph.term-list (append Args [Result])) ")))~%")
  R -> (@s (serialize.canonical R) "~%"))

(define graph.premises
  [] -> "true"
  [P] -> (graph.premise P)
  Ps -> (@s "(and " (graph.premise-list Ps) ")"))

(define graph.premise-list
  [] -> ""
  [P] -> (graph.premise P)
  [P | Ps] -> (@s (graph.premise P) " " (graph.premise-list Ps)))

(define graph.premise
  [call Name Args Result] ->
    (@s "(call " (graph.atom Name) " (" (graph.term-list Args)
         ") " (graph.term Result) ")")
  [value-eq A B] -> (@s "(value-eq " (graph.term A) " "
                         (graph.term B) ")")
  [value-neq A B] -> (@s "(value-neq " (graph.term A) " "
                          (graph.term B) ")")
  [constraint E] -> (@s "(constraint " (graph.term E) ")")
  [= A B] -> (@s "(= " (graph.term A) " " (graph.term B) ")")
  [!= A B] -> (@s "(!= " (graph.term A) " " (graph.term B) ")")
  [match P A] -> (@s "(match " (graph.term P) " " (graph.term A) ")")
  [decompose Tag A] -> (@s "(decompose " (graph.atom Tag) " "
                              (graph.term A) ")")
  [not-tag Tag A] -> (@s "(not-tag " (graph.atom Tag) " "
                             (graph.term A) ")")
  [int-test Test A] -> (@s "(int-test " (graph.atom Test) " "
                               (graph.term A) ")")
  [not-applicable I Patterns Args Guard] ->
    (@s "(not-applicable " (graph.atom I) " (" (graph.term-list Patterns)
        ") (" (graph.term-list Args) ") " (graph.term Guard) ")")
  P -> (graph.term P))

(define graph.term-list
  [] -> ""
  [X] -> (graph.term X)
  [X | Xs] -> (@s (graph.term X) " " (graph.term-list Xs)))

(define graph.term
  [v-var X] -> (@s "(v-var " (graph.atom X) ")")
  [v-int I] -> (@s "(v-int " (graph.int-term I) ")")
  v-true -> "v-true"
  v-false -> "v-false"
  [v-symbol S] -> (@s "(v-symbol " (graph.atom S) ")")
  [v-string S] -> (@s "(v-string " (graph.atom S) ")")
  [v-ctor Tag Args] -> (@s "(v-ctor " (graph.atom Tag) " ("
                              (graph.term-list Args) "))")
  [i-var X] -> (@s "(i-var " (graph.atom X) ")")
  [i-lit N] -> (@s "(i-lit " (graph.atom N) ")")
  [i-add A B] -> (@s "(i-add " (graph.int-term A) " "
                       (graph.int-term B) ")")
  [i-sub A B] -> (@s "(i-sub " (graph.int-term A) " "
                       (graph.int-term B) ")")
  [i-mul A B] -> (@s "(i-mul " (graph.int-term A) " "
                       (graph.int-term B) ")")
  [s-var X] -> (@s "(s-var " (graph.atom X) ")")
  [s-lit S] -> (@s "(s-lit " (graph.atom S) ")")
  X -> (serialize.canonical X))

(define graph.int-term
  [i-var X] -> (@s "(i-var " (graph.atom X) ")")
  [i-lit N] -> (@s "(i-lit " (graph.atom N) ")")
  [i-add A B] -> (@s "(i-add " (graph.int-term A) " "
                       (graph.int-term B) ")")
  [i-sub A B] -> (@s "(i-sub " (graph.int-term A) " "
                       (graph.int-term B) ")")
  [i-mul A B] -> (@s "(i-mul " (graph.int-term A) " "
                       (graph.int-term B) ")")
  X -> (graph.term X))

(define graph.atom
  X -> (serialize.canonical X))

(define graph.sccs
  [] -> ""
  [[scc Names] | Ss] ->
    (@s "(least-scc (" (graph.relation-names Names) "))~%"
          (graph.sccs Ss))
  [S | Ss] -> (@s "(least-scc " (graph.term S) ")~%"
                (graph.sccs Ss)))

(define graph.relation-names
  [] -> ""
  [X] -> (graph.atom X)
  [X | Xs] -> (@s (graph.atom X) " " (graph.relation-names Xs)))

(define graph.name-map
  [name-map Pairs] -> (@s "(name-map (" (graph.name-pairs Pairs) "))~%")
  none -> ""
  X -> (@s "(name-map " (graph.term X) ")~%"))

(define graph.name-pairs
  [] -> ""
  [[A B]] -> (@s "(" (graph.atom A) " " (graph.atom B) ")")
  [[A B] | Ps] -> (@s "(" (graph.atom A) " " (graph.atom B) ") "
                       (graph.name-pairs Ps))
  [P | Ps] -> (@s (graph.term P) " " (graph.name-pairs Ps)))

\\ Compatibility aliases used by the v1 CHC/THF renderers.
(define graph.expr
  X -> (graph.term X))
(define graph.exprs
  Xs -> (graph.term-list Xs))
(define graph.guard
  none -> "none"
  [some G] -> (graph.term G)
  G -> (graph.term G))
(define graph.names
  Xs -> (graph.relation-names Xs))
(define graph.relation-name
  X -> (graph.atom X))
