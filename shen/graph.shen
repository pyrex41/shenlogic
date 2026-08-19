\\ Typed graph and simultaneous leastness review dialect.

(define graph.render
  [theory Declarations Rules SCCs] ->
    (@s "; ShenLogic typed evaluation graph v1" (n->string 10)
          (graph.declarations Declarations)
          (graph.rules Rules)
          (graph.sccs SCCs))
  X -> (@s "; invalid theory: " (str X)))

(define graph.declarations
  [] -> ""
  [[relation Name Sorts Result] | Ds] ->
    (@s "(relation " (graph.relation-name Name) " ("
          (graph.names (append Sorts [Result])) "))" (n->string 10)
          (graph.declarations Ds)))

(define graph.rules
  [] -> ""
  [R | Rs] -> (@s (graph.rule R) (graph.rules Rs)))

(define graph.rule
  [rule Id Function Args Bound Premises Result] ->
    (@s "(rule " (str Id) (n->string 10)
          "  (when " (graph.premises Premises) ")" (n->string 10)
          "  (derive (" (graph.relation-name Function) " "
          (graph.exprs (append Args [Result])) "))" (n->string 10)
          ")" (n->string 10))
  _ -> "")

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
    (@s "(" (graph.relation-name Name) " "
          (graph.exprs (append Args [Result])) ")")
  [constraint E] -> (graph.expr E)
  [= A B] -> (@s "(= " (graph.expr A) " " (graph.expr B) ")")
  [!= A B] -> (@s "(!= " (graph.expr A) " " (graph.expr B) ")")
  [match P A] -> (@s "(match " (surface.term P) " " (graph.expr A) ")")
  [not-applicable I Patterns Args Guard] ->
    (@s "(not-applicable " (str I) " ("
        (surface.terms Patterns) ") (" (graph.exprs Args) ") "
        (graph.guard Guard) ")")
  X -> (graph.expr X))

(define graph.guard
  none -> "none"
  [some G] -> (surface.term G)
  G -> (surface.term G))

(define graph.expr
  [add A B] -> (@s "(+ " (graph.expr A) " " (graph.expr B) ")")
  [sub A B] -> (@s "(- " (graph.expr A) " " (graph.expr B) ")")
  [mul A B] -> (@s "(* " (graph.expr A) " " (graph.expr B) ")")
  [eq A B] -> (@s "(= " (graph.expr A) " " (graph.expr B) ")")
  [lt A B] -> (@s "(< " (graph.expr A) " " (graph.expr B) ")")
  [gt A B] -> (@s "(> " (graph.expr A) " " (graph.expr B) ")")
  [le A B] -> (@s "(<= " (graph.expr A) " " (graph.expr B) ")")
  [ge A B] -> (@s "(>= " (graph.expr A) " " (graph.expr B) ")")
  [ite C T F] -> (@s "(if " (graph.expr C) " " (graph.expr T) " " (graph.expr F) ")")
  [app F Args] -> (@s "(" (str F) " " (graph.exprs Args) ")")
  X -> (str X))

(define graph.exprs
  [] -> ""
  [X] -> (graph.expr X)
  [X | Xs] -> (@s (graph.expr X) " " (graph.exprs Xs)))

(define graph.sccs
  [] -> ""
  [[scc Names] | Ss] ->
    (@s "(least-scc (" (graph.relation-names Names) "))" (n->string 10)
          (graph.sccs Ss)))

(define graph.relation-names
  [] -> ""
  [X] -> (graph.relation-name X)
  [X | Xs] -> (@s (graph.relation-name X) " " (graph.relation-names Xs)))

(define graph.names
  [] -> ""
  [X] -> (str X)
  [X | Xs] -> (@s (str X) " " (graph.names Xs)))

(define graph.relation-name
  X -> (@s (str X) "$"))
