\\ SMT-LIB2 constrained Horn clause backend.

(define shenlogic.chc.render
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
