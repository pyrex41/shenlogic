\\ Validation for the exact-integer, pure, first-order v1 fragment.

(define shenlogic.validate.program
  [program Definitions] ->
    (let Names (map (/. D (shenlogic.ast.definition-name D)) Definitions)
      (let Errors (shenlogic.validate.definitions Definitions Names [])
        (if (= Errors []) [ok [program Definitions]] [errors (reverse Errors)])))
  X -> [errors [[sl-v000 X]]])

(define shenlogic.validate.definitions
  [] _ Errors -> Errors
  [D | Ds] Names Errors ->
    (shenlogic.validate.definitions Ds Names
      (append (shenlogic.validate.definition D Names) Errors)))

(define shenlogic.validate.definition
  [definition Name _ Clauses Arity] Names ->
    (shenlogic.validate.clauses Clauses Arity Names Name)
  X _ -> [[sl-v001 X]])

(define shenlogic.validate.clauses
  [] _ _ _ -> []
  [[clause I Patterns Guard Body] | Cs] Arity Names Name ->
    (append
      (if (= (length Patterns) Arity) [] [[sl-v002 Name I]])
      (append
        (shenlogic.validate.patterns Patterns)
        (append
          (shenlogic.validate.guard Guard Names)
          (append (shenlogic.validate.expr Body Names)
                  (shenlogic.validate.clauses Cs Arity Names Name))))))

(define shenlogic.validate.patterns
  [] -> []
  [P | Ps] -> (append (shenlogic.validate.pattern P)
                      (shenlogic.validate.patterns Ps)))

(define shenlogic.validate.pattern
  P -> (if (number? P)
           (if (integer? P) [] [[sl-v010 P]])
           (if (cons? P)
               (shenlogic.validate.patterns P)
               [])))

(define shenlogic.validate.guard
  none _ -> []
  [some G] Names -> (shenlogic.validate.guard-expr G Names)
  G Names -> (shenlogic.validate.guard-expr G Names))

(define shenlogic.validate.guard-expr
  E _ ->
    (if (cons? E)
        (let Op (hd E)
          (append (if (and (symbol? Op)
                           (not (element? Op [if let and or = + - * < > <= >= cons])))
                      [[sl-v023 guard-user-call Op]] [])
                  (shenlogic.validate.expressions (tl E) [])))
        (shenlogic.validate.expr E [])))

(define shenlogic.validate.expr
  E Names ->
    (if (number? E)
        (if (integer? E) [] [[sl-v010 E]])
        (if (cons? E)
            (shenlogic.validate.application E Names)
            [])))

(define shenlogic.validate.application
  [] _ -> []
  [Op | Args] Names ->
    (if (cons? Op)
        [[sl-v022 higher-order-callee Op]]
        (if (element? Op [/ hd tl lambda freeze eval load open close trap-error <-])
        [[sl-v020 Op]]
        (append
          (if (and (symbol? Op)
                   (not (or (element? Op [if let and or do cons = + - * < > <= >=])
                            (element? Op Names))))
              [[sl-v021 Op]]
              [])
          (shenlogic.validate.expressions Args Names)))))

(define shenlogic.validate.expressions
  [] _ -> []
  [E | Es] Names -> (append (shenlogic.validate.expr E Names)
                            (shenlogic.validate.expressions Es Names)))

\\ The evaluator models short-circuit control directly.  Rule IR v1 does not
\\ yet split control-flow expressions into separate paths, so translation
\\ rejects them instead of compiling both branches eagerly.
(define shenlogic.validate.logic
  [program Definitions] ->
    (let Errors (shenlogic.validate.logic-definitions Definitions [])
      (if (= Errors []) [ok [program Definitions]] [errors (reverse Errors)]))
  X -> [errors [[sl-l000 X]]])

(define shenlogic.validate.logic-definitions
  [] Errors -> Errors
  [[definition Name _ Clauses _] | Ds] Errors ->
    (shenlogic.validate.logic-definitions Ds
      (append (shenlogic.validate.logic-clauses Name Clauses) Errors)))

(define shenlogic.validate.logic-clauses
  _ [] -> []
  Name [[clause Index _ Guard Body] | Cs] ->
    (append (shenlogic.validate.logic-guard Name Index Guard)
      (append (shenlogic.validate.logic-expr Name Index Body)
              (shenlogic.validate.logic-clauses Name Cs))))

(define shenlogic.validate.logic-guard
  _ _ none -> []
  Name Index [some G] -> (shenlogic.validate.logic-expr Name Index G)
  Name Index G -> (shenlogic.validate.logic-expr Name Index G))

(define shenlogic.validate.logic-expr
  Name Index [Op | Args] ->
    (append (if (element? Op [if let and or do]) [[sl-l030 Name Index Op]] [])
            (shenlogic.validate.logic-expressions Name Index Args))
  _ _ _ -> [])

(define shenlogic.validate.logic-expressions
  _ _ [] -> []
  Name Index [E | Es] ->
    (append (shenlogic.validate.logic-expr Name Index E)
            (shenlogic.validate.logic-expressions Name Index Es)))
