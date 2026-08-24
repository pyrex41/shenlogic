\\ Validation for the exact-integer, pure, first-order v1 fragment.

(define shenlogic.validate.program
  [program Definitions] ->
    (let Names (map (/. D (shenlogic.ast.definition-name D)) Definitions)
      (let Errors (shenlogic.validate.program-errors-env [program Definitions] Definitions Names)
        (if (= Errors []) [ok [program Definitions]] [errors (reverse Errors)])))
  X -> [errors [[sl-v000 X]]])

(define shenlogic.validate.program-errors-env
  Program Definitions Names ->
    (append (shenlogic.validate.name-errors Names [])
      (append (shenlogic.validate.reserved-errors Names)
        (append (shenlogic.validate.signature-errors Definitions)
          (append (shenlogic.validate.constructor-errors
                    (shenlogic.ast.constructor-environment Program))
            (shenlogic.validate.definitions-env Definitions Names
              (shenlogic.validate.constructor-list Program)
              (shenlogic.validate.signature-table Definitions) []))))))

\\ Definition-order table of name, arity, and normalized signature, used to
\\ validate function-typed argument positions.
(define shenlogic.validate.signature-table
  [] -> []
  [[definition Name Sig _ Arity] | Ds] ->
    [[Name Arity Sig] | (shenlogic.validate.signature-table Ds)]
  [_ | Ds] -> (shenlogic.validate.signature-table Ds))

(define shenlogic.validate.table-entry
  _ [] -> none
  Name [[Name Arity Sig] | _] -> [found Arity Sig]
  Name [_ | Es] -> (shenlogic.validate.table-entry Name Es))

(define shenlogic.validate.reserved-errors
  [] -> []
  [N | Ns] ->
    (append (if (shenlogic.validate.prefix? "sl.apply-" (str N))
                [[sl-v048 reserved-name N]] [])
            (shenlogic.validate.reserved-errors Ns)))

(define shenlogic.validate.prefix?
  "" _ -> true
  _ "" -> false
  Pre S -> (if (= (pos Pre 0) (pos S 0))
               (shenlogic.validate.prefix? (tlstr Pre) (tlstr S))
               false))

(define shenlogic.validate.constructor-list
  Program -> (hd (tl (shenlogic.ast.constructor-environment Program))))

(define shenlogic.validate.constructor-tags
  [] -> []
  [[constructor Source _ _] | Cs] ->
    [Source | (shenlogic.validate.constructor-tags Cs)])

(define shenlogic.validate.name-errors
  [] _ -> []
  [N | Ns] Seen ->
    (if (element? N Seen)
        [[sl-v003 duplicate-definition N] |
          (shenlogic.validate.name-errors Ns Seen)]
        (shenlogic.validate.name-errors Ns [N | Seen])))

(define shenlogic.validate.signature-errors
  [] -> []
  [[definition Name Sig _ Arity] | Ds] ->
    (append (shenlogic.validate.signature-error Name Sig Arity)
            (shenlogic.validate.signature-errors Ds)))

(define shenlogic.validate.signature-error
  _ none _ -> []
  Name [error _ Type] _ -> [[sl-v004 invalid-signature Name Type]]
  Name [signature Args Result] Arity ->
    (append (if (= (length Args) Arity) []
                [[sl-v005 signature-arity Name Arity (length Args)]])
      (append (shenlogic.validate.argument-type-errors Name Args)
              (if (shenlogic.validate.contains-arrow? Result)
                  [[sl-v006 higher-order-signature Name Result]] [])))
  Name Type _ -> [[sl-v004 invalid-signature Name Type]])

\\ Arrow types are legal in argument positions (function parameters) but may
\\ not nest: no higher-rank parameters and no function-valued components.
(define shenlogic.validate.argument-type-errors
  _ [] -> []
  Name [T | Ts] ->
    (append
      (if (shenlogic.ast.arrow-type? T)
          (if (shenlogic.validate.any-arrow?
                (append (shenlogic.ast.arrow-args T)
                        [(shenlogic.ast.arrow-result T)]))
              [[sl-v041 nested-higher-order Name T]] [])
          (if (shenlogic.validate.contains-arrow? T)
              [[sl-v041 nested-higher-order Name T]] []))
      (shenlogic.validate.argument-type-errors Name Ts)))

(define shenlogic.validate.any-arrow?
  [] -> false
  [T | Ts] -> (if (shenlogic.validate.contains-arrow? T)
                  true
                  (shenlogic.validate.any-arrow? Ts)))

(define shenlogic.validate.contains-arrow?
  T -> (if (cons? T) (shenlogic.validate.arrow-in-list? T) false))

(define shenlogic.validate.arrow-in-list?
  [] -> false
  [X | Xs] -> (if (shenlogic.ast.atom-spelling? X "-->")
                  true
                  (if (shenlogic.validate.contains-arrow? X)
                      true
                      (shenlogic.validate.arrow-in-list? Xs))))

(define shenlogic.validate.function-type?
  [A --> B] -> true
  [A | Rest] -> (element? --> Rest)
  _ -> false)

(define shenlogic.validate.constructor-errors
  [value-signature Constructors] ->
    (shenlogic.validate.constructor-errors-list Constructors [])
  _ -> [])

(define shenlogic.validate.constructor-errors-list
  [] _ -> []
  [[constructor Tag _ Arity] | Cs] Seen ->
    (let Prior (shenlogic.validate.constructor-prior Tag Seen)
      (append (if (= Prior none) []
                  (if (= (hd (tl Prior)) Arity) []
                      [[sl-v030 constructor-arity Tag (hd (tl Prior)) Arity]]))
              (shenlogic.validate.constructor-errors-list Cs
                [[Tag Arity] | Seen]))))

(define shenlogic.validate.constructor-prior
  _ [] -> none
  Tag [[Tag Arity] | _] -> [found Arity]
  Tag [_ | Ss] -> (shenlogic.validate.constructor-prior Tag Ss))

\\ Body validation carries the closed-world constructor environment.  A
\\ constructor is admissible only when its pattern established tag/arity is
\\ present; unknown applications remain diagnostics.
(define shenlogic.validate.definitions-env
  [] _ _ _ Errors -> Errors
  [D | Ds] Names Constructors Table Errors ->
    (shenlogic.validate.definitions-env Ds Names Constructors Table
      (append (shenlogic.validate.definition-env D Names Constructors Table)
              Errors)))

(define shenlogic.validate.definition-env
  [definition Name Sig Clauses Arity] Names Constructors Table ->
    (shenlogic.validate.clauses-env Clauses Arity Names Constructors Table
      Sig Name)
  X _ _ _ -> [[sl-v001 X]])

(define shenlogic.validate.clauses-env
  [] _ _ _ _ _ _ -> []
  [[clause I Patterns Guard Body] | Cs] Arity Names Constructors Table Sig Name ->
    (let FE (shenlogic.validate.fn-env Patterns Sig Name I)
      (append
        (if (= (length Patterns) Arity) [] [[sl-v002 Name I]])
        (append (shenlogic.validate.patterns Patterns)
          (append (hd (tl (tl FE)))
            (append (shenlogic.validate.guard Guard Names)
              (append (shenlogic.validate.expr-env Body Names Constructors
                        (hd (tl FE)) Table)
                (shenlogic.validate.clauses-env Cs Arity Names Constructors
                  Table Sig Name)))))))
  [X | Cs] Arity Names Constructors Table Sig Name ->
    [[sl-v001 X] |
     (shenlogic.validate.clauses-env Cs Arity Names Constructors Table Sig
       Name)])

\\ Per-clause function-parameter environment: [fnenv [[Var Arity] ...] Errs].
\\ Arrow-typed argument positions accept only a variable or wildcard pattern
\\ (sl-v046); a function-typed variable may not be bound twice (sl-v047).
(define shenlogic.validate.fn-env
  Patterns [signature Ts _] Name I ->
    (shenlogic.validate.fn-env-walk Patterns Ts Name I
      (shenlogic.validate.raw-vars-list Patterns) [] [])
  _ _ _ _ -> [fnenv [] []])

(define shenlogic.validate.fn-env-walk
  _ [] _ _ _ Env Errs -> [fnenv (reverse Env) (reverse Errs)]
  [] _ _ _ _ Env Errs -> [fnenv (reverse Env) (reverse Errs)]
  [P | Ps] [T | Ts] Name I AllVars Env Errs ->
    (if (shenlogic.ast.arrow-type? T)
        (if (shenlogic.ast.atom-spelling? P "_")
            (shenlogic.validate.fn-env-walk Ps Ts Name I AllVars Env Errs)
            (if (variable? P)
                (shenlogic.validate.fn-env-walk Ps Ts Name I AllVars
                  [[P (shenlogic.ast.arrow-arity T)] | Env]
                  (if (> (shenlogic.validate.occurrences P AllVars) 1)
                      [[sl-v047 function-value-escape Name I P] | Errs]
                      Errs))
                (shenlogic.validate.fn-env-walk Ps Ts Name I AllVars Env
                  [[sl-v046 function-pattern Name I P] | Errs])))
        (shenlogic.validate.fn-env-walk Ps Ts Name I AllVars Env Errs)))

(define shenlogic.validate.occurrences
  _ [] -> 0
  X [X | Xs] -> (+ 1 (shenlogic.validate.occurrences X Xs))
  X [_ | Xs] -> (shenlogic.validate.occurrences X Xs))

(define shenlogic.validate.raw-vars-list
  [] -> []
  [P | Ps] -> (append (shenlogic.validate.raw-vars P)
                      (shenlogic.validate.raw-vars-list Ps)))

(define shenlogic.validate.raw-vars
  P -> (if (variable? P)
           [P]
           (if (cons? P) (shenlogic.validate.raw-vars-list P) [])))

(define shenlogic.validate.fn-arity
  _ [] -> none
  V [[V A] | _] -> [found A]
  V [_ | Es] -> (shenlogic.validate.fn-arity V Es))

(define shenlogic.validate.expr-env
  E Names Constructors FnEnv Table ->
    (if (number? E)
        (if (integer? E) [] [[sl-v010 E]])
        (if (cons? E)
            (shenlogic.validate.application-env E Names Constructors FnEnv
              Table)
            (if (and (variable? E)
                     (not (= (shenlogic.validate.fn-arity E FnEnv) none)))
                [[sl-v047 function-value-escape E]]
                []))))

(define shenlogic.validate.application-env
  [] _ _ _ _ -> []
  [let X A B] Names Constructors FnEnv Table ->
    (append
      (shenlogic.validate.application-arity let [X A B])
      (append
        (if (= (shenlogic.validate.fn-arity X FnEnv) none) []
            [[sl-v047 function-value-escape X]])
        (append (shenlogic.validate.expr-env A Names Constructors FnEnv Table)
                (shenlogic.validate.expr-env B Names Constructors FnEnv
                  Table))))
  [Op | Args] Names Constructors FnEnv Table ->
    (if (cons? Op)
        [[sl-v022 higher-order-callee Op]]
        (if (variable? Op)
            (append
              (let A (shenlogic.validate.fn-arity Op FnEnv)
                (if (= A none)
                    [[sl-v044 applied-variable-needs-signature Op]]
                    (if (= (hd (tl A)) (length Args)) []
                        [[sl-v043 applied-variable-arity Op (hd (tl A))
                          (length Args)]])))
              (shenlogic.validate.expressions-env Args Names Constructors
                FnEnv Table))
            (if (element? Op [/ div mod do effect set! set freeze eval load open close trap-error <-])
                [[sl-v020 Op]]
                (append
                  (shenlogic.validate.application-arity Op Args)
                  (if (and (symbol? Op)
                           (not (or (element? Op [if let and or do cons = + - * < > <= >=])
                                    (element? Op Names)
                                    (shenlogic.validate.constructor-arity? Op (length Args) Constructors))))
                      [[sl-v021 Op]] [])
                  (shenlogic.validate.arguments-env Op Args Names Constructors
                    FnEnv Table))))))

\\ Validate call arguments against the callee's signature when one exists:
\\ arrow-typed positions accept exactly a function-typed variable of equal
\\ arity or a defined function name of equal arity (sl-v045); other
\\ positions recurse ordinarily.
(define shenlogic.validate.arguments-env
  Op Args Names Constructors FnEnv Table ->
    (let E (shenlogic.validate.table-entry Op Table)
      (if (= E none)
          (shenlogic.validate.expressions-env Args Names Constructors FnEnv
            Table)
          (shenlogic.validate.arguments-typed Op Args
            (shenlogic.validate.entry-arg-types E) Names Constructors FnEnv
            Table))))

(define shenlogic.validate.entry-arg-types
  [found _ [signature Ts _]] -> Ts
  _ -> [])

(define shenlogic.validate.arguments-typed
  _ [] _ _ _ _ _ -> []
  Op [A | As] [] Names Constructors FnEnv Table ->
    (append (shenlogic.validate.expr-env A Names Constructors FnEnv Table)
            (shenlogic.validate.arguments-typed Op As [] Names Constructors
              FnEnv Table))
  Op [A | As] [T | Ts] Names Constructors FnEnv Table ->
    (append
      (if (shenlogic.ast.arrow-type? T)
          (shenlogic.validate.function-argument Op A
            (shenlogic.ast.arrow-arity T) FnEnv Table)
          (shenlogic.validate.expr-env A Names Constructors FnEnv Table))
      (shenlogic.validate.arguments-typed Op As Ts Names Constructors FnEnv
        Table)))

(define shenlogic.validate.function-argument
  Op A Arity FnEnv Table ->
    (if (variable? A)
        (let F (shenlogic.validate.fn-arity A FnEnv)
          (if (= F none)
              [[sl-v045 function-argument-mismatch Op A]]
              (if (= (hd (tl F)) Arity) []
                  [[sl-v045 function-argument-mismatch Op A]])))
        (let E (shenlogic.validate.table-entry A Table)
          (if (= E none)
              [[sl-v045 function-argument-mismatch Op A]]
              (if (= (hd (tl E)) Arity) []
                  [[sl-v045 function-argument-mismatch Op A]])))))

(define shenlogic.validate.expressions-env
  [] _ _ _ _ -> []
  [E | Es] Names Constructors FnEnv Table ->
    (append (shenlogic.validate.expr-env E Names Constructors FnEnv Table)
            (shenlogic.validate.expressions-env Es Names Constructors FnEnv
              Table)))

(define shenlogic.validate.constructor-arity?
  _ _ [] -> false
  Tag Arity [[constructor Tag _ Arity] | _] -> true
  Tag Arity [[constructor _ Tag Arity] | _] -> true
  Tag Arity [_ | Cs] -> (shenlogic.validate.constructor-arity? Tag Arity Cs))

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
        (if (element? Op [/ div mod do effect set! set freeze eval load open close trap-error <-])
        [[sl-v020 Op]]
        (append
          (shenlogic.validate.application-arity Op Args)
          (if (and (symbol? Op)
                   (not (or (element? Op [if let and or do cons = + - * < > <= >=])
                            (element? Op Names))))
              [[sl-v021 Op]]
              [])
          (shenlogic.validate.expressions Args Names)))))

(define shenlogic.validate.application-arity
  if Args -> (if (= (length Args) 3) [] [[sl-v024 arity if 3 (length Args)]])
  let Args -> (if (= (length Args) 3) [] [[sl-v024 arity let 3 (length Args)]])
  and Args -> (if (= (length Args) 2) [] [[sl-v024 arity and 2 (length Args)]])
  or Args -> (if (= (length Args) 2) [] [[sl-v024 arity or 2 (length Args)]])
  Op Args -> (if (element? Op [+ - * = neq < > <= >= cons])
                (if (= (length Args) 2) [] [[sl-v024 arity Op 2 (length Args)]])
                []))

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
    (append (if (element? Op [do effect set! set freeze eval load open close trap-error <-])
                 [[sl-l030 Name Index Op]] [])
            (shenlogic.validate.logic-expressions Name Index Args))
  _ _ _ -> [])

(define shenlogic.validate.logic-expressions
  _ _ [] -> []
  Name Index [E | Es] ->
    (append (shenlogic.validate.logic-expr Name Index E)
            (shenlogic.validate.logic-expressions Name Index Es)))
