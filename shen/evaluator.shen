\\ ShenLogic executable semantics (reference evaluator).
\\
\\ Results are always one of [value V], [error Code], or [timeout].  The
\\ evaluator accepts the original reader representation as well as the closed
\\ normalized representation used by the 0.2 front end:
\\
\\   expressions: e-var, e-value, e-call, e-ctor, e-if, e-let, e-and,
\\               e-or, e-prim
\\   patterns:    p-wild, p-var, p-lit, p-ctor
\\   values:      ctor-value

(define evaluator-evaluate
  Program Expr Fuel -> (evaluator-expr Program
                          (evaluator-input Program Expr) [] Fuel))

\\ Query expressions may still be in the reader's source representation.  Run
\\ them through the same closed-world normalizer used for clause bodies so
\\ constructor applications (for example (node 7)) are values rather than
\\ accidental function calls.  Already-tagged e-* nodes are left untouched.
(define evaluator-input
  [program Definitions] Expr ->
    (if (evaluator-normalized-expression? Expr)
        Expr
        (let Names (map (/. D (shenlogic.ast.definition-name D)) Definitions)
          (let Env (shenlogic.ast.constructor-environment [program Definitions])
            (shenlogic.ast.normalize-expr Expr Names (hd (tl Env))))))
  _ Expr -> Expr)

(define evaluator-normalized-expression?
  [e-var _] -> true
  [e-value _] -> true
  [e-lit _] -> true
  [e-call _ _] -> true
  [e-apply _ _] -> true
  [e-ctor _ _] -> true
  [e-constructor _ _] -> true
  [e-if _ _ _] -> true
  [e-let _ _ _] -> true
  [e-and _ _] -> true
  [e-or _ _] -> true
  [e-prim _ _] -> true
  _ -> false)

(define evaluator-ok
  [value _] -> true
  _ -> false)

(define evaluator-val
  [value V] -> V
  _ -> false)

\\ Every expression node consumes one unit.  A zero budget is observed before
\\ dispatch, which makes recursive calls and strict argument evaluation
\\ deterministic and gives timeout/error precedence over clause fallback.
(define evaluator-expr
  P X E F -> (if (<= F 0)
                 [timeout]
                 (evaluator-expr1 P X E (- F 1))))

(define evaluator-expr1
  P [e-var X] E N -> (evaluator-lookup X E)
  P [e-value X] E N -> [value X]
  P [e-lit X] E N -> [value X]
  P [e-call Name Args] E N -> (evaluator-call P Name Args E N [])
  P [e-apply Head Args] E N -> (evaluator-apply P Head Args E N)
  P [e-ctor Tag Args] E N -> (let R (evaluator-args P Args E N)
                               (if (evaluator-ok R)
                                   (evaluator-construct-value Tag
                                     (evaluator-val R))
                                   R))
  P [e-constructor Tag Args] E N -> (let R (evaluator-args P Args E N)
                                     (if (evaluator-ok R)
                                         (evaluator-construct-value Tag
                                           (evaluator-val R))
                                         R))
  P [e-if C T F] E N -> (evaluator-if P C T F E N)
  P [e-let X A B] E N -> (let R (evaluator-expr P A E N)
                          (if (evaluator-ok R)
                              (evaluator-expr P B [[X (evaluator-val R)] | E] N)
                              R))
  P [e-and A B] E N -> (evaluator-and P A B E N)
  P [e-or A B] E N -> (evaluator-or P A B E N)
  P [e-prim Op Args] E N -> (let R (evaluator-args P Args E N)
                              (if (evaluator-ok R)
                                  (evaluator-primitive-list Op (evaluator-val R))
                                  R))

  P [var X] E N -> (evaluator-lookup X E)
  P [lit X] E N -> [value X]
  P [call Name Args] E N -> (evaluator-call P Name Args E N [])
  P [ctor Tag Args] E N -> (let R (evaluator-args P Args E N)
                             (if (evaluator-ok R)
                                 (evaluator-construct-value Tag
                                   (evaluator-val R))
                                 R))
  P [if C T F] E N -> (evaluator-if P C T F E N)
  P [let X A B] E N -> (let R (evaluator-expr P A E N)
                        (if (evaluator-ok R)
                            (evaluator-expr P B [[X (evaluator-val R)] | E] N)
                            R))
  P [and A B] E N -> (evaluator-and P A B E N)
  P [or A B] E N -> (evaluator-or P A B E N)
  P [cons A B] E N -> (let X (evaluator-expr P A E N)
                       (if (evaluator-ok X)
                           (let Y (evaluator-expr P B E N)
                             (if (evaluator-ok Y)
                                 [value [(evaluator-val X) | (evaluator-val Y)]]
                                 Y))
                           X))
  P [list | Xs] E N -> (evaluator-args P Xs E N)

  P [= A B] E N -> (sl-bin = P A B E N)
  P [neq A B] E N -> (sl-bin neq P A B E N)
  P [+ A B] E N -> (sl-bin + P A B E N)
  P [- A B] E N -> (sl-bin - P A B E N)
  P [* A B] E N -> (sl-bin * P A B E N)
  P [< A B] E N -> (sl-bin < P A B E N)
  P [> A B] E N -> (sl-bin > P A B E N)
  P [<= A B] E N -> (sl-bin <= P A B E N)
  P [>= A B] E N -> (sl-bin >= P A B E N)
  P [apply Head | Args] E N -> (evaluator-apply P Head Args E N)
  P [Name | Args] E N -> (evaluator-call P Name Args E N [])

  P X E N -> (let R (evaluator-lookup X E)
              (if (evaluator-ok R) R [value X]))
)

\\ A function value is its name: resolve the head to a symbol in the
\\ environment, then dispatch by that name.  Non-symbol heads are apply
\\ errors, matching the closed defunctionalized theory.
(define evaluator-apply
  P Head Args E N ->
    (let R (evaluator-expr P (if (variable? Head) [e-var Head] Head) E N)
      (if (evaluator-ok R)
          (if (symbol? (evaluator-val R))
              (evaluator-call P (evaluator-val R) Args E N [])
              [error apply-non-function])
          R)))

(define evaluator-if
  P C T F E N -> (let R (evaluator-expr P C E N)
                  (if (evaluator-ok R)
                      (if (= (evaluator-val R) true)
                          (evaluator-expr P T E N)
                          (evaluator-expr P F E N))
                      R)))

(define evaluator-and
  P A B E N -> (let R (evaluator-expr P A E N)
                (if (evaluator-ok R)
                    (if (= (evaluator-val R) true)
                        (evaluator-expr P B E N)
                        [value false])
                    R)))

(define evaluator-or
  P A B E N -> (let R (evaluator-expr P A E N)
               (if (evaluator-ok R)
                   (if (= (evaluator-val R) true)
                       [value true]
                       (evaluator-expr P B E N))
                   R)))

(define evaluator-lookup
  X [] -> [error unbound-variable]
  X [[Y V] | Es] -> (if (= X Y) [value V] (evaluator-lookup X Es))
  X [_ | Es] -> (evaluator-lookup X Es))

(define sl-bin
  Op P A B E N -> (let X (evaluator-expr P A E N)
                   (if (evaluator-ok X)
                       (let Y (evaluator-expr P B E N)
                         (if (evaluator-ok Y)
                             (evaluator-primitive Op
                               (evaluator-val X) (evaluator-val Y))
                             Y))
                       X)))

(define evaluator-primitive-list
  Op [X Y] -> (evaluator-primitive Op X Y)
  _ _ -> [error arity-error])

\\ Lists are the built-in nil/cons constructors and remain ordinary Shen
\\ lists at the public evaluator boundary.  Other constructors are free,
\\ closed values with an explicit tag and an argument vector.
(define evaluator-construct-value
  nil [] -> [value []]
  cons [H T] -> [value [H | T]]
  Tag Values -> [value [ctor-value Tag Values]])

(define evaluator-primitive
  Op X Y ->
    (let Name (str Op)
      (if (= Name "=") [value (= X Y)]
      (if (= Name "neq") [value (not (= X Y))]
      (if (not (and (integer? X) (integer? Y))) [error type-error]
      (if (= Name "+") [value (+ X Y)]
      (if (= Name "-") [value (- X Y)]
      (if (= Name "*") [value (* X Y)]
      (if (= Name "<") [value (< X Y)]
      (if (= Name ">") [value (> X Y)]
      (if (= Name "<=") [value (<= X Y)]
      (if (= Name ">=") [value (>= X Y)]
          [error unknown-primitive]))))))))))))

(define evaluator-args
  P [] E N -> [value []]
  P [A | As] E N -> (let X (evaluator-expr P A E N)
                     (if (evaluator-ok X)
                         (let Y (evaluator-args P As E N)
                           (if (evaluator-ok Y)
                               [value [(evaluator-val X) |
                                       (evaluator-val Y)]]
                               Y))
                         X))
  P _ E N -> [error malformed-arguments])

(define evaluator-call
  P Name [] E N Rev -> (evaluator-dispatch P Name (reverse Rev) N)
  P Name [A | As] E N Rev -> (let X (evaluator-expr P A E N)
                              (if (evaluator-ok X)
                                  (evaluator-call P Name As E N
                                    [(evaluator-val X) | Rev])
                                  X))
  P Name _ E N Rev -> [error malformed-arguments])

(define evaluator-dispatch
  P Name Args N -> (let D (evaluator-definition Name P)
                    (if (= D false)
                        [error unknown-function]
                        (evaluator-clauses P D Args N))))

(define evaluator-definition
  Name [program Ds] -> (evaluator-definition Name Ds)
  Name [] -> false
  Name [[definition N Sig Cs Arity] | Ds] ->
    (if (= Name N) [definition N Sig Cs Arity]
        (evaluator-definition Name Ds))
  Name [_ | Ds] -> (evaluator-definition Name Ds))

(define evaluator-clauses
  P [definition Name Sig [] Arity] Args N -> [error no-matching-clause]
  P [definition Name Sig [[clause I Ps G B] | Cs] Arity] Args N ->
    (let M (evaluator-match-list Ps Args [])
      (if (= (hd M) match-fail)
          (evaluator-clauses P [definition Name Sig Cs Arity] Args N)
          (if (= G none)
              (evaluator-expr P B (tl M) N)
              (let Q (evaluator-guard G P (tl M) N)
                (if (evaluator-ok Q)
                    (if (= (evaluator-val Q) true)
                        (evaluator-expr P B (tl M) N)
                        (evaluator-clauses
                          P [definition Name Sig Cs Arity] Args N))
                    Q))))))

(define evaluator-guard
  [some G] P E N -> (evaluator-expr P G E N)
  G P E N -> (evaluator-expr P G E N))

\\ Pattern matching returns [match-ok | Bindings].  A repeated variable is
\\ an equality check; it never overwrites its earlier binding.
(define evaluator-match-list
  [] [] E -> [match-ok | E]
  [P | Ps] [V | Vs] E -> (let R (evaluator-match P V E)
                          (if (= (hd R) match-fail)
                              R
                              (evaluator-match-list Ps Vs (tl R))))
  _ _ _ -> [match-fail])

(define evaluator-match
  [p-wild] V E -> [match-ok | E]
  [p-var X] V E -> (evaluator-bind X V E)
  [p-lit X] V E -> (if (= X V) [match-ok | E] [match-fail])
  [p-ctor nil Ps] V E -> (if (= Ps [])
                             (if (= V []) [match-ok | E] [match-fail])
                             [match-fail])
  [p-ctor cons Ps] V E -> (if (and (= (length Ps) 2)
                                      (evaluator-list-value? V))
                              (let H (evaluator-match (hd Ps) (hd V) E)
                                (if (= (hd H) match-fail)
                                    H
                                    (evaluator-match
                                      (hd (tl Ps)) (tl V) (tl H))))
                              [match-fail])
  [p-ctor Tag Ps] V E -> (evaluator-match-ctor Tag Ps V E)
  [p-constructor nil Ps] V E -> (evaluator-match [p-ctor nil Ps] V E)
  [p-constructor cons Ps] V E -> (evaluator-match [p-ctor cons Ps] V E)
  [p-constructor Tag Ps] V E -> (evaluator-match-ctor Tag Ps V E)
  [p-cons A B] V E -> (if (evaluator-list-value? V)
                          (let H (evaluator-match A (hd V) E)
                            (if (= (hd H) match-fail)
                                H
                                (evaluator-match B (tl V) (tl H))))
                          [match-fail])
  P V E -> (if (= P _)
              [match-ok | E]
              (if (variable? P)
                  (evaluator-bind P V E)
                  (if (and (cons? P) (= (hd P) cons))
                      (if (evaluator-list-value? V)
                          (let H (evaluator-match (hd (tl P)) (hd V) E)
                            (if (= (hd H) match-fail)
                                H
                                (evaluator-match
                                  (hd (tl (tl P))) (tl V) (tl H))))
                          [match-fail])
                          (if (cons? P)
                          (if (evaluator-list-value? V)
                              (let H (evaluator-match (hd P) (hd V) E)
                                (if (= (hd H) match-fail)
                                    H
                                    (evaluator-match (tl P) (tl V) (tl H))))
                              [match-fail])
                          (if (= P V) [match-ok | E] [match-fail]))))))

(define evaluator-bind
  X V E -> (let Old (evaluator-binding X E)
            (if (= Old not-found)
                [match-ok [X V] | E]
                (if (= (hd (tl Old)) V)
                    [match-ok | E]
                    [match-fail]))))

(define evaluator-ctor-value
  [ctor-value Tag Values] -> [found Tag Values]
  [constructor-value Tag Values] -> [found Tag Values]
  _ -> not-found)

(define evaluator-list-value?
  V -> (and (cons? V) (= (evaluator-ctor-value V) not-found)))

(define evaluator-match-ctor
  Tag Ps V E -> (let C (evaluator-ctor-value V)
                 (if (= C not-found)
                     [match-fail]
                     (if (= Tag (hd (tl C)))
                         (evaluator-match-list Ps (hd (tl (tl C))) E)
                         [match-fail]))))

(define evaluator-binding
  _ [] -> not-found
  X [[X V] | _] -> [found V]
  X [_ | Es] -> (evaluator-binding X Es))
