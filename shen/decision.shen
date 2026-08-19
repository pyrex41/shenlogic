
(define decision-make-match
  Patterns Then Else -> (cons match (cons Patterns (cons Then (cons Else ())))) )

(define decision-make-guard
  Guard Then Else -> (cons guard (cons Guard (cons Then (cons Else ())))) )

(define decision-make-eval
  Expr Var Next -> (cons eval (cons Expr (cons Var (cons Next ())))) )

(define decision-make-return
  Expr -> (cons return (cons Expr ())))

(define decision-make-fail
  Reason -> (cons fail (cons Reason ())))

(define decision-node-tag
  Node -> (hd Node))

(define decision-args
  Node -> (tl Node))

(define decision-clause-patterns
  Clause -> (hd (tl (tl Clause))))

(define decision-clause-guard
  Clause -> (hd (tl (tl (tl Clause)))))

(define decision-clause-body
  Clause -> (hd (tl (tl (tl (tl Clause))))))

(define decision-clause-index
  Clause -> (hd (tl Clause)))

(define decision-clause
  Patterns Guard Body Index -> (cons clause (cons Patterns (cons Guard (cons Body (cons Index ()))))))

(define decision-compile-clauses
  () -> (decision-make-fail no-clause)
  [Clause | Rest] ->
    (decision-compile-clause Clause (decision-compile-clauses Rest)))

(define decision-compile-clause
  Clause Next ->
    (decision-compile-clause-1
      (decision-clause-patterns Clause)
      (decision-clause-guard Clause)
      (decision-clause-body Clause) Next))

(define decision-compile-clause-1
  Patterns none Body Next ->
    (decision-make-match Patterns (decision-make-return Body) Next)
  Patterns true Body Next ->
    (decision-make-match Patterns (decision-make-return Body) Next)
  Patterns [some Guard] Body Next ->
    (decision-make-match Patterns
      (decision-make-guard Guard (decision-make-return Body) Next) Next)
  Patterns Guard Body Next ->
    (decision-make-match Patterns
      (decision-make-guard Guard (decision-make-return Body) Next) Next))

(define decision-compile-definition
  Name Clauses -> (cons definition (cons Name (cons (decision-compile-clauses Clauses) ()))))

(define decision.compile
  [program Definitions] -> (decision-compile-definitions Definitions))

(define decision-compile-definitions
  [] -> []
  [D | Rest] ->
    (cons (decision-compile-definition
            (hd (tl D))
            (hd (tl (tl (tl D)))))
          (decision-compile-definitions Rest)))

\\ 0.2 path API.  Rules lowering consumes these terminal records; keeping
\\ the decision tree API above is useful to clients that render it.
(define decision.path
  Function Clause Path Patterns Guard Body ->
    [path Function Clause Path Patterns Guard Body])

(define decision.paths
  [program Definitions] -> (decision-path-definitions Definitions))

(define decision-path-definitions
  [] -> []
  [[definition Name _ Clauses _] | Ds] ->
    (append (decision-path-clauses Name Clauses 0)
            (decision-path-definitions Ds)))

(define decision-path-clauses
  _ [] _ -> []
  Name [[clause I Patterns Guard Body] | Cs] N ->
    [(decision.path Name I N Patterns Guard Body) |
     (decision-path-clauses Name Cs (+ N 1))])

\\ Explicit path-limit check shared by callers before expensive lowering.
(define decision.path-limit?
  Paths -> (<= (length Paths) 4096))
