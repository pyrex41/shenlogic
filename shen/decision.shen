
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
