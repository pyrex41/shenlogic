\\ ShenLogic executable semantics. AST contract: (program Defs), definitions
\\ (definition Name Signature Clauses Arity), clauses (clause Index Patterns Guard Body).
\\ Guard is none or [some Expr]. Results are [value V], [error Code], [timeout].

(define evaluator-evaluate
  Program Expr Fuel -> (evaluator-expr Program Expr [] Fuel))

(define evaluator-ok
  R -> (= (hd R) value))

(define evaluator-val
  R -> (hd (tl R)))

(define evaluator-expr
  P X E 0 -> [timeout]
  P X E F -> (evaluator-expr1 P X E (- F 1)))

(define evaluator-expr1
  P [var X] E F -> (evaluator-lookup X E)
  P [lit X] E F -> [value X]
  P [if C T F] E N -> (let R (evaluator-expr P C E N)
                       (if (evaluator-ok R)
                           (if (= (evaluator-val R) true)
                               (evaluator-expr P T E N)
                               (evaluator-expr P F E N)) R))
  P [let X A B] E N -> (let R (evaluator-expr P A E N)
                        (if (evaluator-ok R)
                            (evaluator-expr P B [[X (evaluator-val R)] | E] N) R))
  P [and A B] E N -> (let R (evaluator-expr P A E N)
                      (if (evaluator-ok R)
                          (if (= (evaluator-val R) true) (evaluator-expr P B E N) [value false]) R))
  P [or A B] E N -> (let R (evaluator-expr P A E N)
                     (if (evaluator-ok R)
                         (if (= (evaluator-val R) true) [value true] (evaluator-expr P B E N)) R))
  P [call Name Args] E N -> (evaluator-call P Name Args E N [])
  P [apply Name | Args] E N -> (evaluator-call P Name Args E N [])
  P [cons A B] E N -> (let X (evaluator-expr P A E N)
                       (if (evaluator-ok X)
                           (let Y (evaluator-expr P B E N)
                             (if (evaluator-ok Y) [value [(evaluator-val X) | (evaluator-val Y)]] Y)) X))
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
  P [Name | Args] E N -> (evaluator-call P Name Args E N [])
  P X E F -> (if (= F 0) [timeout]
              (let R (evaluator-lookup X E)
                (if (= (hd R) error) [value X] R))))

(define evaluator-lookup
  X [] -> [error unbound-variable]
  X [[Y V] | Es] -> (if (= X Y) [value V] (evaluator-lookup X Es)))

(define sl-bin
  Op P A B E N -> (let X (evaluator-expr P A E N)
                   (if (evaluator-ok X)
                       (let Y (evaluator-expr P B E N)
                         (if (evaluator-ok Y) (evaluator-primitive Op (evaluator-val X) (evaluator-val Y)) Y)) X)))

(define evaluator-primitive
  Op X Y ->
    (let Name (str Op)
      (if (= Name "=") [value (= X Y)]
      (if (= Name "neq") [value (not (= X Y))]
      (if (not (and (number? X) (number? Y))) [error type-error]
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
                           (if (evaluator-ok Y) [value [(evaluator-val X) | (evaluator-val Y)]] Y)) X)))

(define evaluator-call
  P Name [] E N Rev -> (evaluator-dispatch P Name (reverse Rev) N)
  P Name [A | As] E N Rev -> (let X (evaluator-expr P A E N)
                              (if (evaluator-ok X) (evaluator-call P Name As E N [(evaluator-val X) | Rev]) X)))

(define evaluator-dispatch
  P Name Args N -> (let D (evaluator-definition Name P)
                    (if (= D false) [error unknown-function] (evaluator-clauses P D Args N))))

(define evaluator-definition
  Name [program Ds] -> (evaluator-definition Name Ds)
  Name [] -> false
  Name [[definition N Sig Cs Arity] | Ds] -> (if (= Name N) [definition N Sig Cs Arity] (evaluator-definition Name Ds))
  Name [_ | Ds] -> (evaluator-definition Name Ds))

(define evaluator-clauses
  P [definition Name Sig [] Arity] Args N -> [error no-matching-clause]
  P [definition Name Sig [[clause I Ps G B] | Cs] Arity] Args N ->
    (let M (evaluator-match-list Ps Args [])
      (if (= (hd M) match-fail) (evaluator-clauses P [definition Name Sig Cs Arity] Args N)
        (if (= G none) (evaluator-expr P B (tl M) N)
          (let Q (evaluator-expr P (hd (tl G)) (tl M) N)
            (if (evaluator-ok Q)
                (if (= (evaluator-val Q) true) (evaluator-expr P B (tl M) N)
                    (evaluator-clauses P [definition Name Sig Cs Arity] Args N)) Q))))))

(define evaluator-match-list
  [] [] E -> [match-ok | E]
  [P | Ps] [V | Vs] E -> (let R (evaluator-match P V E)
                          (if (= (hd R) match-fail) R (evaluator-match-list Ps Vs (tl R))))
  _ _ E -> [match-fail])

(define evaluator-match
  P V E ->
    (if (= P _)
        [match-ok | E]
        (if (variable? P)
            (let Old (evaluator-binding P E)
              (if (= Old not-found)
                  [match-ok [P V] | E]
                  (if (= (hd (tl Old)) V) [match-ok | E] [match-fail])))
        (if (and (cons? P) (= (hd P) cons))
            (if (cons? V)
                (let H (evaluator-match (hd (tl P)) (hd V) E)
                  (if (= (hd H) match-fail)
                      H
                      (evaluator-match (hd (tl (tl P))) (tl V) (tl H))))
                [match-fail])
        (if (cons? P)
            (if (cons? V)
                (let H (evaluator-match (hd P) (hd V) E)
                  (if (= (hd H) match-fail)
                      H
                      (evaluator-match (tl P) (tl V) (tl H))))
                [match-fail])
            (if (= P V) [match-ok | E] [match-fail]))))))

(define evaluator-binding
  _ [] -> not-found
  X [[X V] | _] -> [found V]
  X [_ | Es] -> (evaluator-binding X Es))
