\\ ShenLogic 0.2 Rule IR.  All lowering is list based, hence deterministic.

(define rules.compile
  [program Definitions] ->
    (let Names (map (/. D (shenlogic.ast.definition-name D)) Definitions)
      (let Rules (rules.compile-definitions Definitions Names)
        [theory [value-signature (rules.value-signature [program Definitions])]
                (rules.relations Definitions)
                Rules
                (rules.sccs Definitions Names)
                [name-map (rules.name-map Names)]]))
  X -> (error [sl-rules-invalid-program X]))

(define rules.value-signature
  Program -> (rules.value-signature-with Program
    (reverse [[constructor int int 1] [constructor true true 0]
      [constructor false false 0] [constructor symbol symbol 1]
      [constructor string string 1] [constructor nil nil 0]
      [constructor cons cons 2]])))

(define rules.value-signature-with
  [program Definitions] Acc ->
    (rules.signature-definitions Definitions Acc)
  _ Acc -> Acc)

(define rules.signature-definitions
  [] Acc -> (reverse Acc)
  [[definition _ _ Clauses _] | Ds] Acc ->
    (rules.signature-definitions Ds (rules.signature-clauses Clauses Acc)))

(define rules.signature-clauses
  [] Acc -> Acc
  [[clause _ Ps _ _] | Cs] Acc ->
    (rules.signature-clauses Cs (rules.signature-patterns Ps Acc)))

(define rules.signature-patterns
  [] Acc -> Acc
  [P | Ps] Acc ->
    (let T (rules.pattern-tag P)
      (if (= T none)
          (rules.signature-patterns Ps Acc)
          (let A (rules.pattern-arity P)
            (if (rules.has-constructor T Acc)
                (rules.signature-patterns Ps Acc)
                (rules.signature-patterns Ps
                  (cons [constructor T T A] Acc)))))))

(define rules.pattern-tag
  [p-ctor Tag _] -> Tag
  P -> (if (cons? P)
           (if (= (hd P) cons) cons
               (if (or (= (hd P) ctor) (= (hd P) constructor))
                   (hd (tl P)) cons))
           (if (= P []) nil none)))

(define rules.pattern-arity
  [p-ctor _ Fields] -> (length Fields)
  P -> (if (cons? P)
           (if (= (hd P) cons) 2
               (if (or (= (hd P) ctor) (= (hd P) constructor))
                   (length (hd (tl (tl P)))) 2))
           0))

(define rules.has-constructor
  _ [] -> false
  T [[constructor T _ _] | _] -> true
  T [_ | Cs] -> (rules.has-constructor T Cs))

(define rules.name-map
  [] -> []
  [N | Ns] -> [[N N] | (rules.name-map Ns)])

(define rules.relations
  [] -> []
  [[definition N _ _ A] | Ds] ->
    [[relation N (rules.sorts A) value] | (rules.relations Ds)])
(define rules.sorts
  0 -> []
  N -> [value | (rules.sorts (- N 1))])

\\ [rs Premises Bound Env Counter Term].
(define rules.rs
  P B E C T -> [rs P B E C T])
(define rules.rs-p [rs P _ _ _ _] -> P)
(define rules.rs-b [rs _ B _ _ _] -> B)
(define rules.rs-e [rs _ _ E _ _] -> E)
(define rules.rs-c [rs _ _ _ C _] -> C)
(define rules.rs-t [rs _ _ _ _ T] -> T)
(define rules.rs-take
  [rs P B E C _] T -> [rs P B E C T])
(define rules.rs-env
  [rs P B _ C T] E -> [rs P B E C T])
(define rules.rs-counter
  [rs P B E _ T] C -> [rs P B E C T])
(define rules.rs-prem
  S X -> [rs (append (rules.rs-p S) [X]) (rules.rs-b S)
              (rules.rs-e S) (rules.rs-c S) (rules.rs-t S)])
(define rules.rs-bound
  S X -> (if (element? X (rules.rs-b S)) S
             [rs (rules.rs-p S) (append (rules.rs-b S) [X])
                 (rules.rs-e S) (rules.rs-c S) (rules.rs-t S)]))
(define rules.lookup
  _ [] -> not-found
  X [[X V] | _] -> [found V]
  X [_ | Xs] -> (rules.lookup X Xs))
(define rules.term
  X E -> (let F (rules.lookup X E)
           (if (variable? X)
               (if (= F not-found) [v-var X] (hd (tl F)))
               (if (number? X) [v-int [i-lit X]]
                   (if (string? X) [v-string X]
                       (if (= X true) v-true
                           (if (= X false) v-false [v-symbol X])))))))
(define rules.fresh
  Prefix C -> (intern (cn Prefix (str C))))

\\ Pattern matching returns [pm Success FailureStates].
(define rules.match-pattern
  [p-wild] V S -> [pm S []]
  [p-var X] V S -> (rules.match-pattern X V S)
  [p-lit X] V S -> (rules.match-pattern X V S)
  [p-ctor Tag Fields] V S -> (rules.match-constructor-normalized Tag Fields V S)
  P V S ->
    (if (= P _)
        [pm S []]
        (if (variable? P)
            (let F (rules.lookup P (rules.rs-e S))
              (if (= F not-found)
                  [pm (rules.bind S P V) []]
                  (let Old (hd (tl F))
                    [pm S [[rs (append (rules.rs-p S)
                                        [[value-neq Old V]])
                                     (rules.rs-b S) (rules.rs-e S)
                                     (rules.rs-c S) (rules.rs-t S)]]])))
        (if (or (number? P) (string? P) (= P true) (= P false))
            (let T (rules.term P [])
              [pm (rules.rs-prem S [value-eq V T])
                  [[rs (append (rules.rs-p S) [[value-neq V T]])
                       (rules.rs-b S) (rules.rs-e S) (rules.rs-c S)
                       (rules.rs-t S)]]])
        (if (cons? P)
            (let Tag (rules.pattern-tag P)
              (let Fields (rules.pattern-fields P)
                (rules.match-constructor Tag Fields V S)))
            (let T (rules.term P [])
              [pm (rules.rs-prem S [value-eq V T])
                  [[rs (append (rules.rs-p S) [[value-neq V T]])
                       (rules.rs-b S) (rules.rs-e S) (rules.rs-c S)
                       (rules.rs-t S)]]]))))))

(define rules.bind
  S X V -> (let F (rules.lookup X (rules.rs-e S))
            (if (= F not-found)
                [rs (rules.rs-p S) (rules.rs-b S)
                    (append (rules.rs-e S) [[X V]])
                    (rules.rs-c S) (rules.rs-t S)] S)))
(define rules.pattern-fields
  P -> (if (= (hd P) cons)
           [(hd (tl P)) (hd (tl (tl P)))]
           (if (or (= (hd P) ctor) (= (hd P) constructor))
               (hd (tl (tl P))) [(hd P) (tl P)])))

(define rules.match-patterns
  [] [] S -> [pmany [S] []]
  [P | Ps] [V | Vs] S ->
    (let M (rules.match-pattern P V S)
      (let R (rules.match-patterns Ps Vs (hd (tl M)))
        [pmany (hd (tl R)) (append (hd (tl (tl M))) (hd (tl (tl R))))]))
  _ _ S -> [pmany [S] []])

(define rules.match-constructor
  Tag Patterns V S ->
    (let C (rules.rs-c S)
      (let Fields (rules.make-fields Patterns C)
        (let D (rules.rs-prem S [decompose V Tag Fields])
          (let B (rules.add-fields D Fields)
            (let M (rules.match-patterns Patterns Fields B)
              [pm (hd (hd (tl M)))
                  (cons (rules.rs-prem S [not-tag V Tag])
                        (hd (tl (tl M))))]))))))
(define rules.match-constructor-normalized
  Tag Patterns V S ->
    (let C (rules.rs-c S)
      (let Fields (rules.make-fields Patterns C)
        (let D (rules.rs-prem S [decompose V Tag Fields])
          (let B (rules.add-fields D Fields)
            (let M (rules.match-patterns Patterns Fields B)
              [pm (hd (hd (tl M)))
                  (cons (rules.rs-prem S [not-tag V Tag])
                        (hd (tl (tl M))))]))))))
(define rules.make-fields
  [] _ -> []
  [_ | Ps] C -> [[v-var (rules.fresh "M" (+ C (length Ps)))] |
                 (rules.make-fields Ps C)])
(define rules.add-fields
  S [] -> S
  S [[v-var X] | Xs] ->
    (rules.add-fields (rules.rs-bound S [v-var X]) Xs)
  S [_ | Xs] -> (rules.add-fields S Xs))

\\ Expression compiler returns a list of states and is strict by recursive
\\ argument traversal.  Boolean expressions split into true/false paths.
(define rules.expr
  [e-var X] S Ns -> [(rules.rs-take S (rules.term X (rules.rs-e S)))]
  [e-value X] S _ -> [(rules.rs-take S (rules.term X (rules.rs-e S)))]
  [e-ctor Tag Args] S Ns -> (rules.constructor Tag Args S Ns)
  [e-call Op Args] S Ns -> (rules.call Op Args S Ns)
  [e-if C T F] S Ns -> (let B (rules.bool C S Ns)
                        (append (rules.expr-frontier T (hd (tl B)) Ns)
                                (rules.expr-frontier F (hd (tl (tl B))) Ns)))
  [e-let X A B] S Ns -> (rules.let-expr X A B S Ns)
  [e-and A B] S Ns -> (rules.app and [A B] S Ns)
  [e-or A B] S Ns -> (rules.app or [A B] S Ns)
  [e-prim Op Args] S Ns -> (rules.app Op Args S Ns)
  E S Names ->
    (if (variable? E) [(rules.rs-take S (rules.term E (rules.rs-e S)))]
        (if (or (number? E) (string? E) (= E true) (= E false))
            [(rules.rs-take S (rules.term E (rules.rs-e S)))]
        (if (cons? E) (rules.app (hd E) (tl E) S Names)
            [(rules.rs-take S (rules.term E (rules.rs-e S)))]))))

(define rules.app
  if [C T F] S Ns -> (let B (rules.bool C S Ns)
                      (append (rules.expr-frontier T (hd (tl B)) Ns)
                              (rules.expr-frontier F (hd (tl (tl B))) Ns)))
  let [X A B] S Ns -> (let Q (rules.expr A S Ns)
                        (rules.let-frontier X B Q Ns))
  and [A B] S Ns -> (let Q (rules.bool A S Ns)
                      (append (map (/. X (rules.rs-take X v-false))
                                   (hd (tl (tl Q))))
                              (rules.expr-frontier B (hd (tl Q)) Ns)))
  or [A B] S Ns -> (let Q (rules.bool A S Ns)
                     (append (map (/. X (rules.rs-take X v-true)) (hd (tl Q)))
                             (rules.expr-frontier B (hd (tl (tl Q))) Ns)))
  cons [A B] S Ns -> (rules.constructor cons [A B] S Ns)
  + [A B] S Ns -> (rules.int-expr + A B S Ns)
  - [A B] S Ns -> (rules.int-expr - A B S Ns)
  * [A B] S Ns -> (rules.int-expr * A B S Ns)
  = [A B] S Ns -> (rules.bool-expr = A B S Ns)
  neq [A B] S Ns -> (rules.bool-expr neq A B S Ns)
  < [A B] S Ns -> (rules.bool-expr < A B S Ns)
  > [A B] S Ns -> (rules.bool-expr > A B S Ns)
  <= [A B] S Ns -> (rules.bool-expr <= A B S Ns)
  >= [A B] S Ns -> (rules.bool-expr >= A B S Ns)
  do Xs S Ns -> (rules.do-expr Xs S Ns)
  Op Args S Ns -> (if (element? Op Ns)
                       (rules.call Op Args S Ns)
                       (rules.constructor Op Args S Ns)))

(define rules.expr-frontier
  _ [] _ -> []
  E [S | Ss] Ns -> (append (rules.expr E S Ns)
                          (rules.expr-frontier E Ss Ns)))

\\ Evaluate arguments left-to-right, retaining each argument term separately.
(define rules.eval-args
  Args S Ns -> (rules.eval-args-frontier Args [[S []]] Ns))
(define rules.eval-args-frontier
  [] Pairs _ -> Pairs
  [E | Es] Pairs Ns ->
    (rules.eval-args-frontier Es (rules.eval-arg E Pairs Ns) Ns))
(define rules.eval-arg
  _ [] _ -> []
  E [[S Ts] | Ps] Ns ->
    (append (rules.eval-arg-one E S Ts Ns)
            (rules.eval-arg E Ps Ns)))
(define rules.eval-arg-one
  E S Ts Ns -> (rules.eval-arg-states (rules.expr E S Ns) Ts))
(define rules.eval-arg-states
  [] _ -> []
  [S | Ss] Ts -> [[S (append Ts [(rules.rs-t S)])] |
                  (rules.eval-arg-states Ss Ts)])

(define rules.let-expr
  X A B S Ns -> (rules.let-frontier X B (rules.expr A S Ns) Ns))
(define rules.let-frontier
  _ _ [] _ -> []
  X B [S | Ss] Ns -> (append (rules.expr B
                              (rules.rs-env S (cons [X (rules.rs-t S)]
                                                    (rules.rs-e S))) Ns)
                            (rules.let-frontier X B Ss Ns)))

(define rules.scalar
  + A B -> [i-add A B]
  - A B -> [i-sub A B]
  * A B -> [i-mul A B])
(define rules.int-expr
  Op A B S Ns ->
    (rules.int-pairs Op (rules.eval-args [A B] S Ns)))
(define rules.int-pairs
  _ [] -> []
  Op [Pair | Pairs] ->
    (append (rules.int-pair Op Pair) (rules.int-pairs Op Pairs)))
(define rules.int-pair
  Op [S [A B]] ->
    (rules.int-pair-first Op (rules.ensure-int A S) B))
(define rules.int-pair-first
  Op [int IA S] B -> (rules.int-pair-second Op IA (rules.ensure-int B S))
  _ not-int _ -> [])
(define rules.int-pair-second
  Op IA [int IB S] ->
    [(rules.rs-take S [v-int (rules.scalar Op IA IB)])]
  _ _ not-int -> [])
(define rules.ensure-int
  [v-int I] S -> [int I S]
  [v-var X] S ->
    [int [i-var X]
         (rules.rs-bound
           (rules.rs-prem S [value-eq [v-var X] [v-int [i-var X]]])
           [i-var X])]
  _ _ -> not-int)
(define rules.bool-expr
  Op A B S Ns -> (let Q (rules.bool [Op A B] S Ns)
                  (append (map (/. X (rules.rs-take X v-true)) (hd (tl Q)))
                          (map (/. X (rules.rs-take X v-false))
                               (hd (tl (tl Q)))))))

(define rules.bool
  true S _ -> [bool [S] []]
  false S _ -> [bool [] [S]]
  [e-value true] S _ -> [bool [S] []]
  [e-value false] S _ -> [bool [] [S]]
  [e-and A B] S Ns -> (rules.bool [and A B] S Ns)
  [e-or A B] S Ns -> (rules.bool [or A B] S Ns)
  [e-prim = [A B]] S Ns -> (rules.compare = A B S Ns)
  [e-prim neq [A B]] S Ns -> (rules.compare neq A B S Ns)
  [e-prim < [A B]] S Ns -> (rules.compare < A B S Ns)
  [e-prim > [A B]] S Ns -> (rules.compare > A B S Ns)
  [e-prim <= [A B]] S Ns -> (rules.compare <= A B S Ns)
  [e-prim >= [A B]] S Ns -> (rules.compare >= A B S Ns)
  [and A B] S Ns -> (let X (rules.bool A S Ns)
                     (let Y (rules.bool-list B (hd (tl X)) Ns)
                       [bool (hd (tl Y))
                             (append (hd (tl (tl X))) (hd (tl (tl Y))))]))
  [or A B] S Ns -> (let X (rules.bool A S Ns)
                    (let Y (rules.bool-list B (hd (tl (tl X))) Ns)
                      [bool (append (hd (tl X)) (hd (tl Y)))
                            (hd (tl (tl Y)))]))
  [= A B] S Ns -> (rules.compare = A B S Ns)
  [neq A B] S Ns -> (rules.compare neq A B S Ns)
  [< A B] S Ns -> (rules.compare < A B S Ns)
  [> A B] S Ns -> (rules.compare > A B S Ns)
  [<= A B] S Ns -> (rules.compare <= A B S Ns)
  [>= A B] S Ns -> (rules.compare >= A B S Ns)
  E S Ns -> (let Q (rules.expr E S Ns)
             (rules.bool-fan Q)))
(define rules.bool-list
  _ [] _ -> [bool [] []]
  E [S | Ss] Ns -> (let Q (rules.bool E S Ns)
                    (let R (rules.bool-list E Ss Ns)
                      [bool (append (hd (tl Q)) (hd (tl R)))
                            (append (hd (tl (tl Q))) (hd (tl (tl R))))])))
(define rules.bool-fan
  [] -> [bool [] []]
  [S | Ss] -> (let R (rules.bool-fan Ss)
               [bool (cons (rules.rs-prem S [value-eq (rules.rs-t S) v-true])
                           (hd (tl R)))
                     (cons (rules.rs-prem S [value-neq (rules.rs-t S) v-true])
                           (hd (tl (tl R))))]))
(define rules.compare
  Op A B S Ns ->
    (let Pairs (rules.eval-args [A B] S Ns)
      (let Both (rules.compare-pairs Op Pairs)
        [bool (rules.firsts Both) (rules.seconds Both)])))
(define rules.compare-pairs
  _ [] -> []
  Op [[S [A B]] | Ps] ->
    (if (or (= Op =) (= Op neq))
        [[(rules.rs-prem S (if (= Op =) [value-eq A B]
                              [value-neq A B]))
          (rules.rs-prem S (if (= Op =) [value-neq A B]
                              [value-eq A B]))] |
         (rules.compare-pairs Op Ps)]
        (let X (rules.ensure-int A S)
          (if (= X not-int)
              (rules.compare-pairs Op Ps)
              (let Y (rules.ensure-int B (hd (tl (tl X))))
                (if (= Y not-int)
                    (rules.compare-pairs Op Ps)
                    [[(rules.rs-prem (hd (tl (tl Y)))
                                      [int-test Op (hd (tl X)) (hd (tl Y))])
                      (rules.rs-prem (hd (tl (tl Y)))
                                      [int-test (rules.compare-negate Op)
                                                (hd (tl X)) (hd (tl Y))])] |
                     (rules.compare-pairs Op Ps)]))))))
(define rules.compare-negate
  < -> >=
  > -> <=
  <= -> >
  >= -> <)
(define rules.firsts
  [] -> []
  [[A _] | Xs] -> [A | (rules.firsts Xs)])
(define rules.seconds
  [] -> []
  [[_ B] | Xs] -> [B | (rules.seconds Xs)])

(define rules.call
  Op Args S Ns -> (rules.call-pairs Op (rules.eval-args Args S Ns)))
(define rules.call-pairs
  _ [] -> []
  Op [[S Ts] | Ps] ->
    [(rules.emit-call Op S Ts) | (rules.call-pairs Op Ps)])
(define rules.emit-call
  Op S Ts -> (let R (rules.fresh "R" (rules.rs-c S))
               (let Q (rules.rs-counter (rules.rs-bound S [v-var R])
                                        (+ (rules.rs-c S) 1))
                 (rules.rs-take (rules.rs-prem Q [call Op Ts [v-var R]])
                                 [v-var R]))))
(define rules.constructor
  Tag Args S Ns -> (rules.constructor-pairs Tag (rules.eval-args Args S Ns)))
(define rules.constructor-pairs
  _ [] -> []
  Tag [[S Ts] | Ps] ->
    [(rules.rs-take S [v-ctor Tag Ts]) |
     (rules.constructor-pairs Tag Ps)])
(define rules.list-expr
  Es S Ns -> (rules.expr (rules.list-node Es) S Ns))
(define rules.list-node
  [] -> [e-ctor nil []]
  [E | Es] -> [e-ctor cons [E (rules.list-node Es)]])
(define rules.do-expr
  [] S _ -> [(rules.rs-take S v-true)]
  [E] S Ns -> (rules.expr E S Ns)
  [E | Es] S Ns -> (rules.do-expr Es S Ns))

\\ Ordered clauses and explicit fallback paths.
(define rules.compile-definitions
  [] _ -> []
  [[definition Name _ Clauses Arity] | Ds] Ns ->
    (let Args (rules.args Name Arity 0)
      (let Start [rs [] (rules.arg-bounds Args) [] 0 v-true]
        (let Leaves (rules.clause-chain Name Clauses Args Start Ns)
          (if (> (length Leaves) 4096)
              (error [sl-rules-too-many-paths Name (length Leaves)])
              (append (rules.make-rules Name Leaves Args 0)
                      (rules.compile-definitions Ds Ns)))))))
(define rules.args
  _ 0 _ -> []
  N A I -> [(rules.fresh (cn (str N) "_a") I) |
            (rules.args N (- A 1) (+ I 1))])
(define rules.arg-bounds
  [] -> []
  [X | Xs] -> [[v-var X] | (rules.arg-bounds Xs)])
(define rules.clause-chain
  _ [] _ _ _ -> []
  Name [[clause I Ps G B] | Cs] Args S Ns ->
    (let M (rules.match-patterns Ps (rules.arg-terms Args) S)
      (let Good (rules.guard G (hd (hd (tl M))) Ns)
        (append (rules.leaves I (rules.expr-frontier B (hd (tl Good)) Ns))
                (rules.clause-fallback Name Cs Args
                  (append (hd (tl (tl M))) (hd (tl (tl Good)))) Ns)))))
(define rules.arg-terms
  [] -> []
  [X | Xs] -> [[v-var X] | (rules.arg-terms Xs)])
(define rules.clause-fallback
  _ _ _ [] _ -> []
  Name Cs Args [S | Ss] Ns ->
    (append (rules.clause-chain Name Cs Args S Ns)
            (rules.clause-fallback Name Cs Args Ss Ns)))
(define rules.guard
  none S _ -> [guard [S] []]
  true S _ -> [guard [S] []]
  [some G] S Ns -> (rules.guard-expr G S Ns)
  G S Ns -> (rules.guard-expr G S Ns))
(define rules.guard-expr
  G S Ns -> (let B (rules.bool G S Ns)
             [guard (hd (tl B)) (hd (tl (tl B)))]))
(define rules.leaves
  _ [] -> []
  I [S | Ss] -> [[leaf I S] | (rules.leaves I Ss)])
(define rules.make-rules
  _ [] _ _ -> []
  Name [[leaf I S] | Ls] Args P ->
    (let Id (intern (cn (str Name) (cn "_c" (cn (str I) (cn "_p" (str P))))))
      [[rule Id Name I P (rules.arg-terms Args)
             (rules.unique (rules.rs-b S)) (rules.rs-p S) (rules.rs-t S)] |
       (rules.make-rules Name Ls Args (+ P 1))]))
(define rules.unique
  [] -> []
  [X | Xs] -> (if (element? X Xs) (rules.unique Xs) [X | (rules.unique Xs)]))

\\ Deterministic SCCs over raw source calls.
(define rules.sccs
  Definitions Names -> (rules.scc-list Names (rules.adjacency Definitions Names) []))
(define rules.adjacency
  [] _ -> []
  [[definition N _ Cs _] | Ds] Ns -> [[edge N (rules.calls Cs Ns)] |
                                         (rules.adjacency Ds Ns)])
(define rules.calls
  X Ns -> (rules.unique (rules.walk X Ns)))
(define rules.walk
  [] _ -> []
  [F | As] Ns -> (append (if (element? F Ns) [F] []) (rules.walk-list As Ns))
  _ _ -> [])
(define rules.walk-list
  [] _ -> []
  [X | Xs] Ns -> (append (rules.walk X Ns) (rules.walk-list Xs Ns)))
(define rules.scc-list
  [] _ A -> (reverse A)
  [N | Ns] Adj A -> (let F (rules.reach N Adj [])
                      (let R (rules.reach N (rules.rev Adj) [])
                        (let C (rules.inter F R)
                          (rules.scc-list (rules.minus Ns C) Adj [[scc C] | A])))))
(define rules.reach
  N Adj Seen -> (if (element? N Seen) Seen
                    (rules.reach-many (rules.neigh N Adj) Adj [N | Seen])))
(define rules.reach-many
  [] _ S -> S
  [N | Ns] A S -> (rules.reach-many Ns A (rules.reach N A S)))
(define rules.neigh
  _ [] -> []
  N [[edge N X] | _] -> X
  N [_ | Xs] -> (rules.neigh N Xs))
(define rules.rev
  [] -> []
  [[edge N _] | Xs] -> [[edge N (rules.pred N Xs)] | (rules.rev Xs)])
(define rules.pred
  _ [] -> []
  N [[edge M X] | Xs] -> (if (element? N X) [M | (rules.pred N Xs)]
                           (rules.pred N Xs)))
(define rules.inter
  [] _ -> []
  [X | Xs] Y -> (if (element? X Y) [X | (rules.inter Xs Y)] (rules.inter Xs Y)))
(define rules.minus
  [] _ -> []
  [X | Xs] Y -> (if (element? X Y) (rules.minus Xs Y) [X | (rules.minus Xs Y)]))
