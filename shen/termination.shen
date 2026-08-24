\\ Conservative totality classifier for the tsl backend.
\\
\\ (termination.classify Program) over the normalized program returns
\\ [totality [[Name Status Reason] ...]] in definition order, where Status
\\ is total or unknown.  The classifier is sound only under the typed
\\ reading established by tsl.type-program: guards are total because they
\\ are user-call-free (sl-v023) and well-typed, and (list T) is inhabited by
\\ proper lists only, so nil/cons case analysis is exhaustive.
\\
\\ An SCC is total iff every member is exhaustive, every callee outside the
\\ SCC is already total, and all in-SCC calls share a descent scheme:
\\ structural descent at one position, lexicographic structural descent at
\\ two positions (self-recursion only), or an integer measure with a
\\ guard-derived lower bound.  Anything else stays unknown.

(define termination.classify
  [program Defs] ->
    (let Names (map (/. D (shenlogic.ast.definition-name D)) Defs)
      (let Sccs (termination.sccs Names (termination.adjacency Defs Names))
        [totality (termination.report Names
                    (termination.fixpoint Defs Sccs
                      (termination.init Names) (+ (length Sccs) 1)))]))
  _ -> [totality []])

(define termination.init
  [] -> []
  [N | Ns] -> [[N unknown [unclassified]] | (termination.init Ns)])

(define termination.report
  [] _ -> []
  [N | Ns] Statuses ->
    (let F (tsl.env-lookup N Statuses)
      [[N (hd (hd (tl F))) (hd (tl (hd (tl F))))] |
       (termination.report Ns Statuses)]))

(define termination.total?
  N Statuses -> (let F (tsl.env-lookup N Statuses)
                  (if (= F not-found) false (= (hd (hd (tl F))) total))))

(define termination.fixpoint
  _ _ Statuses 0 -> Statuses
  Defs Sccs Statuses Fuel ->
    (let Next (termination.pass Defs Sccs Statuses)
      (if (= Next Statuses)
          Statuses
          (termination.fixpoint Defs Sccs Next (- Fuel 1)))))

(define termination.pass
  _ [] Statuses -> Statuses
  Defs [[scc C] | Sccs] Statuses ->
    (termination.pass Defs Sccs
      (if (termination.all-total? C Statuses)
          Statuses
          (termination.update C (termination.try-scc C Defs Statuses)
            Statuses))))

(define termination.all-total?
  [] _ -> true
  [N | Ns] Statuses -> (if (termination.total? N Statuses)
                           (termination.all-total? Ns Statuses)
                           false))

(define termination.update
  [] _ Statuses -> Statuses
  [N | Ns] Verdict Statuses ->
    (termination.update Ns Verdict
      (termination.store N
        (if (= (hd Verdict) ok)
            [total (hd (tl Verdict))]
            [unknown (hd (tl Verdict))])
        Statuses)))

(define termination.store
  N Entry [] -> [[N Entry]]
  N Entry [[N _] | Rest] -> [[N Entry] | Rest]
  N Entry [S | Rest] -> [S | (termination.store N Entry Rest)])

\\ --- SCC verdict ---------------------------------------------------------

(define termination.try-scc
  C Defs Statuses ->
    (let Members (termination.defs-in C Defs)
      (let Ex (termination.first-unexhaustive Members)
        (if (not (= Ex none))
            [fail [non-exhaustive (hd (tl Ex))]]
            (let Out (termination.first-unready-callee Members C Statuses)
              (if (not (= Out none))
                  [fail [callee (hd (tl Out))]]
                  (let Sites (termination.scc-sites Members C)
                    (if (= Sites [])
                        [ok [non-recursive]]
                        (let Scheme (termination.scheme Sites
                                      (termination.min-arity Members)
                                      (= (length C) 1))
                          (if (= Scheme none)
                              [fail [no-descent]]
                              [ok Scheme]))))))))))

(define termination.defs-in
  _ [] -> []
  C [[definition N Sig Cs A] | Ds] ->
    (if (element? N C)
        [[definition N Sig Cs A] | (termination.defs-in C Ds)]
        (termination.defs-in C Ds)))

(define termination.min-arity
  [[definition _ _ _ A]] -> A
  [[definition _ _ _ A] | Ds] ->
    (let Rest (termination.min-arity Ds)
      (if (< A Rest) A Rest)))

\\ --- exhaustiveness ------------------------------------------------------

(define termination.first-unexhaustive
  [] -> none
  [[definition N Sig Cs A] | Ds] ->
    (if (termination.exhaustive? Sig Cs A)
        (termination.first-unexhaustive Ds)
        [found N]))

(define termination.exhaustive?
  Sig Clauses Arity ->
    (if (termination.catch-all? Clauses)
        true
        (termination.signature-cover? Sig Clauses 0 Arity)))

(define termination.catch-all?
  [] -> false
  [[clause _ Ps none _] | Cs] ->
    (if (termination.all-vars? Ps) true (termination.catch-all? Cs))
  [_ | Cs] -> (termination.catch-all? Cs))

(define termination.all-vars?
  [] -> true
  [[p-var _] | Ps] -> (termination.all-vars? Ps)
  [[p-wild] | Ps] -> (termination.all-vars? Ps)
  _ -> false)

(define termination.signature-cover?
  _ _ I Arity -> false where (>= I Arity)
  [signature Args R] Clauses I Arity ->
    (if (termination.covered-at? (termination.nth Args I) Clauses I)
        true
        (termination.signature-cover? [signature Args R] Clauses
          (+ I 1) Arity))
  _ _ _ _ -> false)

\\ Coverage at one position: two unguarded clauses that are fully general
\\ everywhere else and jointly cover the position's sort.
(define termination.covered-at?
  [list _] Clauses I ->
    (and (termination.clause-covering? Clauses I nil)
         (termination.clause-covering? Clauses I cons))
  boolean Clauses I ->
    (and (termination.clause-covering? Clauses I true)
         (termination.clause-covering? Clauses I false))
  _ _ _ -> false)

(define termination.clause-covering?
  [] _ _ -> false
  [[clause _ Ps none _] | Cs] I Want ->
    (if (and (termination.covers? (termination.nth Ps I) Want)
             (termination.all-vars? (termination.except Ps I)))
        true
        (termination.clause-covering? Cs I Want))
  [_ | Cs] I Want -> (termination.clause-covering? Cs I Want))

(define termination.covers?
  [p-ctor nil []] nil -> true
  [p-ctor cons Fs] cons -> (termination.all-vars? Fs)
  [p-lit true] true -> true
  [p-lit false] false -> true
  _ _ -> false)

(define termination.nth
  [X | _] 0 -> X
  [_ | Xs] I -> (termination.nth Xs (- I 1)))

(define termination.except
  [] _ -> []
  [_ | Xs] 0 -> Xs
  [X | Xs] I -> [X | (termination.except Xs (- I 1))])

\\ --- call graph ----------------------------------------------------------

(define termination.adjacency
  [] _ -> []
  [[definition N _ Cs _] | Ds] Names ->
    [[edge N (termination.unique
               (termination.ops (termination.clauses-sites Cs) Names))] |
     (termination.adjacency Ds Names)])

(define termination.ops
  [] _ -> []
  [[rec-call _ _ Op _] | Ss] Names ->
    (append (if (element? Op Names) [Op] []) (termination.ops Ss Names)))

(define termination.unique
  [] -> []
  [X | Xs] -> (if (element? X Xs) (termination.unique Xs)
                  [X | (termination.unique Xs)]))

(define termination.clauses-sites
  [] -> []
  [[clause _ Ps G B] | Cs] ->
    (append (termination.sites Ps G (append (termination.guard-expr-list G)
                                            [B]))
            (termination.clauses-sites Cs)))

(define termination.guard-expr-list
  none -> []
  [some G] -> [G]
  G -> [G])

(define termination.sites
  _ _ [] -> []
  Ps G [E | Es] ->
    (append (termination.expr-sites Ps G E) (termination.sites Ps G Es)))

(define termination.expr-sites
  Ps G [e-call Op Args] ->
    [[rec-call Ps G Op Args] | (termination.sites Ps G Args)]
  Ps G [e-ctor _ Args] -> (termination.sites Ps G Args)
  Ps G [e-prim _ Args] -> (termination.sites Ps G Args)
  Ps G [e-if C T F] -> (termination.sites Ps G [C T F])
  Ps G [e-let _ A B] -> (termination.sites Ps G [A B])
  Ps G [e-and A B] -> (termination.sites Ps G [A B])
  Ps G [e-or A B] -> (termination.sites Ps G [A B])
  _ _ _ -> [])

(define termination.scc-sites
  [] _ -> []
  [[definition _ _ Cs _] | Ds] C ->
    (append (termination.in-scc (termination.clauses-sites Cs) C)
            (termination.scc-sites Ds C)))

(define termination.in-scc
  [] _ -> []
  [[rec-call Ps G Op Args] | Ss] C ->
    (if (element? Op C)
        [[rec-call Ps G Op Args] | (termination.in-scc Ss C)]
        (termination.in-scc Ss C)))

(define termination.first-unready-callee
  [] _ _ -> none
  [[definition _ _ Cs _] | Ds] C Statuses ->
    (let Bad (termination.unready
               (termination.clauses-sites Cs) C Statuses)
      (if (= Bad none)
          (termination.first-unready-callee Ds C Statuses)
          Bad)))

(define termination.unready
  [] _ _ -> none
  [[rec-call _ _ Op _] | Ss] C Statuses ->
    (if (or (element? Op C) (termination.total? Op Statuses))
        (termination.unready Ss C Statuses)
        [found Op]))

\\ --- descent schemes -----------------------------------------------------

(define termination.scheme
  Sites MinA Single ->
    (let S (termination.scheme-single Sites 0 MinA)
      (if (= S none)
          (if Single (termination.scheme-lex Sites 0 0 MinA) none)
          S)))

(define termination.scheme-single
  _ I MinA -> none where (>= I MinA)
  Sites I MinA ->
    (if (termination.structural-at? Sites I)
        [structural I]
        (if (termination.int-at? Sites I)
            [int-measure I]
            (termination.scheme-single Sites (+ I 1) MinA))))

(define termination.scheme-lex
  _ I _ MinA -> none where (>= I MinA)
  Sites I J MinA ->
    (if (>= J MinA)
        (termination.scheme-lex Sites (+ I 1) 0 MinA)
        (if (and (not (= I J)) (termination.lex-at? Sites I J))
            [structural-lex I J]
            (termination.scheme-lex Sites I (+ J 1) MinA))))

(define termination.structural-at?
  [] _ -> true
  [[rec-call Ps _ _ Args] | Ss] I ->
    (if (termination.strict-arg? (termination.nth Args I)
          (termination.nth Ps I))
        (termination.structural-at? Ss I)
        false))

(define termination.strict-arg?
  [e-var V] [p-ctor _ Fs] -> (element? V (tsl.patterns-vars Fs))
  _ _ -> false)

(define termination.lex-at?
  [] _ _ -> true
  [[rec-call Ps G Op Args] | Ss] I J ->
    (if (or (termination.strict-arg? (termination.nth Args I)
              (termination.nth Ps I))
            (and (termination.same-arg? (termination.nth Args I)
                   (termination.nth Ps I))
                 (termination.strict-arg? (termination.nth Args J)
                   (termination.nth Ps J))))
        (termination.lex-at? Ss I J)
        false))

(define termination.same-arg?
  [e-var V] [p-var V] -> true
  _ _ -> false)

\\ Integer measure: every in-SCC call passes (- V k) with a positive literal
\\ k at a position whose caller pattern is the bare variable V, and the
\\ clause's own guard bounds V from below.  Exclusion-derived facts such as
\\ (~ (V = 0)) are deliberately not accepted: they give no lower bound.
(define termination.int-at?
  [] _ -> true
  [[rec-call Ps G _ Args] | Ss] I ->
    (if (termination.int-step? (termination.nth Args I)
          (termination.nth Ps I) G)
        (termination.int-at? Ss I)
        false))

(define termination.int-step?
  [e-prim - [[e-var V] [e-value K]]] [p-var V] G ->
    (if (and (integer? K) (> K 0))
        (termination.bound? G V)
        false)
  _ _ _ -> false)

(define termination.bound?
  none _ -> false
  [some G] V -> (termination.bound-conj? G V)
  G V -> (termination.bound-conj? G V))

(define termination.bound-conj?
  [e-and A B] V -> (if (termination.bound-conj? A V)
                       true
                       (termination.bound-conj? B V))
  [e-prim > [[e-var V] [e-value N]]] V -> (integer? N)
  [e-prim >= [[e-var V] [e-value N]]] V -> (integer? N)
  [e-prim < [[e-value N] [e-var V]]] V -> (integer? N)
  [e-prim <= [[e-value N] [e-var V]]] V -> (integer? N)
  _ _ -> false)

\\ --- SCC computation (correct predecessor edges) -------------------------

(define termination.sccs
  Names Adj -> (termination.scc-list Names Names Adj []))

(define termination.scc-list
  _ [] _ Acc -> (reverse Acc)
  Names [N | Ns] Adj Acc ->
    (let F (termination.reach [N] Adj [])
      (let B (termination.back-reach [N] Adj [])
        (let C (termination.ordered-members Names F B)
          (termination.scc-list Names (termination.minus Ns C) Adj
            [[scc C] | Acc])))))

(define termination.ordered-members
  [] _ _ -> []
  [X | Xs] F B ->
    (if (and (element? X F) (element? X B))
        [X | (termination.ordered-members Xs F B)]
        (termination.ordered-members Xs F B)))

(define termination.reach
  [] _ Seen -> Seen
  [N | Ns] Adj Seen ->
    (if (element? N Seen)
        (termination.reach Ns Adj Seen)
        (termination.reach (append (termination.neigh N Adj) Ns) Adj
          [N | Seen])))

(define termination.back-reach
  [] _ Seen -> Seen
  [N | Ns] Adj Seen ->
    (if (element? N Seen)
        (termination.back-reach Ns Adj Seen)
        (termination.back-reach (append (termination.preds N Adj) Ns) Adj
          [N | Seen])))

(define termination.neigh
  _ [] -> []
  N [[edge N X] | _] -> X
  N [_ | Es] -> (termination.neigh N Es))

(define termination.preds
  _ [] -> []
  N [[edge M X] | Es] ->
    (if (element? N X)
        [M | (termination.preds N Es)]
        (termination.preds N Es))
  N [_ | Es] -> (termination.preds N Es))

(define termination.minus
  [] _ -> []
  [X | Xs] Y -> (if (element? X Y)
                    (termination.minus Xs Y)
                    [X | (termination.minus Xs Y)]))
