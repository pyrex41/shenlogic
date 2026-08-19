\\ Canonical relational Rule IR.

(define rules.compile
  [program Definitions] ->
    (let Names (map (/. D (shenlogic.ast.definition-name D)) Definitions)
      [theory
        (rules.declarations Definitions)
        (rules.definitions Definitions Names)
        (rules.sccs Definitions Names)]))

(define rules.declarations
  [] -> []
  [[definition Name _ _ Arity] | Ds] ->
    [[relation Name (rules.sorts Arity) value] | (rules.declarations Ds)])

(define rules.sorts
  0 -> []
  N -> [value | (rules.sorts (- N 1))])

(define rules.definitions
  [] _ -> []
  [[definition Name _ Clauses Arity] | Ds] Names ->
    (append (rules.clauses Name Clauses Arity Names [] 0)
            (rules.definitions Ds Names)))

(define rules.clauses
  _ [] _ _ _ _ -> []
  Name [[clause Index Patterns Guard Body] | Cs] Arity Names Prior Counter ->
    (let Args (rules.args Name Arity 0)
      (let Matched (rules.patterns Patterns Args [] [] Args)
        (let Env (hd (tl Matched))
          (let PatternPremises (hd (tl (tl Matched)))
            (let Bound (hd (tl (tl (tl Matched))))
              (let Compiled (rules.expr Body Names Env Counter)
                (let Term (hd (tl Compiled))
                  (let Calls (hd (tl (tl Compiled)))
                    (let MoreBound (hd (tl (tl (tl Compiled))))
                      (let Next (hd (tl (tl (tl (tl Compiled)))))
                        (let Guarded (rules.guard Guard Names Env Next)
                          (let GuardPremises (hd (tl Guarded))
                            (let GuardBound (hd (tl (tl Guarded)))
                              (let Next2 (hd (tl (tl (tl Guarded))))
                                (let Rule [rule
                                            (intern (cn (str Name) (cn "_" (str Index))))
                                            Name Args
                                            (rules.unique (append Args (append Bound (append MoreBound GuardBound))))
                                            (append (rules.priority Prior Args)
                                              (append PatternPremises
                                                (append GuardPremises Calls)))
                                            Term]
                                  [Rule | (rules.clauses Name Cs Arity Names
                                            [[clause Index Patterns Guard Body] | Prior]
                                            Next2)]))))))))))))))))

(define rules.args
  _ 0 _ -> []
  Name N I ->
    [(intern (cn (str Name) (cn "_a" (str I)))) |
      (rules.args Name (- N 1) (+ I 1))])

(define rules.patterns
  [] [] Env Premises Bound -> [state Env (reverse Premises) Bound]
  [P | Ps] [A | As] Env Premises Bound ->
    (let R (rules.pattern P A Env Premises Bound)
      (rules.patterns Ps As (hd (tl R)) (hd (tl (tl R)))
        (hd (tl (tl (tl R))))))
  _ _ Env Premises Bound -> [state Env [[invalid-pattern-arity] | Premises] Bound])

(define rules.pattern
  P A Env Premises Bound ->
    (if (= P _)
        [state Env Premises Bound]
        (if (variable? P)
            (let Found (rules.lookup P Env)
              (if (= Found not-found)
                  [state [[P A] | Env] Premises Bound]
                  [state Env [[= A (hd (tl Found))] | Premises] Bound]))
        (if (cons? P)
            (let Vars (rules.pattern-vars P [])
              [state (rules.bind-pattern-vars Vars Env)
                     [[match P A] | Premises]
                     (append Vars Bound)])
            [state Env [[= A P] | Premises] Bound]))))

(define rules.pattern-vars
  X Acc ->
    (if (= X _)
        Acc
        (if (variable? X)
            (if (element? X Acc) Acc [X | Acc])
            (if (cons? X) (rules.pattern-vars-list X Acc) Acc))))

(define rules.pattern-vars-list
  [] Acc -> Acc
  [X | Xs] Acc -> (rules.pattern-vars-list Xs (rules.pattern-vars X Acc)))

(define rules.bind-pattern-vars
  [] Env -> Env
  [X | Xs] Env ->
    (rules.bind-pattern-vars Xs
      (if (= (rules.lookup X Env) not-found) [[X X] | Env] Env)))

(define rules.guard
  none _ _ Counter -> [guarded [] [] Counter]
  [some G] Names Env Counter ->
    (let C (rules.expr G Names Env Counter)
      [guarded [[constraint (hd (tl C))] | (hd (tl (tl C)))]
               (hd (tl (tl (tl C))))
               (hd (tl (tl (tl (tl C)))))]))

(define rules.expr
  E Names Env Counter ->
    (if (variable? E)
        (let Found (rules.lookup E Env)
          [compiled (if (= Found not-found) E (hd (tl Found))) [] [] Counter])
        (if (cons? E)
            (rules.application (hd E) (tl E) Names Env Counter)
            [compiled E [] [] Counter])))

(define rules.application
  Op Args Names Env Counter ->
    (let Many (rules.expressions Args Names Env Counter [] [] [])
      (let Terms (hd (tl Many))
        (let Premises (hd (tl (tl Many)))
          (let Bound (hd (tl (tl (tl Many))))
            (let Next (hd (tl (tl (tl (tl Many)))))
              (if (element? Op Names)
                  (let Result (intern (cn "R" (str Next)))
                    [compiled Result
                      (append Premises [[call Op Terms Result]])
                      [Result | Bound] (+ Next 1)])
                  [compiled (rules.primitive Op Terms) Premises Bound Next])))))))

(define rules.expressions
  [] _ _ Counter RevTerms Premises Bound ->
    [many (reverse RevTerms) Premises Bound Counter]
  [E | Es] Names Env Counter RevTerms Premises Bound ->
    (let C (rules.expr E Names Env Counter)
      (rules.expressions Es Names Env
        (hd (tl (tl (tl (tl C)))))
        [(hd (tl C)) | RevTerms]
        (append Premises (hd (tl (tl C))))
        (append Bound (hd (tl (tl (tl C))))))))

(define rules.primitive
  + [A B] -> [add A B]
  - [A B] -> [sub A B]
  * [A B] -> [mul A B]
  = [A B] -> [eq A B]
  < [A B] -> [lt A B]
  > [A B] -> [gt A B]
  <= [A B] -> [le A B]
  >= [A B] -> [ge A B]
  if [C T F] -> [ite C T F]
  Op Args -> [app Op Args])

(define rules.priority
  [] _ -> []
  [C | Cs] Args -> (append (rules.exclusion C Args) (rules.priority Cs Args)))

(define rules.exclusion
  [clause Index [P] none _] [A] ->
    (if (or (= P _) (variable? P))
        [[constraint false]]
        (if (cons? P)
            [[not-applicable Index [P] [A] none]]
            [[!= A P]]))
  [clause Index Patterns none _] Args ->
    (if (rules.irrefutable-patterns? Patterns [])
        [[constraint false]]
        [[not-applicable Index Patterns Args none]])
  [clause Index Patterns Guard _] Args ->
    [[not-applicable Index Patterns Args Guard]])

(define rules.irrefutable-patterns?
  [] _ -> true
  [P | Ps] Seen ->
    (if (= P _)
        (rules.irrefutable-patterns? Ps Seen)
        (if (variable? P)
            (if (element? P Seen) false
                (rules.irrefutable-patterns? Ps [P | Seen]))
            false)))

(define rules.pattern-exclusion
  [] [] -> [[constraint false]]
  [P | Ps] [A | As] ->
    (if (or (= P _) (variable? P))
        (rules.pattern-exclusion Ps As)
        [[!= A P]])
  _ _ -> [[constraint true]])

(define rules.lookup
  _ [] -> not-found
  X [[X V] | _] -> [found V]
  X [_ | Rest] -> (rules.lookup X Rest))

(define rules.unique
  [] -> []
  [X | Xs] -> (if (element? X Xs) (rules.unique Xs)
                  [X | (rules.unique Xs)]))

\\ SCCs are computed from raw source calls so mutual recursion stays grouped.
(define rules.sccs
  Definitions Names ->
    (rules.scc-list Names (rules.adjacency Definitions Names) []))

(define rules.adjacency
  [] _ -> []
  [[definition Name _ Clauses _] | Ds] Names ->
    [[edge Name (rules.calls Clauses Names)] | (rules.adjacency Ds Names)])

(define rules.calls
  X Names -> (rules.unique (rules.calls-walk X Names)))

(define rules.calls-walk
  [] _ -> []
  [F | Args] Names ->
    (append (if (element? F Names) [F] [])
            (rules.calls-walk-list Args Names))
  _ _ -> [])

(define rules.calls-walk-list
  [] _ -> []
  [X | Xs] Names -> (append (rules.calls-walk X Names)
                            (rules.calls-walk-list Xs Names)))

(define rules.scc-list
  [] _ Acc -> (reverse Acc)
  [N | Ns] Adj Acc ->
    (let Forward (rules.reachable N Adj [])
      (let Reverse (rules.reachable N (rules.reverse Adj) [])
        (let Component (rules.intersection Forward Reverse)
          (rules.scc-list (rules.minus Ns Component) Adj
            [[scc Component] | Acc])))))

(define rules.reachable
  N Adj Seen ->
    (if (element? N Seen) Seen
        (rules.reachable-many (rules.neighbours N Adj) Adj [N | Seen])))

(define rules.reachable-many
  [] _ Seen -> Seen
  [N | Ns] Adj Seen ->
    (rules.reachable-many Ns Adj (rules.reachable N Adj Seen)))

(define rules.neighbours
  _ [] -> []
  N [[edge N Xs] | _] -> Xs
  N [_ | Es] -> (rules.neighbours N Es))

(define rules.reverse
  Adj -> (rules.reverse-nodes Adj Adj []))

(define rules.reverse-nodes
  [] _ Acc -> Acc
  [[edge N _] | Es] All Acc ->
    (rules.reverse-nodes Es All [[edge N (rules.predecessors N All)] | Acc]))

(define rules.predecessors
  _ [] -> []
  N [[edge F Xs] | Es] ->
    (if (element? N Xs) [F | (rules.predecessors N Es)]
        (rules.predecessors N Es)))

(define rules.intersection
  [] _ -> []
  [X | Xs] Ys -> (if (element? X Ys) [X | (rules.intersection Xs Ys)]
                     (rules.intersection Xs Ys)))

(define rules.minus
  [] _ -> []
  [X | Xs] Ys -> (if (element? X Ys) (rules.minus Xs Ys)
                     [X | (rules.minus Xs Ys)]))
