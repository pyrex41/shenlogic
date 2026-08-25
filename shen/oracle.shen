\\ Differential typing oracle: Shen's own sequent-calculus type checker
\\ (System S, called exactly as Tarver's logic.shen calls it) cross-checks
\\ the tsl typing pass.  For each typed clause, the oracle asks System S
\\ whether the raw source body inhabits the declared result type under
\\ hypotheses giving every defined function its curried signature and
\\ every pattern variable its inferred binding type.  Signature type
\\ variables are replaced by the reserved opaque tokens t/t1/t2/...
\\ (Tarver's schematic-generality move); uppercase variables are never
\\ passed to the Prolog side.  Agreement is evidence, not proof, that
\\ shen/typing.shen matches System S; a disagreement is reported, never
\\ repaired silently.
\\
\\ Scope: definitions whose signatures and clauses stay inside System S's
\\ native vocabulary -- number/boolean/symbol/string, (list T), type
\\ variables, and arrow argument types.  Definitions using the value sort
\\ or user constructors are counted as skipped (System S has no datatype
\\ declarations for them here).

(define oracle.call-system-S
  Hyps [X : A] -> (prolog? (shen.system-S [(shen.curry (receive X)) : (receive A)] (receive Hyps))))

(define shenlogic.oracle-file
  File ->
    (let Source (shenlogic.source-program File)
      (let Program (shenlogic.ast.normalize-program Source)
        (let TR (tsl.type-program Program)
          (if (tsl.ok? TR)
              (oracle.check-defs (hd (tl TR))
                (shenlogic.ast.program-definitions Source)
                (oracle.fun-hyps (hd (tl TR)))
                0 0)
              (tsl.render-error TR))))))

(define oracle.check-defs
  [] _ _ Agreed Skipped -> [ok Agreed Skipped]
  [[t-def Name TVars Args Result TCs] | Ds] Raw FunHyps Agreed Skipped ->
    (if (oracle.in-scope? Args Result TCs)
        (let R (oracle.check-clauses Name TCs
                 (oracle.raw-clauses Name Raw)
                 (oracle.tokenize Result (oracle.token-map TVars))
                 (oracle.token-map TVars) FunHyps 0)
          (if (= (hd R) ok)
              (oracle.check-defs Ds Raw FunHyps (+ Agreed (hd (tl R)))
                Skipped)
              R))
        (oracle.check-defs Ds Raw FunHyps Agreed (+ Skipped 1))))

(define oracle.raw-clauses
  _ [] -> []
  Name [[definition Name _ Clauses _] | _] -> Clauses
  Name [_ | Ds] -> (oracle.raw-clauses Name Ds))

\\ One hypothesis per defined function at its curried, tokenized signature.
(define oracle.fun-hyps
  [] -> []
  [[t-def Name TVars Args Result _] | Ds] ->
    [[Name : (oracle.curry (map (/. T (oracle.tokenize T
                                        (oracle.token-map TVars))) Args)
               (oracle.tokenize Result (oracle.token-map TVars)))] |
     (oracle.fun-hyps Ds)])

(define oracle.curry
  [] Result -> Result
  [T | Ts] Result -> [T --> (oracle.curry Ts Result)])

\\ Reserved opaque type tokens, in Tarver's spelling.
(define oracle.token-map
  TVars -> (oracle.token-map-h TVars 0))

(define oracle.token-map-h
  [] _ -> []
  [V | Vs] 0 -> [[V (intern "t")] | (oracle.token-map-h Vs 1)]
  [V | Vs] N -> [[V (intern (cn "t" (str N)))] | (oracle.token-map-h Vs (+ N 1))])

(define oracle.tokenize
  [list T] Map -> [list (oracle.tokenize T Map)]
  [arrow As R] Map -> (oracle.curry (map (/. T (oracle.tokenize T Map)) As)
                        (oracle.tokenize R Map))
  T Map -> (if (variable? T)
               (let F (tsl.env-lookup T Map)
                 (if (= F not-found) (intern "t") (hd (tl F))))
               T))

(define oracle.in-scope?
  Args Result TCs ->
    (and (oracle.types-ok? [Result | Args])
         (oracle.tcs-ok? TCs)))

(define oracle.types-ok?
  [] -> true
  [T | Ts] -> (if (oracle.type-ok? T) (oracle.types-ok? Ts) false))

(define oracle.type-ok?
  [list T] -> (oracle.type-ok? T)
  [arrow As R] -> (oracle.types-ok? [R | As])
  value -> false
  T -> (if (cons? T) false true))

(define oracle.tcs-ok?
  [] -> true
  [[t-clause _ Ps _ _ Bindings] | TCs] ->
    (if (and (= (prove.patterns-user-ctor Ps) none)
             (oracle.types-ok? (map (/. B (hd (tl B))) Bindings)))
        (oracle.tcs-ok? TCs)
        false))

\\ A clause whose raw pattern variables are not all present in the typed
\\ bindings (tsl alpha-renames a pattern variable that collides with a
\\ signature type variable) is skipped, not reported: the hypotheses
\\ could not name the body's variables.
(define oracle.check-clauses
  _ [] _ _ _ _ N -> [ok N]
  Name [[t-clause I _ _ _ Bindings] | TCs] RawClauses Result Map FunHyps N ->
    (let Raw (oracle.raw-clause I RawClauses)
      (if (= Raw none)
          [error [sl-o001 oracle-missing-clause Name I]]
          (if (not (oracle.covers?
                     (shenlogic.validate.raw-vars-list
                       (oracle.raw-patterns (hd (tl Raw))))
                     (tsl.binding-names Bindings)))
              (oracle.check-clauses Name TCs RawClauses Result Map FunHyps N)
              (let Hyps (append (oracle.binding-hyps Bindings Map) FunHyps)
                (let BodyOk (oracle.call-system-S Hyps
                              [(oracle.raw-body (hd (tl Raw))) : Result])
                  (if BodyOk
                      (let GuardR (oracle.check-guard Name I
                                    (oracle.raw-guard (hd (tl Raw))) Hyps)
                        (if (= GuardR ok)
                            (oracle.check-clauses Name TCs RawClauses Result
                              Map FunHyps (+ N 1))
                            GuardR))
                      [error [sl-o002 oracle-disagrees Name I]]))))))
  Name [X | _] _ _ _ _ _ -> [error [sl-o001 oracle-missing-clause Name X]])

(define oracle.covers?
  [] _ -> true
  [V | Vs] Names -> (if (element? V Names) (oracle.covers? Vs Names) false))

(define oracle.raw-patterns [clause _ Ps _ _] -> Ps)

(define oracle.raw-clause
  _ [] -> none
  I [[clause I Ps G B] | _] -> [found [clause I Ps G B]]
  I [_ | Cs] -> (oracle.raw-clause I Cs))

(define oracle.raw-body [clause _ _ _ B] -> B)
(define oracle.raw-guard [clause _ _ G _] -> G)

(define oracle.binding-hyps
  [] _ -> []
  [[V T] | Bs] Map -> [[V : (oracle.tokenize T Map)] |
                       (oracle.binding-hyps Bs Map)])

(define oracle.check-guard
  _ _ none _ -> ok
  Name I [some G] Hyps ->
    (if (oracle.call-system-S Hyps [G : boolean])
        ok
        [error [sl-o002 oracle-disagrees Name I]])
  Name I G Hyps -> (oracle.check-guard Name I [some G] Hyps))
