\\ Typed reading of the normalized program for the tsl backend.
\\
\\ Types are: the rigid sorts number, boolean, symbol, string, value; the
\\ former [list T]; signature type variables (raw Shen variables, rigid in
\\ their own definition, instantiated fresh at call sites); and unification
\\ variables [tv N].  User constructors are monomorphic at value.
\\
\\ The pass returns [ok [t-def ...]] or [error [sl-t00N ...]].  Each
\\ [t-def Name TVars ArgTypes Result TClauses] carries
\\ [t-clause Index Patterns Guard Body Bindings] clauses whose wildcards
\\ have been renamed to fresh variables and whose Bindings list every
\\ pattern variable with its resolved type in first-occurrence order.

(define tsl.type-program
  [program Definitions] ->
    (tsl.type-definitions Definitions
      (tsl.signature-table Definitions) [])
  X -> [error [sl-t005 tsl-unsupported program X]])

(define tsl.signature-table
  [] -> []
  [[definition Name Sig _ _] | Ds] ->
    [[Name Sig] | (tsl.signature-table Ds)])

(define tsl.type-definitions
  [] _ Acc -> [ok (reverse Acc)]
  [D | Ds] Table Acc ->
    (let R (tsl.type-definition D Table)
      (if (tsl.ok? R)
          (tsl.type-definitions Ds Table [(hd (tl R)) | Acc])
          R)))

(define tsl.type-definition
  [definition Name none _ _] _ -> [error [sl-t001 tsl-signature-required Name]]
  [definition Name [signature Args Result] Clauses _] Table ->
    (if (or (tsl.arrow-type? Result) (tsl.nested-arrow? Args))
        [error [sl-t002 tsl-higher-order-type Name Result]]
        (let IArgs (map (/. T (tsl.internal-type T)) Args)
          (let IResult (tsl.internal-type Result)
            (let Bad (tsl.first-illformed [IResult | IArgs])
              (if (not (= Bad none))
                  [error [sl-t005 tsl-unsupported Name [type (hd (tl Bad))]]]
                  (let TCs (tsl.type-clauses Name Clauses IArgs IResult
                             Table [])
                    (if (tsl.ok? TCs)
                        [ok [t-def Name (tsl.tvars-list IArgs [IResult])
                             IArgs IResult (hd (tl TCs))]]
                        TCs)))))))
  [definition Name _ _ _] _ -> [error [sl-t001 tsl-signature-required Name]])

\\ Rank-1 only: an argument may itself be an arrow type, but no arrow may
\\ appear inside an arrow's components or under a type former.
(define tsl.nested-arrow?
  [] -> false
  [T | Ts] ->
    (if (if (shenlogic.ast.arrow-type? T)
            (tsl.any-arrow-deep?
              (append (shenlogic.ast.arrow-args T)
                      [(shenlogic.ast.arrow-result T)]))
            (tsl.arrow-deep? T))
        true
        (tsl.nested-arrow? Ts)))

(define tsl.any-arrow-deep?
  [] -> false
  [T | Ts] -> (if (tsl.arrow-deep? T) true (tsl.any-arrow-deep? Ts)))

(define tsl.arrow-deep?
  T -> (if (cons? T) (tsl.arrow-elements? T) false))

\\ Internal representation: raw arrow lists become [arrow ArgTypes Result].
(define tsl.internal-type
  [list T] -> [list (tsl.internal-type T)]
  T -> (if (shenlogic.ast.arrow-type? T)
           [arrow (map (/. U (tsl.internal-type U))
                       (shenlogic.ast.arrow-args T))
                  (tsl.internal-type (shenlogic.ast.arrow-result T))]
           T))

(define tsl.ok?
  [ok | _] -> true
  _ -> false)

\\ Deep arrow detection over raw signature types.  Part B of the workflow
\\ relaxes this for argument positions; until then any arrow is rejected.
(define tsl.first-arrow
  [] -> none
  [T | Ts] -> (if (tsl.arrow-type? T) [found T] (tsl.first-arrow Ts)))

(define tsl.arrow-type?
  T -> (if (cons? T) (tsl.arrow-elements? T) false))

(define tsl.arrow-elements?
  [] -> false
  [X | Xs] -> (if (shenlogic.ast.atom-spelling? X "-->")
                  true
                  (if (tsl.arrow-type? X) true (tsl.arrow-elements? Xs))))

(define tsl.first-illformed
  [] -> none
  [T | Ts] -> (if (tsl.wellformed-type? T)
                  (tsl.first-illformed Ts)
                  [found T]))

(define tsl.wellformed-type?
  [list T] -> (tsl.wellformed-type? T)
  [arrow Args Result] -> (if (tsl.wellformed-types? Args)
                             (tsl.wellformed-type? Result)
                             false)
  T -> (if (cons? T)
           false
           (if (variable? T)
               true
               (element? T [number boolean symbol string value]))))

(define tsl.wellformed-types?
  [] -> true
  [T | Ts] -> (if (tsl.wellformed-type? T) (tsl.wellformed-types? Ts) false))

(define tsl.tvars-list
  Args Rest -> (tsl.tvars-collect (append Args Rest) []))

(define tsl.tvars-collect
  [] Acc -> (reverse Acc)
  [T | Ts] Acc -> (tsl.tvars-collect Ts (tsl.tvars-type T Acc)))

(define tsl.tvars-type
  [list T] Acc -> (tsl.tvars-type T Acc)
  [arrow Args Result] Acc ->
    (tsl.tvars-type Result (tsl.tvars-types Args Acc))
  T Acc -> (if (and (variable? T) (not (element? T Acc)))
               [T | Acc]
               Acc))

(define tsl.tvars-types
  [] Acc -> Acc
  [T | Ts] Acc -> (tsl.tvars-types Ts (tsl.tvars-type T Acc)))

(define tsl.type-clauses
  _ [] _ _ _ Acc -> [ok (reverse Acc)]
  Name [C | Cs] Args Result Table Acc ->
    (let R (tsl.type-clause Name C Args Result Table)
      (if (tsl.ok? R)
          (tsl.type-clauses Name Cs Args Result Table [(hd (tl R)) | Acc])
          R)))

(define tsl.type-clause
  Name [clause Index Patterns Guard Body] Args Result Table ->
    (let Used (append (tsl.patterns-vars Patterns)
                (append (tsl.guard-vars Guard) (tsl.expr-vars Body)))
      (let FP (tsl.freshen-list Patterns Used 0)
        (let Ctx [Name Index]
          (let RP (tsl.type-patterns (hd FP) Args [] [] 0 Ctx)
            (if (tsl.ok? RP)
                (let Env (hd (tl RP))
                  (let RG (tsl.type-guard Guard Env Table
                            (hd (tl (tl RP))) (hd (tl (tl (tl RP)))) Ctx)
                    (if (tsl.ok? RG)
                        (let RB (tsl.type-check Body Result Env Table
                                  (hd (tl RG)) (hd (tl (tl RG))) Ctx)
                          (if (tsl.ok? RB)
                              [ok [t-clause Index (hd FP) Guard Body
                                   (tsl.resolve-env (reverse Env) (hd (tl RB)))]]
                              RB))
                        RG)))
                RP))))))

\\ --- wildcard freshening -------------------------------------------------

(define tsl.freshen-list
  [] _ Counter -> [[] Counter]
  [P | Ps] Used Counter ->
    (let R (tsl.freshen P Used Counter)
      (let Rs (tsl.freshen-list Ps Used (hd (tl R)))
        [[(hd R) | (hd Rs)] (hd (tl Rs))])))

(define tsl.freshen
  [p-wild] Used Counter ->
    (let W (tsl.wild-name Used Counter)
      [[p-var (hd W)] (hd (tl W))])
  [p-ctor Tag Ps] Used Counter ->
    (let R (tsl.freshen-list Ps Used Counter)
      [[p-ctor Tag (hd R)] (hd (tl R))])
  P _ Counter -> [P Counter])

(define tsl.wild-name
  Used Counter ->
    (let V (intern (cn "W" (str Counter)))
      (if (element? V Used)
          (tsl.wild-name Used (+ Counter 1))
          [V (+ Counter 1)])))

(define tsl.patterns-vars
  [] -> []
  [P | Ps] -> (append (tsl.pattern-vars P) (tsl.patterns-vars Ps)))

(define tsl.pattern-vars
  [p-var X] -> [X]
  [p-ctor _ Ps] -> (tsl.patterns-vars Ps)
  _ -> [])

(define tsl.guard-vars
  none -> []
  [some G] -> (tsl.expr-vars G)
  G -> (tsl.expr-vars G))

(define tsl.expr-vars
  [e-var X] -> [X]
  [e-let X A B] -> [X | (append (tsl.expr-vars A) (tsl.expr-vars B))]
  [e-ctor _ Args] -> (tsl.exprs-vars Args)
  [e-call _ Args] -> (tsl.exprs-vars Args)
  [e-apply F Args] -> [F | (tsl.exprs-vars Args)]
  [e-prim _ Args] -> (tsl.exprs-vars Args)
  [e-if C T F] -> (append (tsl.expr-vars C)
                    (append (tsl.expr-vars T) (tsl.expr-vars F)))
  [e-and A B] -> (append (tsl.expr-vars A) (tsl.expr-vars B))
  [e-or A B] -> (append (tsl.expr-vars A) (tsl.expr-vars B))
  _ -> [])

(define tsl.exprs-vars
  [] -> []
  [E | Es] -> (append (tsl.expr-vars E) (tsl.exprs-vars Es)))

\\ --- pattern typing ------------------------------------------------------

(define tsl.type-patterns
  [] [] Env Subst Counter _ -> [ok Env Subst Counter]
  [P | Ps] [T | Ts] Env Subst Counter Ctx ->
    (let R (tsl.type-pattern P T Env Subst Counter Ctx)
      (if (tsl.ok? R)
          (tsl.type-patterns Ps Ts (hd (tl R)) (hd (tl (tl R)))
            (hd (tl (tl (tl R)))) Ctx)
          R))
  _ _ _ _ _ Ctx ->
    [error [sl-t005 tsl-unsupported (hd Ctx) [pattern-arity (hd (tl Ctx))]]])

(define tsl.type-pattern
  [p-var X] T Env Subst Counter Ctx ->
    (let Old (tsl.env-lookup X Env)
      (if (= Old not-found)
          [ok [[X T] | Env] Subst Counter]
          (let U (tsl.unify (hd (tl Old)) T Subst)
            (if (tsl.ok? U)
                [ok Env (hd (tl U)) Counter]
                (tsl.pattern-error [p-var X] T Subst Ctx)))))
  [p-lit L] T Env Subst Counter Ctx ->
    (let U (tsl.unify T (tsl.literal-type L) Subst)
      (if (tsl.ok? U)
          [ok Env (hd (tl U)) Counter]
          (tsl.pattern-error [p-lit L] T Subst Ctx)))
  [p-ctor nil []] T Env Subst Counter Ctx ->
    (let U (tsl.unify T [list [tv Counter]] Subst)
      (if (tsl.ok? U)
          [ok Env (hd (tl U)) (+ Counter 1)]
          (tsl.pattern-error [p-ctor nil []] T Subst Ctx)))
  [p-ctor cons [H Tl]] T Env Subst Counter Ctx ->
    (let F [tv Counter]
      (let U (tsl.unify T [list F] Subst)
        (if (tsl.ok? U)
            (let RH (tsl.type-pattern H F Env (hd (tl U)) (+ Counter 1) Ctx)
              (if (tsl.ok? RH)
                  (tsl.type-pattern Tl [list F] (hd (tl RH))
                    (hd (tl (tl RH))) (hd (tl (tl (tl RH)))) Ctx)
                  RH))
            (tsl.pattern-error [p-ctor cons [H Tl]] T Subst Ctx))))
  [p-ctor Tag Ps] T Env Subst Counter Ctx ->
    (let U (tsl.unify T value Subst)
      (if (tsl.ok? U)
          (tsl.type-pattern-fields Ps Env (hd (tl U)) Counter Ctx)
          (tsl.pattern-error [p-ctor Tag Ps] T Subst Ctx)))
  P T Env Subst Counter Ctx -> (tsl.pattern-error P T Subst Ctx))

(define tsl.type-pattern-fields
  [] Env Subst Counter _ -> [ok Env Subst Counter]
  [P | Ps] Env Subst Counter Ctx ->
    (let R (tsl.type-pattern P value Env Subst Counter Ctx)
      (if (tsl.ok? R)
          (tsl.type-pattern-fields Ps (hd (tl R)) (hd (tl (tl R)))
            (hd (tl (tl (tl R)))) Ctx)
          R)))

(define tsl.pattern-error
  P T Subst [Name Index] ->
    [error [sl-t003 tsl-pattern-type Name Index P (tsl.resolve T Subst)]])

(define tsl.literal-type
  L -> (if (number? L)
           number
           (if (string? L)
               string
               (if (element? L [true false]) boolean symbol))))

\\ --- expression typing ---------------------------------------------------

\\ Returns [ok Type Subst Counter] or an error.
(define tsl.type-expr
  [e-var X] Env _ Subst Counter Ctx ->
    (let F (tsl.env-lookup X Env)
      (if (= F not-found)
          [error [sl-t005 tsl-unsupported (hd Ctx) [unbound X (hd (tl Ctx))]]]
          [ok (hd (tl F)) Subst Counter]))
  [e-value X] _ _ Subst Counter _ ->
    [ok (tsl.literal-type X) Subst Counter]
  [e-ctor nil []] _ _ Subst Counter _ ->
    [ok [list [tv Counter]] Subst (+ Counter 1)]
  [e-ctor cons [H Tl]] Env Table Subst Counter Ctx ->
    (let F [tv Counter]
      (let RH (tsl.type-check H F Env Table Subst (+ Counter 1) Ctx)
        (if (tsl.ok? RH)
            (let RT (tsl.type-check Tl [list F] Env Table
                      (hd (tl RH)) (hd (tl (tl RH))) Ctx)
              (if (tsl.ok? RT)
                  [ok [list F] (hd (tl RT)) (hd (tl (tl RT)))]
                  RT))
            RH)))
  [e-ctor Tag Args] Env Table Subst Counter Ctx ->
    (let R (tsl.type-checks Args (tsl.value-types Args) Env Table
             Subst Counter Ctx)
      (if (tsl.ok? R)
          [ok value (hd (tl R)) (hd (tl (tl R)))]
          R))
  [e-call F Args] Env Table Subst Counter Ctx ->
    (let Sig (tsl.env-lookup F Table)
      (if (= Sig not-found)
          [error [sl-t005 tsl-unsupported (hd Ctx) [unknown-call F]]]
          (if (= (hd (tl Sig)) none)
              [error [sl-t001 tsl-signature-required F]]
              (let Inst (tsl.instantiate (hd (tl Sig)) Counter)
                (if (= (length Args) (length (hd Inst)))
                    (let R (tsl.type-checks Args (hd Inst) Env Table Subst
                             (hd (tl (tl Inst))) Ctx)
                      (if (tsl.ok? R)
                          [ok (hd (tl Inst)) (hd (tl R)) (hd (tl (tl R)))]
                          R))
                    [error [sl-t005 tsl-unsupported (hd Ctx)
                            [call-arity F]]])))))
  [e-apply F Args] Env Table Subst Counter Ctx ->
    (let TF (tsl.env-lookup F Env)
      (if (= TF not-found)
          [error [sl-t005 tsl-unsupported (hd Ctx) [unbound F]]]
          (let RT (tsl.resolve (hd (tl TF)) Subst)
            (if (= (hd RT) arrow)
                (if (= (length Args) (length (hd (tl RT))))
                    (let R (tsl.type-checks Args (hd (tl RT)) Env Table
                             Subst Counter Ctx)
                      (if (tsl.ok? R)
                          [ok (hd (tl (tl RT))) (hd (tl R)) (hd (tl (tl R)))]
                          R))
                    [error [sl-t005 tsl-unsupported (hd Ctx)
                            [apply-arity F]]])
                [error [sl-t004 tsl-type-mismatch (hd Ctx) (hd (tl Ctx))
                        arrow RT]]))))
  [e-prim Op Args] Env Table Subst Counter Ctx ->
    (tsl.type-prim Op Args Env Table Subst Counter Ctx)
  [e-if C T F] Env Table Subst Counter Ctx ->
    (let RC (tsl.type-check C boolean Env Table Subst Counter Ctx)
      (if (tsl.ok? RC)
          (let RT (tsl.type-expr T Env Table (hd (tl RC))
                    (hd (tl (tl RC))) Ctx)
            (if (tsl.ok? RT)
                (let RF (tsl.type-check F (hd (tl RT)) Env Table
                          (hd (tl (tl RT))) (hd (tl (tl (tl RT)))) Ctx)
                  (if (tsl.ok? RF)
                      [ok (hd (tl RT)) (hd (tl RF)) (hd (tl (tl RF)))]
                      RF))
                RT))
          RC))
  [e-let X A B] Env Table Subst Counter Ctx ->
    (let RA (tsl.type-expr A Env Table Subst Counter Ctx)
      (if (tsl.ok? RA)
          (tsl.type-expr B [[X (hd (tl RA))] | Env] Table
            (hd (tl (tl RA))) (hd (tl (tl (tl RA)))) Ctx)
          RA))
  [e-and A B] Env Table Subst Counter Ctx ->
    (tsl.type-connective A B Env Table Subst Counter Ctx)
  [e-or A B] Env Table Subst Counter Ctx ->
    (tsl.type-connective A B Env Table Subst Counter Ctx)
  E _ _ _ _ Ctx ->
    [error [sl-t005 tsl-unsupported (hd Ctx) [expression E]]])

(define tsl.type-connective
  A B Env Table Subst Counter Ctx ->
    (let RA (tsl.type-check A boolean Env Table Subst Counter Ctx)
      (if (tsl.ok? RA)
          (let RB (tsl.type-check B boolean Env Table (hd (tl RA))
                    (hd (tl (tl RA))) Ctx)
            (if (tsl.ok? RB)
                [ok boolean (hd (tl RB)) (hd (tl (tl RB)))]
                RB))
          RA)))

(define tsl.type-prim
  Op [A B] Env Table Subst Counter Ctx ->
    (if (element? Op [+ - *])
        (let R (tsl.type-checks [A B] [number number] Env Table Subst
                 Counter Ctx)
          (if (tsl.ok? R)
              [ok number (hd (tl R)) (hd (tl (tl R)))]
              R))
        (if (element? Op [< > <= >=])
            (let R (tsl.type-checks [A B] [number number] Env Table Subst
                     Counter Ctx)
              (if (tsl.ok? R)
                  [ok boolean (hd (tl R)) (hd (tl (tl R)))]
                  R))
            (if (element? Op [= neq])
                (let RA (tsl.type-expr A Env Table Subst Counter Ctx)
                  (if (tsl.ok? RA)
                      (let RB (tsl.type-check B (hd (tl RA)) Env Table
                                (hd (tl (tl RA))) (hd (tl (tl (tl RA)))) Ctx)
                        (if (tsl.ok? RB)
                            [ok boolean (hd (tl RB)) (hd (tl (tl RB)))]
                            RB))
                      RA))
                [error [sl-t005 tsl-unsupported (hd Ctx) [primitive Op]]])))
  Op _ _ _ _ _ Ctx ->
    [error [sl-t005 tsl-unsupported (hd Ctx) [primitive-arity Op]]])

\\ Type-check E against the expected type; returns [ok Subst Counter].
\\ A defined function's name expected at an arrow type denotes the function
\\ (symbol encoding); its signature is instantiated fresh.
(define tsl.type-check
  [e-value S] Expected Env Table Subst Counter Ctx ->
    (let Sig (tsl.env-lookup S Table)
      (let Inst (tsl.instantiate (hd (tl Sig)) Counter)
        (let U (tsl.unify [arrow (hd Inst) (hd (tl Inst))] Expected Subst)
          (if (tsl.ok? U)
              [ok (hd (tl U)) (hd (tl (tl Inst)))]
              [error [sl-t004 tsl-type-mismatch (hd Ctx) (hd (tl Ctx))
                      (tsl.resolve Expected Subst)
                      [arrow (hd Inst) (hd (tl Inst))]]]))))
    where (and (symbol? S)
               (and (tsl.arrow-expected? Expected Subst)
                    (tsl.signed-function? S Table)))
  E Expected Env Table Subst Counter Ctx ->
    (let R (tsl.type-expr E Env Table Subst Counter Ctx)
      (if (tsl.ok? R)
          (let U (tsl.unify (hd (tl R)) Expected (hd (tl (tl R))))
            (if (tsl.ok? U)
                [ok (hd (tl U)) (hd (tl (tl (tl R))))]
                [error [sl-t004 tsl-type-mismatch (hd Ctx) (hd (tl Ctx))
                        (tsl.resolve Expected (hd (tl (tl R))))
                        (tsl.resolve (hd (tl R)) (hd (tl (tl R))))]]))
          R)))

(define tsl.arrow-expected?
  Expected Subst -> (let W (tsl.walk Expected Subst)
                      (if (cons? W) (= (hd W) arrow) false)))

(define tsl.signed-function?
  S Table -> (let F (tsl.env-lookup S Table)
               (if (= F not-found) false (not (= (hd (tl F)) none)))))

(define tsl.type-checks
  [] [] _ _ Subst Counter _ -> [ok Subst Counter]
  [E | Es] [T | Ts] Env Table Subst Counter Ctx ->
    (let R (tsl.type-check E T Env Table Subst Counter Ctx)
      (if (tsl.ok? R)
          (tsl.type-checks Es Ts Env Table (hd (tl R)) (hd (tl (tl R))) Ctx)
          R))
  _ _ _ _ _ _ Ctx ->
    [error [sl-t005 tsl-unsupported (hd Ctx) argument-arity]])

(define tsl.value-types
  [] -> []
  [_ | Xs] -> [value | (tsl.value-types Xs)])

(define tsl.type-guard
  none _ _ Subst Counter _ -> [ok Subst Counter]
  [some G] Env Table Subst Counter Ctx ->
    (tsl.type-check G boolean Env Table Subst Counter Ctx)
  G Env Table Subst Counter Ctx ->
    (tsl.type-check G boolean Env Table Subst Counter Ctx))

\\ --- unification ---------------------------------------------------------

(define tsl.unify
  T1 T2 Subst -> (tsl.unify1 (tsl.walk T1 Subst) (tsl.walk T2 Subst) Subst))

(define tsl.unify1
  [tv N] [tv N] Subst -> [ok Subst]
  [tv N] T Subst -> (if (tsl.occurs? N T Subst)
                        [error [clash [tv N] T]]
                        [ok [[N T] | Subst]])
  T [tv N] Subst -> (tsl.unify1 [tv N] T Subst)
  [list A] [list B] Subst -> (tsl.unify A B Subst)
  [arrow As R] [arrow Bs S] Subst ->
    (if (= (length As) (length Bs))
        (let U (tsl.unify-lists As Bs Subst)
          (if (tsl.ok? U) (tsl.unify R S (hd (tl U))) U))
        [error [clash [arrow As R] [arrow Bs S]]])
  T1 T2 Subst -> (if (= T1 T2) [ok Subst] [error [clash T1 T2]]))

(define tsl.unify-lists
  [] [] Subst -> [ok Subst]
  [A | As] [B | Bs] Subst ->
    (let U (tsl.unify A B Subst)
      (if (tsl.ok? U) (tsl.unify-lists As Bs (hd (tl U))) U)))

(define tsl.walk
  [tv N] Subst -> (let F (tsl.env-lookup N Subst)
                    (if (= F not-found) [tv N] (tsl.walk (hd (tl F)) Subst)))
  T _ -> T)

(define tsl.occurs?
  N T Subst -> (tsl.occurs1? N (tsl.walk T Subst) Subst))

(define tsl.occurs1?
  N [tv N] _ -> true
  N [list T] Subst -> (tsl.occurs? N T Subst)
  N [arrow As R] Subst -> (if (tsl.occurs-any? N As Subst)
                              true
                              (tsl.occurs? N R Subst))
  _ _ _ -> false)

(define tsl.occurs-any?
  _ [] _ -> false
  N [T | Ts] Subst -> (if (tsl.occurs? N T Subst)
                          true
                          (tsl.occurs-any? N Ts Subst)))

\\ Deep resolution; unification variables that survive a whole clause carry
\\ no constraint and default to value.
(define tsl.resolve
  T Subst -> (tsl.resolve1 (tsl.walk T Subst) Subst))

(define tsl.resolve1
  [tv _] _ -> value
  [list T] Subst -> [list (tsl.resolve T Subst)]
  [arrow As R] Subst -> [arrow (map (/. T (tsl.resolve T Subst)) As)
                               (tsl.resolve R Subst)]
  T _ -> T)

(define tsl.resolve-env
  [] _ -> []
  [[X T] | Env] Subst -> [[X (tsl.resolve T Subst)] | (tsl.resolve-env Env Subst)])

(define tsl.env-lookup
  _ [] -> not-found
  X [[X V] | _] -> [found V]
  X [_ | Rest] -> (tsl.env-lookup X Rest))

\\ --- signature instantiation ---------------------------------------------

\\ Returns [ArgTypes Result Counter] with the signature's type variables
\\ replaced by fresh unification variables.
(define tsl.instantiate
  [signature Args Result] Counter ->
    (let IArgs (map (/. T (tsl.internal-type T)) Args)
      (let IResult (tsl.internal-type Result)
        (let TVars (tsl.tvars-list IArgs [IResult])
          (let Map (tsl.fresh-map TVars Counter)
            [(tsl.substitute-types IArgs (hd Map))
             (tsl.substitute-type IResult (hd Map))
             (hd (tl Map))])))))

(define tsl.fresh-map
  Vars Counter -> (tsl.fresh-map-acc Vars Counter []))

(define tsl.fresh-map-acc
  [] Counter Acc -> [(reverse Acc) Counter]
  [V | Vs] Counter Acc ->
    (tsl.fresh-map-acc Vs (+ Counter 1) [[V [tv Counter]] | Acc]))

(define tsl.substitute-types
  [] _ -> []
  [T | Ts] Map -> [(tsl.substitute-type T Map) | (tsl.substitute-types Ts Map)])

(define tsl.substitute-type
  [list T] Map -> [list (tsl.substitute-type T Map)]
  [arrow As R] Map -> [arrow (tsl.substitute-types As Map)
                             (tsl.substitute-type R Map)]
  T Map -> (if (variable? T)
               (let F (tsl.env-lookup T Map)
                 (if (= F not-found) T (hd (tl F))))
               T))
