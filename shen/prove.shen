\\ Conjecture-driven proof queries over the tsl theory.
\\
\\ (shenlogic.prove-file File ConjText InductVar) builds one SMT-LIB
\\ query: the tsl equations of every function the conjecture mentions
\\ (all must be checker-proven total, so the equations are unguarded),
\\ optionally one first-order instance of the list induction schema --
\\ instantiated at the conjecture, which is an instance of the documented
\\ second-order comprehension rule, not a new axiom -- and the negated
\\ conjecture.  unsat from the solver means the theory entails the
\\ conjecture.  The solver call and its fail-closed discipline live in
\\ the bin/shenlogic wrapper, exactly as for repair.
\\
\\ v1 fragment: first-order total functions over number, boolean,
\\ signature type variables (embedded as uninterpreted sorts, the
\\ schematic-generality reading), and (list T) via one parametric SMT
\\ datatype whose semantics subsume the constructor axioms.  The
\\ conjecture must reuse the signatures' type-variable names.  Everything
\\ else is a diagnostic, never an approximation.

(define shenlogic.prove-file
  File ConjText InductVar ->
    (let Program (shenlogic.program File)
      (let TR (tsl.type-program Program)
        (if (tsl.ok? TR)
            (let Tot (hd (tl (termination.classify Program)))
              (let Parsed (read-from-string-unprocessed ConjText)
                (if (= (length Parsed) 1)
                    (prove.run (hd (tl TR)) Tot (hd Parsed) InductVar)
                    [error [sl-p001 prove-malformed-conjecture ConjText]])))
            (tsl.render-error TR)))))

(define prove.run
  TDefs Tot Conj InductVar ->
    (let Peeled (prove.peel Conj [])
      (if (= (hd Peeled) ok)
          (let Binders (hd (tl Peeled))
            (let Matrix (prove.formula (hd (tl (tl Peeled)))
                          (prove.sig-table TDefs))
              (if (= (hd Matrix) ok)
                  (prove.run2 TDefs Tot Binders (hd (tl Matrix)) InductVar)
                  Matrix)))
          Peeled)))

(define prove.run2
  TDefs Tot Binders Matrix InductVar ->
    (let Funs (prove.involved (prove.formula-calls Matrix) TDefs [])
      (if (= (hd Funs) ok)
          (let Bad (prove.first-nontotal (hd (tl Funs)) Tot)
            (if (not (= Bad none))
                [error [sl-p003 prove-requires-total (hd (tl Bad))]]
                (let Sig (prove.check-fragment (hd (tl Funs)) TDefs Binders)
                  (if (= Sig ok)
                      (prove.emit TDefs Tot (hd (tl Funs)) Binders Matrix
                        InductVar)
                      Sig))))
          Funs)))

\\ --- conjecture parsing ----------------------------------------------------

\\ Type binders (all A : type ...) become uninterpreted sorts (schematic
\\ generality); term binders are collected with their tsl types.
(define prove.peel
  [all V : type P] Acc -> (prove.peel P Acc)
  [all V : T P] Acc -> (prove.peel P [[V T] | Acc])
  Matrix Acc -> [ok (reverse Acc) Matrix])

(define prove.sig-table
  [] -> []
  [[t-def Name _ Args Result _] | Ds] ->
    [[Name [signature Args Result]] | (prove.sig-table Ds)])

\\ Raw tsl-syntax formula -> f-* AST.
(define prove.formula
  [all V : T P] Sigs -> (prove.wrap-binder f-all V T P Sigs)
  [some V : T P] Sigs -> (prove.wrap-binder f-some V T P Sigs)
  [Neg P] Sigs ->
    (let R (prove.formula P Sigs)
      (if (= (hd R) ok) [ok [f-not (hd (tl R))]] R))
      where (= (str Neg) "~")
  [and | Ps] Sigs -> (prove.junction f-and Ps Sigs [])
  [or | Ps] Sigs -> (prove.junction f-or Ps Sigs [])
  [P Arrow Q] Sigs -> (prove.arrow-formula Arrow P Q Sigs)
      where (element? Arrow [=> <=> =])
  [Op A B] Sigs -> (prove.cmp-formula Op A B Sigs)
      where (element? Op [< > <= >=])
  F _ -> [error [sl-p001 prove-malformed-conjecture F]])

(define prove.wrap-binder
  Tag V T P Sigs ->
    (let R (prove.formula P Sigs)
      (if (= (hd R) ok)
          [ok [Tag [[V T]] (hd (tl R))]]
          R)))

(define prove.junction
  _ [] _ Acc -> [error [sl-p001 prove-malformed-conjecture empty-junction]]
  Tag [P] Sigs Acc ->
    (let R (prove.formula P Sigs)
      (if (= (hd R) ok)
          [ok [Tag (reverse [(hd (tl R)) | Acc])]]
          R))
  Tag [P | Ps] Sigs Acc ->
    (let R (prove.formula P Sigs)
      (if (= (hd R) ok)
          (prove.junction Tag Ps Sigs [(hd (tl R)) | Acc])
          R)))

(define prove.arrow-formula
  => P Q Sigs -> (prove.two-formula f-imp P Q Sigs)
  <=> P Q Sigs -> (prove.two-formula f-iff P Q Sigs)
  = A B Sigs ->
    (let TA (prove.term A Sigs)
      (if (= (hd TA) ok)
          (let TB (prove.term B Sigs)
            (if (= (hd TB) ok)
                [ok [f-eq (hd (tl TA)) (hd (tl TB))]]
                TB))
          TA)))

(define prove.two-formula
  Tag P Q Sigs ->
    (let RP (prove.formula P Sigs)
      (if (= (hd RP) ok)
          (let RQ (prove.formula Q Sigs)
            (if (= (hd RQ) ok)
                [ok [Tag (hd (tl RP)) (hd (tl RQ))]]
                RQ))
          RP)))

(define prove.cmp-formula
  Op A B Sigs ->
    (let TA (prove.term A Sigs)
      (if (= (hd TA) ok)
          (let TB (prove.term B Sigs)
            (if (= (hd TB) ok)
                [ok [f-cmp Op (hd (tl TA)) (hd (tl TB))]]
                TB))
          TA)))

(define prove.term
  X _ -> [ok [e-var X]] where (variable? X)
  N _ -> [ok [e-value N]] where (integer? N)
  true _ -> [ok [e-value true]]
  false _ -> [ok [e-value false]]
  [] _ -> [ok [e-ctor nil []]]
  [cons A B] Sigs -> (prove.term-app (/. Ts [e-ctor cons Ts]) [A B] Sigs [])
  [Op A B] Sigs -> (prove.term-app (/. Ts [e-prim Op Ts]) [A B] Sigs [])
      where (element? Op [+ - *])
  [F | Args] Sigs ->
    (if (= (tsl.env-lookup F Sigs) not-found)
        [error [sl-p002 prove-unknown-function F]]
        (prove.term-app (/. Ts [e-call F Ts]) Args Sigs []))
  X _ -> [error [sl-p001 prove-malformed-conjecture X]])

(define prove.term-app
  Make [] Sigs Acc -> [ok (Make (reverse Acc))]
  Make [A | As] Sigs Acc ->
    (let R (prove.term A Sigs)
      (if (= (hd R) ok)
          (prove.term-app Make As Sigs [(hd (tl R)) | Acc])
          R)))

\\ --- involvement and fragment checks ---------------------------------------

(define prove.formula-calls
  [f-eq A B] -> (append (prove.term-calls A) (prove.term-calls B))
  [f-cmp _ A B] -> (append (prove.term-calls A) (prove.term-calls B))
  [f-not F] -> (prove.formula-calls F)
  [f-and Fs] -> (prove.formulas-calls Fs)
  [f-or Fs] -> (prove.formulas-calls Fs)
  [f-imp F G] -> (append (prove.formula-calls F) (prove.formula-calls G))
  [f-iff F G] -> (append (prove.formula-calls F) (prove.formula-calls G))
  [f-all _ F] -> (prove.formula-calls F)
  [f-some _ F] -> (prove.formula-calls F)
  _ -> [])

(define prove.formulas-calls
  [] -> []
  [F | Fs] -> (append (prove.formula-calls F) (prove.formulas-calls Fs)))

(define prove.term-calls
  [e-call F Args] -> [F | (prove.terms-calls Args)]
  [e-ctor _ Args] -> (prove.terms-calls Args)
  [e-prim _ Args] -> (prove.terms-calls Args)
  [e-if C T F] -> (prove.terms-calls [C T F])
  _ -> [])

(define prove.terms-calls
  [] -> []
  [T | Ts] -> (append (prove.term-calls T) (prove.terms-calls Ts)))

\\ Transitive closure of mentioned functions over the typed clause bodies.
(define prove.involved
  [] _ Acc -> [ok (reverse Acc)]
  [F | Fs] TDefs Acc ->
    (if (element? F Acc)
        (prove.involved Fs TDefs Acc)
        (let D (prove.find-tdef F TDefs)
          (if (= D none)
              [error [sl-p002 prove-unknown-function F]]
              (prove.involved
                (append Fs (prove.tdef-calls (hd (tl D))))
                TDefs [F | Acc])))))

(define prove.find-tdef
  _ [] -> none
  F [[t-def F TVars Args Result TCs] | _] ->
    [found [t-def F TVars Args Result TCs]]
  F [_ | Ds] -> (prove.find-tdef F Ds))

(define prove.tdef-calls
  [t-def _ _ _ _ TCs] -> (prove.tclauses-calls TCs))

(define prove.tclauses-calls
  [] -> []
  [[t-clause _ _ G B _] | TCs] ->
    (append (prove.expr-calls B)
      (append (prove.guard-calls G) (prove.tclauses-calls TCs))))

(define prove.guard-calls
  none -> []
  [some G] -> (prove.expr-calls G)
  G -> (prove.expr-calls G))

(define prove.expr-calls
  [e-call F Args] -> [F | (prove.exprs-calls Args)]
  [e-ctor _ Args] -> (prove.exprs-calls Args)
  [e-prim _ Args] -> (prove.exprs-calls Args)
  [e-if C T F] -> (prove.exprs-calls [C T F])
  [e-let _ A B] -> (prove.exprs-calls [A B])
  [e-and A B] -> (prove.exprs-calls [A B])
  [e-or A B] -> (prove.exprs-calls [A B])
  _ -> [])

(define prove.exprs-calls
  [] -> []
  [E | Es] -> (append (prove.expr-calls E) (prove.exprs-calls Es)))

(define prove.first-nontotal
  [] _ -> none
  [F | Fs] Tot -> (if (tsl.total-function? F Tot)
                      (prove.first-nontotal Fs Tot)
                      [found F]))

(define prove.check-fragment
  Funs TDefs Binders ->
    (let BadT (prove.first-bad-type
                (append (prove.binder-types Binders)
                        (prove.funs-types Funs TDefs)))
      (if (= BadT none)
          (let BadC (prove.first-user-ctor Funs TDefs)
            (if (= BadC none)
                ok
                [error [sl-p004 prove-unsupported (hd (tl BadC))]]))
          [error [sl-p004 prove-unsupported (hd (tl BadT))]])))

(define prove.binder-types
  [] -> []
  [[_ T] | Bs] -> [T | (prove.binder-types Bs)])

(define prove.funs-types
  [] _ -> []
  [F | Fs] TDefs ->
    (let D (prove.find-tdef F TDefs)
      (append (prove.tdef-types (hd (tl D))) (prove.funs-types Fs TDefs))))

(define prove.tdef-types
  [t-def _ _ Args Result _] -> [Result | Args])

(define prove.first-bad-type
  [] -> none
  [T | Ts] -> (if (prove.type-ok? T)
                  (prove.first-bad-type Ts)
                  [found T]))

(define prove.type-ok?
  number -> true
  boolean -> true
  [list T] -> (prove.type-ok? T)
  T -> (variable? T))

(define prove.first-user-ctor
  [] _ -> none
  [F | Fs] TDefs ->
    (let D (prove.find-tdef F TDefs)
      (let Bad (prove.tclauses-user-ctor (prove.tdef-tcs (hd (tl D))))
        (if (= Bad none)
            (prove.first-user-ctor Fs TDefs)
            Bad))))

(define prove.tdef-tcs
  [t-def _ _ _ _ TCs] -> TCs)

(define prove.tclauses-user-ctor
  [] -> none
  [[t-clause _ Ps G B _] | TCs] ->
    (let Bad (prove.patterns-user-ctor Ps)
      (if (= Bad none)
          (prove.tclauses-user-ctor TCs)
          Bad)))

(define prove.patterns-user-ctor
  [] -> none
  [[p-ctor Tag Ps] | Rest] ->
    (if (element? Tag [cons nil])
        (let Inner (prove.patterns-user-ctor Ps)
          (if (= Inner none) (prove.patterns-user-ctor Rest) Inner))
        [found Tag])
  [_ | Rest] -> (prove.patterns-user-ctor Rest))

\\ --- emission ---------------------------------------------------------------

(define prove.emit
  TDefs Tot Funs Binders Matrix InductVar ->
    (let Sigs (prove.sig-table TDefs)
      (let Sorts (tsl.unique-keep-first
                   (prove.tvars-of (append (prove.binder-types Binders)
                                     (prove.funs-types Funs TDefs)))
                   [])
        (let Ind (prove.induction Binders Matrix InductVar Sigs)
          (if (= (hd Ind) ok)
              [ok (@s "; ShenLogic prove query v1" (tsl.nl)
                      "; unsat = the tsl theory entails the conjecture"
                      (tsl.nl)
                      (prove.sort-decls Sorts)
                      "(declare-datatypes ((SLList 1)) ((par (T) ((slnil) (slcons (slhd T) (sltl (SLList T)))))))"
                      (tsl.nl)
                      (prove.fun-decls Funs TDefs)
                      (prove.equation-asserts Funs TDefs Tot)
                      (hd (tl Ind))
                      "(assert (not "
                      (prove.smt [f-all Binders Matrix] Sigs [])
                      "))" (tsl.nl)
                      "(check-sat)" (tsl.nl))]
              Ind)))))

(define prove.tvars-of
  [] -> []
  [T | Ts] -> (append (reverse (tsl.tvars-type T [])) (prove.tvars-of Ts)))

(define prove.sort-decls
  [] -> ""
  [S | Ss] -> (@s "(declare-sort " (prove.name S) " 0)" (tsl.nl)
                  (prove.sort-decls Ss)))

(define prove.name
  X -> (shenlogic.chc.v2-clean (str X)))

(define prove.sort
  number -> "Int"
  boolean -> "Bool"
  [list T] -> (@s "(SLList " (prove.sort T) ")")
  T -> (prove.name T))

(define prove.fun-decls
  [] _ -> ""
  [F | Fs] TDefs ->
    (let D (hd (tl (prove.find-tdef F TDefs)))
      (@s "(declare-fun " (prove.name F) " ("
          (prove.sort-list (prove.tdef-args D)) ") "
          (prove.sort (prove.tdef-result D)) ")" (tsl.nl)
          (prove.fun-decls Fs TDefs))))

(define prove.tdef-args [t-def _ _ Args _ _] -> Args)
(define prove.tdef-result [t-def _ _ _ Result _] -> Result)

(define prove.sort-list
  [] -> ""
  [T] -> (prove.sort T)
  [T | Ts] -> (@s (prove.sort T) " " (prove.sort-list Ts)))

\\ One assert per clause equation, produced by the same construction the
\\ tsl emitter renders (tsl.equation-formula), so prove and tsl cannot
\\ drift.
(define prove.equation-asserts
  [] _ _ -> ""
  [F | Fs] TDefs Tot ->
    (let D (hd (tl (prove.find-tdef F TDefs)))
      (@s (prove.clause-asserts F (prove.tdef-tcs D) [] Tot
            (prove.tdef-tvars D) (prove.sig-table TDefs))
          (prove.equation-asserts Fs TDefs Tot))))

(define prove.tdef-tvars [t-def _ TVars _ _ _] -> TVars)

(define prove.clause-asserts
  _ [] _ _ _ _ -> ""
  Name [TC | TCs] Prior Tot TVars Sigs ->
    (@s "(assert "
        (prove.smt (tsl.equation-formula Name TC (reverse Prior) Tot TVars)
          Sigs [])
        ")" (tsl.nl)
        (prove.clause-asserts Name TCs [TC | Prior] Tot TVars Sigs)))

\\ --- induction instance -----------------------------------------------------

(define prove.induction
  _ _ none _ -> [ok ""]
  Binders Matrix InductVar Sigs ->
    (let T (tsl.env-lookup InductVar Binders)
      (if (= T not-found)
          [error [sl-p005 prove-bad-induction-variable InductVar]]
          (if (prove.list-type? (hd (tl T)))
              [ok (prove.induction-text Binders Matrix InductVar
                    (hd (tl (hd (tl T)))) Sigs)]
              [error [sl-p005 prove-bad-induction-variable InductVar]]))))

(define prove.list-type?
  [list _] -> true
  _ -> false)

\\ P(l) := forall (other binders) Matrix[InductVar := l]; the emitted
\\ instance is (P nil and forall H,T (P T => P (cons H T))) => conjecture.
(define prove.induction-text
  Binders Matrix V ElemT Sigs ->
    (let Others (prove.drop-binder V Binders)
      (let Taken (tsl.binding-names Binders)
        (let H (prove.fresh "H" 0 Taken)
          (let T (prove.fresh "T" 0 [H | Taken])
            (let P (/. Term (tsl.quantify Others
                              (tsl.subst-formula Matrix [[V Term]])))
              (@s "(assert "
                  (prove.smt
                    [f-imp
                      [f-and [(P [e-ctor nil []])
                              [f-all [[H ElemT] [T [list ElemT]]]
                                [f-imp (P [e-var T])
                                       (P [e-ctor cons [[e-var H]
                                                        [e-var T]]])]]]]
                      [f-all Binders Matrix]]
                    Sigs [])
                  ")" (tsl.nl))))))))

(define prove.drop-binder
  _ [] -> []
  V [[V _] | Bs] -> Bs
  V [B | Bs] -> [B | (prove.drop-binder V Bs)])

(define prove.fresh
  Prefix N Taken ->
    (let V (intern (@s Prefix (str N)))
      (if (element? V Taken)
          (prove.fresh Prefix (+ N 1) Taken)
          V)))

\\ --- SMT rendering ----------------------------------------------------------
\\ Env maps term variables to their tsl types (for expected-type-directed
\\ term emission, which pins every nil to an explicit sort).

(define prove.smt
  [f-true] _ _ -> "true"
  [f-false] _ _ -> "false"
  [f-eq A B] Sigs Env ->
    (let T (prove.infer A Sigs Env)
      (let T2 (if (= T none) (prove.infer B Sigs Env) T)
        (@s "(= " (prove.smt-term T2 A Sigs Env) " "
            (prove.smt-term T2 B Sigs Env) ")")))
  [f-cmp Op A B] Sigs Env ->
    (@s "(" (str Op) " " (prove.smt-term number A Sigs Env) " "
        (prove.smt-term number B Sigs Env) ")")
  [f-not F] Sigs Env -> (@s "(not " (prove.smt F Sigs Env) ")")
  [f-and Fs] Sigs Env -> (@s "(and " (prove.smt-list Fs Sigs Env) ")")
  [f-or Fs] Sigs Env -> (@s "(or " (prove.smt-list Fs Sigs Env) ")")
  [f-imp F G] Sigs Env -> (@s "(=> " (prove.smt F Sigs Env) " "
                              (prove.smt G Sigs Env) ")")
  [f-iff F G] Sigs Env -> (@s "(= " (prove.smt F Sigs Env) " "
                              (prove.smt G Sigs Env) ")")
  [f-all [] F] Sigs Env -> (prove.smt F Sigs Env)
  [f-all Bs F] Sigs Env ->
    (@s "(forall (" (prove.smt-binders Bs) ") "
        (prove.smt F Sigs (append Bs Env)) ")")
  [f-some [] F] Sigs Env -> (prove.smt F Sigs Env)
  [f-some Bs F] Sigs Env ->
    (@s "(exists (" (prove.smt-binders Bs) ") "
        (prove.smt F Sigs (append Bs Env)) ")"))

(define prove.smt-list
  [] _ _ -> ""
  [F] Sigs Env -> (prove.smt F Sigs Env)
  [F | Fs] Sigs Env -> (@s (prove.smt F Sigs Env) " "
                           (prove.smt-list Fs Sigs Env)))

(define prove.smt-binders
  [] -> ""
  [[V T]] -> (@s "(" (prove.name V) " " (prove.sort T) ")")
  [[V T] | Bs] -> (@s "(" (prove.name V) " " (prove.sort T) ") "
                      (prove.smt-binders Bs)))

(define prove.infer
  [e-var V] Sigs Env -> (let F (tsl.env-lookup V Env)
                          (if (= F not-found) none (hd (tl F))))
  [e-value N] _ _ -> number where (integer? N)
  [e-value true] _ _ -> boolean
  [e-value false] _ _ -> boolean
  [e-call F _] Sigs _ ->
    (let S (tsl.env-lookup F Sigs)
      (if (= S not-found) none (hd (tl (tl (hd (tl S)))))))
  [e-prim Op _] _ _ -> number where (element? Op [+ - *])
  [e-prim _ _] _ _ -> boolean
  [e-ctor cons [_ T]] Sigs Env -> (prove.infer T Sigs Env)
  _ _ _ -> none)

(define prove.smt-term
  Expected [e-var V] _ _ -> (prove.name V)
  _ [e-value N] _ _ ->
    (if (< N 0) (@s "(- " (str (- 0 N)) ")") (str N)) where (integer? N)
  _ [e-value true] _ _ -> "true"
  _ [e-value false] _ _ -> "false"
  Expected [e-ctor nil []] _ _ ->
    (@s "(as slnil " (prove.sort Expected) ")")
  [list T] [e-ctor cons [H Tl]] Sigs Env ->
    (@s "(slcons " (prove.smt-term T H Sigs Env) " "
        (prove.smt-term [list T] Tl Sigs Env) ")")
  _ [e-call F []] Sigs _ -> (prove.name F)
  Expected [e-call F Args] Sigs Env ->
    (let S (hd (tl (tsl.env-lookup F Sigs)))
      (@s "(" (prove.name F) " "
          (prove.smt-args (hd (tl S)) Args Sigs Env) ")"))
  _ [e-prim Op [A B]] Sigs Env ->
    (@s "(" (prove.smt-op Op) " " (prove.smt-term number A Sigs Env) " "
        (prove.smt-term number B Sigs Env) ")")
      where (element? Op [+ - *])
  _ [e-prim = [A B]] Sigs Env ->
    (let T (prove.infer A Sigs Env)
      (let T2 (if (= T none) (prove.infer B Sigs Env) T)
        (@s "(= " (prove.smt-term T2 A Sigs Env) " "
            (prove.smt-term T2 B Sigs Env) ")")))
  _ [e-prim neq [A B]] Sigs Env ->
    (let T (prove.infer A Sigs Env)
      (let T2 (if (= T none) (prove.infer B Sigs Env) T)
        (@s "(not (= " (prove.smt-term T2 A Sigs Env) " "
            (prove.smt-term T2 B Sigs Env) "))")))
  _ [e-prim Op [A B]] Sigs Env ->
    (@s "(" (str Op) " " (prove.smt-term number A Sigs Env) " "
        (prove.smt-term number B Sigs Env) ")")
  Expected [e-if C T F] Sigs Env ->
    (@s "(ite " (prove.smt-term boolean C Sigs Env) " "
        (prove.smt-term Expected T Sigs Env) " "
        (prove.smt-term Expected F Sigs Env) ")")
  _ [e-and A B] Sigs Env ->
    (@s "(and " (prove.smt-term boolean A Sigs Env) " "
        (prove.smt-term boolean B Sigs Env) ")")
  _ [e-or A B] Sigs Env ->
    (@s "(or " (prove.smt-term boolean A Sigs Env) " "
        (prove.smt-term boolean B Sigs Env) ")"))

(define prove.smt-op
  + -> "+"
  - -> "-"
  * -> "*")

(define prove.smt-args
  [] [] _ _ -> ""
  [T] [A] Sigs Env -> (prove.smt-term T A Sigs Env)
  [T | Ts] [A | As] Sigs Env ->
    (@s (prove.smt-term T A Sigs Env) " "
        (prove.smt-args Ts As Sigs Env)))
