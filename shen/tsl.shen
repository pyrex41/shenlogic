\\ tsl: typed second-order equational output in the shen2logic style.
\\
\\ Consumes the normalized program (via shen/typing.shen) and the compiled
\\ theory.  Equations are guarded by per-call-site definedness obligations
\\ for callees the termination classifier could not prove total; functions
\\ proven total get Tarver-style unguarded equations.  For each unknown
\\ function a self-contained defined-NAME predicate is emitted: intro
\\ clauses, an inversion axiom, and (for self-recursion) a second-order
\\ minimality schema.  The deduction system is docs/TSL-LOGIC.md.
\\
\\ Formula nodes: f-true, f-false, [f-eq A B], [f-cmp Op A B], [f-not F],
\\ [f-and Fs], [f-or Fs], [f-imp F G], [f-defined Name Terms],
\\ [f-some Bindings F], [f-all Bindings F], [f-all-types TVars F],
\\ [f-pred P Terms], [f-all-pred P TypeString F].  Terms are normalized
\\ expression nodes.

(define shenlogic.tsl.render
  Program Theory ->
    (let TR (tsl.type-program Program)
      (if (tsl.ok? TR)
          (let Tot (termination.classify Program)
            [ok (tsl.text (hd (tl TR)) (hd (tl Tot)) Program Theory)])
          (tsl.render-error TR))))

(define tsl.render-error
  [error [Code | Payload]] -> [error Code Payload]
  E -> E)

(define tsl.text
  TDefs Totality Program Theory ->
    (@s (tsl.header TDefs Totality)
        (tsl.axioms-section TDefs Theory)
        (tsl.definedness-section TDefs Totality Program)
        (tsl.equations-section TDefs Totality)))

(define tsl.nl
  -> (n->string 10))

(define tsl.header
  TDefs Totality ->
    (@s "; ShenLogic tsl v1" (tsl.nl)
        "; deduction system: docs/TSL-LOGIC.md" (tsl.nl)
        (tsl.header-lines TDefs Totality)))

(define tsl.header-lines
  [] _ -> ""
  [[t-def Name _ _ _ _] | Ds] Totality ->
    (let E (tsl.totality-entry Name Totality)
      (@s "; totality: " (str Name) " " (str (hd (tl E)))
          " (" (tsl.reason-text (hd (tl (tl E)))) ")" (tsl.nl)
          (tsl.header-lines Ds Totality))))

(define tsl.totality-entry
  Name [] -> [Name unknown [unclassified]]
  Name [[Name S R] | _] -> [Name S R]
  Name [_ | Es] -> (tsl.totality-entry Name Es))

(define tsl.total-function?
  Name Totality -> (= (hd (tl (tsl.totality-entry Name Totality))) total))

(define tsl.reason-text
  [non-recursive] -> "non-recursive"
  [structural I] -> (@s "structural descent at argument " (str I))
  [structural-lex I J] -> (@s "lexicographic structural descent at arguments "
                              (str I) " and " (str J))
  [int-measure I] -> (@s "integer descent at argument " (str I)
                         " with guard lower bound")
  [int-ascent I] -> (@s "integer ascent at argument " (str I)
                        " with guard upper bound")
  [non-exhaustive F] -> (@s "non-exhaustive clauses in " (str F))
  [callee G] -> (@s "depends on " (str G))
  [no-descent] -> "no descent measure found"
  [unclassified] -> "unclassified"
  R -> (str R))

\\ --- axiom blocks --------------------------------------------------------
\\
\\ The companion theory that makes disequalities and induction provable:
\\ constructor injectivity, pairwise disjointness, structural induction,
\\ boolean case analysis, and the conditional's defining equations.  Blocks
\\ are emitted only for sorts the program's typed reading actually uses, so
\\ purely numeric programs stay axiom-free.

(define tsl.axioms-section
  TDefs Theory ->
    (let Lists (if (tsl.uses-list? TDefs) (tsl.list-axioms) "")
      (let Users (tsl.user-ctor-axioms Theory)
        (let Bools (if (tsl.uses-boolean? TDefs) (tsl.boolean-axioms) "")
          (let Bridges (tsl.bool-bridges TDefs)
            (let Ifs (if (tsl.uses-if? TDefs) (tsl.if-axioms) "")
              (let Text (@s Lists Users Bools Bridges Ifs)
                (if (= Text "") "" (@s (tsl.nl) Text)))))))))

\\ Comparison, equality, and connective spellings are overloaded: they are
\\ formulas in condition positions and boolean-sorted terms in value
\\ positions.  These bridge axioms tie each term former used in some body
\\ to its formula reading, so equations like ((positive? X) = (> X 0)) have
\\ derivational force.
(define tsl.bool-bridges
  TDefs ->
    (let Ops (tsl.unique-keep-first (tsl.term-bool-ops TDefs) [])
      (if (= Ops [])
          ""
          (@s "; boolean bridge axioms" (tsl.nl)
              (tsl.bridge-blocks Ops)))))

(define tsl.term-bool-ops
  [] -> []
  [[t-def _ _ _ _ TCs] | Ds] ->
    (append (tsl.clauses-bool-ops TCs) (tsl.term-bool-ops Ds)))

(define tsl.clauses-bool-ops
  [] -> []
  [[t-clause _ _ _ B _] | TCs] ->
    (append (tsl.expr-bool-ops B) (tsl.clauses-bool-ops TCs)))

(define tsl.expr-bool-ops
  [e-prim Op Args] -> (append (if (element? Op [< > <= >= = neq]) [Op] [])
                              (tsl.exprs-bool-ops Args))
  [e-and A B] -> [and | (tsl.exprs-bool-ops [A B])]
  [e-or A B] -> [or | (tsl.exprs-bool-ops [A B])]
  [e-ctor _ Args] -> (tsl.exprs-bool-ops Args)
  [e-call _ Args] -> (tsl.exprs-bool-ops Args)
  [e-apply _ Args] -> (tsl.exprs-bool-ops Args)
  [e-if C T F] -> (tsl.exprs-bool-ops [C T F])
  [e-let _ A B] -> (tsl.exprs-bool-ops [A B])
  _ -> [])

(define tsl.exprs-bool-ops
  [] -> []
  [E | Es] -> (append (tsl.expr-bool-ops E) (tsl.exprs-bool-ops Es)))

(define tsl.bridge-blocks
  [] -> ""
  [Op | Ops] -> (@s (tsl.bridge-block Op) (tsl.bridge-blocks Ops)))

(define tsl.bridge-block
  and -> (@s (tsl.truth-line and true true true)
             (tsl.truth-line and true false false)
             (tsl.truth-line and false true false)
             (tsl.truth-line and false false false))
  or -> (@s (tsl.truth-line or true true true)
            (tsl.truth-line or true false true)
            (tsl.truth-line or false true true)
            (tsl.truth-line or false false false))
  = -> (tsl.eq-bridge)
  neq -> (tsl.neq-bridge)
  Op -> (tsl.cmp-bridge Op))

(define tsl.truth-line
  Op A B R ->
    (tsl.line [f-eq (tsl.connective-term Op [e-value A] [e-value B])
                    [e-value R]]))

(define tsl.connective-term
  and A B -> [e-and A B]
  or A B -> [e-or A B])

(define tsl.cmp-bridge
  Op -> (let X (tsl.sym "X") Y (tsl.sym "Y")
          (@s (tsl.line
                [f-all [[X number] [Y number]]
                  [f-imp [f-cmp Op [e-var X] [e-var Y]]
                         [f-eq [e-prim Op [[e-var X] [e-var Y]]]
                               [e-value true]]]])
              (tsl.line
                [f-all [[X number] [Y number]]
                  [f-imp [f-not [f-cmp Op [e-var X] [e-var Y]]]
                         [f-eq [e-prim Op [[e-var X] [e-var Y]]]
                               [e-value false]]]]))))

(define tsl.eq-bridge
  -> (let A (tsl.sym "A") X (tsl.sym "X") Y (tsl.sym "Y")
       (@s (tsl.line
             [f-all [[X A] [Y A]]
               [f-imp [f-eq [e-var X] [e-var Y]]
                      [f-eq [e-prim = [[e-var X] [e-var Y]]]
                            [e-value true]]]])
           (tsl.line
             [f-all [[X A] [Y A]]
               [f-imp [f-not [f-eq [e-var X] [e-var Y]]]
                      [f-eq [e-prim = [[e-var X] [e-var Y]]]
                            [e-value false]]]]))))

(define tsl.neq-bridge
  -> (let A (tsl.sym "A") X (tsl.sym "X") Y (tsl.sym "Y")
       (@s (tsl.line
             [f-all [[X A] [Y A]]
               [f-imp [f-not [f-eq [e-var X] [e-var Y]]]
                      [f-eq [e-prim neq [[e-var X] [e-var Y]]]
                            [e-value true]]]])
           (tsl.line
             [f-all [[X A] [Y A]]
               [f-imp [f-eq [e-var X] [e-var Y]]
                      [f-eq [e-prim neq [[e-var X] [e-var Y]]]
                            [e-value false]]]]))))

(define tsl.sym
  Name -> (intern Name))

(define tsl.uses-list? TDefs -> (tsl.types-use? (tsl.all-types TDefs) list))
(define tsl.uses-boolean? TDefs -> (tsl.types-use? (tsl.all-types TDefs) boolean))

(define tsl.all-types
  [] -> []
  [[t-def _ _ Args Result TCs] | Ds] ->
    (append Args [Result | (append (tsl.clause-binding-types TCs)
                                   (tsl.all-types Ds))]))

(define tsl.clause-binding-types
  [] -> []
  [[t-clause _ _ _ _ Bindings] | TCs] ->
    (append (map (/. B (hd (tl B))) Bindings)
            (tsl.clause-binding-types TCs)))

(define tsl.types-use?
  [] _ -> false
  [T | Ts] Sort -> (if (tsl.type-uses? T Sort)
                       true
                       (tsl.types-use? Ts Sort)))

(define tsl.type-uses?
  [list T] list -> true
  [list T] Sort -> (tsl.type-uses? T Sort)
  [arrow As R] Sort -> (tsl.types-use? (append As [R]) Sort)
  T Sort -> (= T Sort))

(define tsl.uses-if?
  [] -> false
  [[t-def _ _ _ _ TCs] | Ds] ->
    (if (tsl.clauses-use-if? TCs) true (tsl.uses-if? Ds)))

(define tsl.clauses-use-if?
  [] -> false
  [[t-clause _ _ G B _] | TCs] ->
    (if (or (tsl.expr-uses-if? B) (tsl.guard-uses-if? G))
        true
        (tsl.clauses-use-if? TCs)))

(define tsl.guard-uses-if?
  none -> false
  [some G] -> (tsl.expr-uses-if? G)
  G -> (tsl.expr-uses-if? G))

(define tsl.expr-uses-if?
  [e-if _ _ _] -> true
  [e-ctor _ Args] -> (tsl.exprs-use-if? Args)
  [e-call _ Args] -> (tsl.exprs-use-if? Args)
  [e-apply _ Args] -> (tsl.exprs-use-if? Args)
  [e-prim _ Args] -> (tsl.exprs-use-if? Args)
  [e-let _ A B] -> (tsl.exprs-use-if? [A B])
  [e-and A B] -> (tsl.exprs-use-if? [A B])
  [e-or A B] -> (tsl.exprs-use-if? [A B])
  _ -> false)

(define tsl.exprs-use-if?
  [] -> false
  [E | Es] -> (if (tsl.expr-uses-if? E) true (tsl.exprs-use-if? Es)))

(define tsl.list-axioms
  -> (let A (tsl.sym "A") X (tsl.sym "X") Y (tsl.sym "Y")
          Z (tsl.sym "Z") W (tsl.sym "W") L (tsl.sym "L") P (tsl.sym "P")
       (@s "; list axioms" (tsl.nl)
           (tsl.line
             [f-all [[X A] [Y [list A]] [Z A] [W [list A]]]
               [f-imp [f-eq [e-ctor cons [[e-var X] [e-var Y]]]
                            [e-ctor cons [[e-var Z] [e-var W]]]]
                      [f-and [[f-eq [e-var X] [e-var Z]]
                              [f-eq [e-var Y] [e-var W]]]]]])
           (tsl.line
             [f-all [[X A] [Y [list A]]]
               [f-not [f-eq [e-ctor cons [[e-var X] [e-var Y]]]
                            [e-ctor nil []]]]])
           (tsl.line
             [f-all-pred P [[list A]]
               [f-imp
                 [f-and [[f-pred P [[e-ctor nil []]]]
                         [f-all [[X A] [Y [list A]]]
                           [f-imp [f-pred P [[e-var Y]]]
                                  [f-pred P [[e-ctor cons [[e-var X]
                                                           [e-var Y]]]]]]]]]
                 [f-all [[L [list A]]] [f-pred P [[e-var L]]]]]]))))

(define tsl.boolean-axioms
  -> (let B (tsl.sym "B")
       (@s "; boolean axioms" (tsl.nl)
           (tsl.line [f-not [f-eq [e-value true] [e-value false]]])
           (tsl.line
             [f-all [[B boolean]]
               [f-or [[f-eq [e-var B] [e-value true]]
                      [f-eq [e-var B] [e-value false]]]]]))))

(define tsl.if-axioms
  -> (let A (tsl.sym "A") X (tsl.sym "X") Y (tsl.sym "Y")
       (@s "; conditional axioms" (tsl.nl)
           (tsl.line
             [f-all [[X A] [Y A]]
               [f-eq [e-if [e-value true] [e-var X] [e-var Y]] [e-var X]]])
           (tsl.line
             [f-all [[X A] [Y A]]
               [f-eq [e-if [e-value false] [e-var X] [e-var Y]]
                     [e-var Y]]]))))

\\ User constructors are monomorphic at value: injectivity, pairwise
\\ disjointness, and induction over the value sort they generate.
(define tsl.user-ctor-axioms
  [theory [value-signature Cs] _ _ _ _] ->
    (let Users (tsl.user-ctors Cs)
      (if (= Users [])
          ""
          (@s "; constructor axioms" (tsl.nl)
              (tsl.user-injectivity Users)
              (tsl.user-disjointness Users)
              (tsl.line (tsl.user-induction Users)))))
  _ -> "")

(define tsl.user-ctors
  [] -> []
  [[constructor Tag _ N] | Cs] ->
    (if (element? Tag [int true false symbol string nil cons])
        (tsl.user-ctors Cs)
        [[Tag N] | (tsl.user-ctors Cs)]))

(define tsl.user-injectivity
  [] -> ""
  [[Tag 0] | Cs] -> (tsl.user-injectivity Cs)
  [[Tag N] | Cs] ->
    (let Xs (tsl.value-vars "X" 0 N)
      (let Ys (tsl.value-vars "Y" 0 N)
        (@s (tsl.line
              [f-all (append (tsl.value-bindings Xs) (tsl.value-bindings Ys))
                [f-imp [f-eq [e-ctor Tag (tsl.var-terms Xs)]
                             [e-ctor Tag (tsl.var-terms Ys)]]
                       (tsl.flatten-and (tsl.pairwise-eq Xs Ys))]])
            (tsl.user-injectivity Cs)))))

(define tsl.pairwise-eq
  [] [] -> []
  [X | Xs] [Y | Ys] -> [[f-eq [e-var X] [e-var Y]] |
                        (tsl.pairwise-eq Xs Ys)])

(define tsl.user-disjointness
  [] -> ""
  [C | Cs] -> (@s (tsl.disjoint-with C Cs) (tsl.user-disjointness Cs)))

(define tsl.disjoint-with
  _ [] -> ""
  [Tag N] [[Tag2 N2] | Cs] ->
    (let Xs (tsl.value-vars "X" 0 N)
      (let Ys (tsl.value-vars "Y" 0 N2)
        (@s (tsl.line
              [f-all (append (tsl.value-bindings Xs) (tsl.value-bindings Ys))
                [f-not [f-eq [e-ctor Tag (tsl.var-terms Xs)]
                             [e-ctor Tag2 (tsl.var-terms Ys)]]]])
            (tsl.disjoint-with [Tag N] Cs)))))

(define tsl.user-induction
  Users ->
    (let P (tsl.sym "P") V (tsl.sym "V")
      [f-all-pred P [value]
        [f-imp (tsl.flatten-and (tsl.induction-cases Users P))
               [f-all [[V value]] [f-pred P [[e-var V]]]]]]))

(define tsl.induction-cases
  [] _ -> []
  [[Tag 0] | Cs] P -> [[f-pred P [[e-ctor Tag []]]] |
                       (tsl.induction-cases Cs P)]
  [[Tag N] | Cs] P ->
    (let Xs (tsl.value-vars "X" 0 N)
      [[f-all (tsl.value-bindings Xs)
         [f-imp (tsl.flatten-and (tsl.pred-hyps Xs P))
                [f-pred P [[e-ctor Tag (tsl.var-terms Xs)]]]]] |
       (tsl.induction-cases Cs P)]))

(define tsl.pred-hyps
  [] _ -> []
  [X | Xs] P -> [[f-pred P [[e-var X]]] | (tsl.pred-hyps Xs P)])

(define tsl.value-vars
  _ N N -> []
  Prefix I N -> [(tsl.sym (cn Prefix (str I))) |
                 (tsl.value-vars Prefix (+ I 1) N)])

(define tsl.value-bindings
  [] -> []
  [X | Xs] -> [[X value] | (tsl.value-bindings Xs)])

(define tsl.var-terms
  [] -> []
  [X | Xs] -> [[e-var X] | (tsl.var-terms Xs)])

\\ --- definedness ---------------------------------------------------------

(define tsl.definedness-section
  TDefs Totality Program ->
    (let Text (@s (tsl.apply-definedness TDefs Totality Program)
                  (tsl.definedness-defs TDefs Totality
                    (tsl.singleton-sccs Program)))
      (if (= Text "") "" (@s (tsl.nl) Text))))

\\ defined-apply-N axioms: applying a named total function is defined on all
\\ arguments; applying a named unknown function is defined exactly on its
\\ definedness domain.  defined-apply-N is otherwise unconstrained, matching
\\ the intended reading exists r. sl.apply-N(F, x̄, r).
(define tsl.apply-definedness
  TDefs Totality Program ->
    (let Arities (tsl.program-apply-arities Program)
      (if (= Arities [])
          ""
          (@s "; definedness: function application" (tsl.nl)
              (tsl.apply-definedness-arities Arities TDefs Totality)))))

(define tsl.program-apply-arities
  [program Defs] -> (rules.apply-arities Defs)
  _ -> [])

(define tsl.apply-defined-name
  N -> (intern (cn "defined-apply-" (str N))))

(define tsl.apply-definedness-arities
  [] _ _ -> ""
  [N | Ns] TDefs Totality ->
    (@s (tsl.apply-definedness-defs N TDefs Totality)
        (tsl.apply-definedness-arities Ns TDefs Totality)))

(define tsl.apply-definedness-defs
  _ [] _ -> ""
  N [[t-def F _ Args _ TCs] | Ds] Totality ->
    (@s (if (= (length Args) N)
            (tsl.line (tsl.apply-definedness-axiom N F Args Totality))
            "")
        (tsl.apply-definedness-defs N Ds Totality)))

(define tsl.apply-definedness-axiom
  N F Args Totality ->
    (let Vars (tsl.devar-clash (tsl.value-vars "X" 0 N)
                (tsl.types-tvars Args) [])
      (let Terms [[e-value F] | (tsl.var-terms Vars)]
        (tsl.quantify (tsl.typed-bindings Vars Args)
          (if (tsl.total-function? F Totality)
              [f-defined (tsl.apply-defined-name N) Terms]
              [f-iff [f-defined (tsl.defined-name F) (tsl.var-terms Vars)]
                     [f-defined (tsl.apply-defined-name N) Terms]])))))

(define tsl.typed-bindings
  [] [] -> []
  [X | Xs] [T | Ts] -> [[X T] | (tsl.typed-bindings Xs Ts)])

(define tsl.devar-clash
  [] _ _ -> []
  [V | Vs] Avoid Done ->
    (let W (if (element? V Avoid)
               (tsl.fresh-exist 0 (append Avoid (append Vs Done)))
               V)
      [W | (tsl.devar-clash Vs Avoid [W | Done])]))

(define tsl.singleton-sccs
  [program Defs] ->
    (let Names (map (/. D (shenlogic.ast.definition-name D)) Defs)
      (tsl.singletons (termination.sccs Names
                        (termination.adjacency Defs Names))))
  _ -> [])

(define tsl.singletons
  [] -> []
  [[scc [N]] | Ss] -> [N | (tsl.singletons Ss)]
  [_ | Ss] -> (tsl.singletons Ss))

(define tsl.definedness-defs
  [] _ _ -> ""
  [D | Ds] Totality Singles ->
    (@s (tsl.definedness-def D Totality Singles)
        (tsl.definedness-defs Ds Totality Singles)))

(define tsl.definedness-def
  [t-def Name TVars Args Result TCs] Totality Singles ->
    (if (tsl.total-function? Name Totality)
        ""
        (@s "; definedness: " (str Name) (tsl.nl)
            (tsl.intro-lines Name TCs [] Totality TVars)
            (tsl.line (tsl.inversion Name TVars Args TCs Totality))
            (if (element? Name Singles)
                (tsl.line (tsl.minimality Name TVars Args TCs Totality))
                (@s "; leastness of " (str (tsl.defined-name Name))
                    " is model-theoretic (mutual recursion)" (tsl.nl))))))

(define tsl.line
  F -> (@s (tsl.render-formula (tsl.quantify-types F)) (tsl.nl)))

(define tsl.intro-lines
  _ [] _ _ _ -> ""
  Name [TC | TCs] Prior Totality TVars ->
    (@s (tsl.line (tsl.intro-formula Name TC (reverse Prior) Totality TVars))
        (tsl.intro-lines Name TCs [TC | Prior] Totality TVars)))

\\ An intro clause is the clause's equation conditions concluding in
\\ defined-NAME applied to the clause's pattern terms.
(define tsl.intro-formula
  Name [t-clause I Ps G B Bindings] Prior Totality TVars ->
    (let Conds (tsl.clause-conditions [t-clause I Ps G B Bindings]
                 Prior Totality TVars)
      (tsl.quantify Bindings
        (tsl.implies Conds
          [f-defined (tsl.defined-name Name) (tsl.pattern-terms Ps)]))))

(define tsl.defined-name
  Name -> (intern (cn "defined-" (str Name))))

\\ The inversion axiom: a defined call entered through some clause whose
\\ match, priority context, guard, and body obligations all hold.
(define tsl.inversion
  Name TVars Args TCs Totality ->
    (let Univ (tsl.universal-args TCs Args 0 TVars)
      (tsl.quantify Univ
        [f-imp [f-defined (tsl.defined-name Name) (tsl.binding-terms Univ)]
               (tsl.or-cases
                 (tsl.inversion-cases TCs [] Univ Totality TVars))])))

(define tsl.or-cases
  [] -> [f-false]
  [F] -> F
  Fs -> [f-or Fs])

\\ Each case carries its priority exclusions specialized against the case
\\ clause's own patterns (inside tsl.applicable), so constructor-disjoint
\\ priors are pruned exactly as in the equations section.
(define tsl.inversion-cases
  [] _ _ _ _ -> []
  [TC | TCs] Prior Univ Totality TVars ->
    (let Avoid (append TVars (tsl.binding-names Univ))
      (let App (tsl.applicable TC (reverse Prior)
                 (tsl.binding-patterns Univ) Avoid true Totality)
        (append
          (if (= App disjoint) [] [(hd (tl App))])
          (tsl.inversion-cases TCs [TC | Prior] Univ Totality TVars)))))

(define tsl.flatten-and
  [F] -> F
  Fs -> [f-and (tsl.flatten-and-list Fs)])

(define tsl.flatten-and-list
  [] -> []
  [[f-and Gs] | Fs] -> (append Gs (tsl.flatten-and-list Fs))
  [F | Fs] -> [F | (tsl.flatten-and-list Fs)])

\\ Universal argument names: the first pattern variable seen at a position,
\\ else a generated name; all kept distinct from each other and from the
\\ signature's type variables.
(define tsl.universal-args
  TCs [] _ _ -> []
  TCs [T | Ts] I Avoid ->
    (let Rest (tsl.universal-args TCs Ts (+ I 1) Avoid)
      [[(tsl.univ-name TCs I (append Avoid (map (/. B (hd B)) Rest))) T] |
       Rest]))

(define tsl.univ-name
  TCs I Taken ->
    (let V (tsl.first-var-at TCs I)
      (if (or (= V none) (element? (hd (tl V)) Taken))
          (tsl.fresh-univ I Taken)
          (hd (tl V)))))

(define tsl.first-var-at
  [] _ -> none
  [[t-clause _ Ps _ _ _] | TCs] I ->
    (let P (termination.nth Ps I)
      (if (= (hd P) p-var)
          [found (hd (tl P))]
          (tsl.first-var-at TCs I))))

(define tsl.fresh-univ
  I Taken -> (let V (intern (cn "A" (str I)))
               (if (element? V Taken)
                   (tsl.fresh-univ (+ I 1) Taken)
                   V)))

(define tsl.binding-patterns
  [] -> []
  [[V _] | Bs] -> [[p-var V] | (tsl.binding-patterns Bs)])

(define tsl.binding-names
  [] -> []
  [[V _] | Bs] -> [V | (tsl.binding-names Bs)])

(define tsl.binding-terms
  [] -> []
  [[V _] | Bs] -> [[e-var V] | (tsl.binding-terms Bs)])

\\ Second-order minimality for a self-recursive unknown function: any
\\ predicate closed under the intro clauses contains defined-NAME.
(define tsl.minimality
  Name TVars Args TCs Totality ->
    (let P (tsl.pred-name TCs TVars)
      (let Univ (tsl.universal-args TCs Args 0 TVars)
        [f-all-pred P Args
          [f-imp (tsl.flatten-and
                   (tsl.closure-clauses Name P TCs [] Totality TVars))
                 (tsl.quantify Univ
                   [f-imp [f-defined (tsl.defined-name Name)
                           (tsl.binding-terms Univ)]
                          [f-pred P (tsl.binding-terms Univ)]])]])))

(define tsl.closure-clauses
  _ _ [] _ _ _ -> []
  Name P [TC | TCs] Prior Totality TVars ->
    [(tsl.swap-defined
       (tsl.intro-formula Name TC (reverse Prior) Totality TVars)
       (tsl.defined-name Name) P) |
     (tsl.closure-clauses Name P TCs [TC | Prior] Totality TVars)])

(define tsl.pred-name
  TCs TVars -> (tsl.pred-candidate
                 [(intern "P") (intern "Pred") (intern "Pred0")]
                 (append TVars (tsl.clause-var-names TCs))))

(define tsl.pred-candidate
  [] Taken -> (tsl.pred-fresh 1 Taken)
  [C | Cs] Taken -> (if (element? C Taken)
                        (tsl.pred-candidate Cs Taken)
                        C))

(define tsl.pred-fresh
  N Taken -> (let V (intern (cn "Pred" (str N)))
               (if (element? V Taken)
                   (tsl.pred-fresh (+ N 1) Taken)
                   V)))

(define tsl.clause-var-names
  [] -> []
  [[t-clause _ _ _ _ Bindings] | TCs] ->
    (append (map (/. B (hd B)) Bindings) (tsl.clause-var-names TCs)))

(define tsl.pred-type
  [] -> "o"
  [T | Ts] -> (@s "(" (tsl.render-type T) " => " (tsl.pred-type Ts) ")"))

(define tsl.swap-defined
  [f-defined D Ts] D P -> [f-pred P Ts]
  [f-defined E Ts] _ _ -> [f-defined E Ts]
  [f-not F] D P -> [f-not (tsl.swap-defined F D P)]
  [f-and Fs] D P -> [f-and (tsl.swap-defined-list Fs D P)]
  [f-or Fs] D P -> [f-or (tsl.swap-defined-list Fs D P)]
  [f-imp F G] D P -> [f-imp (tsl.swap-defined F D P) (tsl.swap-defined G D P)]
  [f-some Bs F] D P -> [f-some Bs (tsl.swap-defined F D P)]
  [f-all Bs F] D P -> [f-all Bs (tsl.swap-defined F D P)]
  [f-all-types Vs F] D P -> [f-all-types Vs (tsl.swap-defined F D P)]
  F _ _ -> F)

(define tsl.swap-defined-list
  [] _ _ -> []
  [F | Fs] D P -> [(tsl.swap-defined F D P) | (tsl.swap-defined-list Fs D P)])

\\ --- equations -----------------------------------------------------------

(define tsl.equations-section
  TDefs Totality ->
    (@s (tsl.nl) "; equations" (tsl.nl)
        (tsl.equations-defs TDefs Totality)))

(define tsl.equations-defs
  [] _ -> ""
  [[t-def Name TVars _ _ TCs] | Ds] Totality ->
    (@s (tsl.equation-lines Name TCs [] Totality TVars)
        (tsl.equations-defs Ds Totality)))

(define tsl.equation-lines
  _ [] _ _ _ -> ""
  Name [TC | TCs] Prior Totality TVars ->
    (@s (tsl.line (tsl.equation-formula Name TC (reverse Prior) Totality
                    TVars))
        (tsl.equation-lines Name TCs [TC | Prior] Totality TVars)))

(define tsl.equation-formula
  Name [t-clause I Ps G B Bindings] Prior Totality TVars ->
    (let Conds (tsl.clause-conditions [t-clause I Ps G B Bindings]
                 Prior Totality TVars)
      (tsl.quantify Bindings
        (tsl.implies Conds
          [f-eq [e-call Name (tsl.pattern-terms Ps)]
                (tsl.inline B)]))))

\\ Shared clause conditions: priority exclusions, then the guard, then the
\\ body's definedness obligations.  The avoid set includes the signature's
\\ type variables so generated names never shadow them.
(define tsl.clause-conditions
  [t-clause _ Ps G B Bindings] Prior Totality TVars ->
    (let Excl (tsl.exclusion-formulas Prior Ps
                (append TVars (map (/. X (hd X)) Bindings)) Totality)
      (let Guard (tsl.guard-formula G)
        (append Excl
          (append Guard
            (tsl.simp-obligations
              (tsl.unique-formulas (tsl.obligations B Totality))
              (append Excl Guard)))))))

(define tsl.implies
  [] F -> F
  Conds F -> [f-imp (tsl.flatten-and Conds) F])

(define tsl.quantify
  [] F -> F
  Bindings F -> [f-all Bindings F])

(define tsl.guard-formula
  none -> []
  [some G] -> [(tsl.formula-of (tsl.inline G))]
  G -> [(tsl.formula-of (tsl.inline G))])

(define tsl.unique-formulas
  [] -> []
  [F | Fs] -> (if (element? F Fs)
                  (tsl.unique-formulas Fs)
                  [F | (tsl.unique-formulas Fs)]))

\\ --- contextual reduction --------------------------------------------------
\\
\\ A small, ordered, size-decreasing reducer applied to definedness
\\ obligation lists under the assumptions already in force (the clause's
\\ exclusions, guard, and earlier obligations).  Every rule is a classical
\\ equivalence; deletion happens only when the context syntactically
\\ contains the formula (or its negation), so unknown entailments leave the
\\ formula untouched.  Axiom blocks, quantifier binders, exclusions, and
\\ guards are never altered.  Rules:
\\   N1 units: true/false absorb or vanish in and/or.
\\   N2 flatten: nested and/or splice into their parent; singletons open.
\\   N3 double negation: ~~F is F.
\\   N4 duplicates: a conjunct/disjunct already present is dropped.
\\   A1 context: a conjunct entailed by (context + earlier survivors) is
\\      dropped; one refuted there makes the conjunction false.
\\   A2 complements: F alongside ~F makes a conjunction false and a
\\      disjunction true.
\\   A4 disjunct context: disjunct i is reduced under the negations of the
\\      earlier surviving disjuncts (A or B is A or (B under ~A)); one that
\\      the context proves makes the disjunction true.  Order is preserved.
\\ Termination: structural recursion; each fold step consumes one member.

(define tsl.neg
  [f-not F] -> F
  F -> [f-not F])

\\ Atom comparison modulo the linear-arithmetic background theory,
\\ checker-side only: printed formulas are never rewritten.  A comparison
\\ is keyed by the canonical form of its difference, normalized to strict
\\ (d < 0) or non-strict (d <= 0); two spellings with equal keys denote
\\ the same relation (LIA), and [lt D] is the exact complement of
\\ [le -D] by the total order on the integers.  Numeric equalities
\\ compare by difference form up to sign (symmetry of =).  Any operand
\\ without a linear form falls back to structural comparison: fail
\\ closed.

(define tsl.cmp-key
  [f-cmp < A B] -> (tsl.key-tag lt (linarith.form [e-prim - [A B]]))
  [f-cmp > A B] -> (tsl.key-tag lt (linarith.form [e-prim - [B A]]))
  [f-cmp <= A B] -> (tsl.key-tag le (linarith.form [e-prim - [A B]]))
  [f-cmp >= A B] -> (tsl.key-tag le (linarith.form [e-prim - [B A]]))
  _ -> none)

(define tsl.key-tag
  _ none -> none
  Tag D -> [Tag D])

(define tsl.eq-key
  [f-eq A B] -> (linarith.form [e-prim - [A B]])
  _ -> none)

(define tsl.atom-equal?
  F F -> true
  [f-not F] [f-not G] -> (tsl.atom-equal? F G)
  F G -> (let KF (tsl.cmp-key F)
           (if (not (= KF none))
               (= KF (tsl.cmp-key G))
               (let DF (tsl.eq-key F)
                 (if (= DF none)
                     false
                     (let DG (tsl.eq-key G)
                       (if (= DG none)
                           false
                           (or (= DF DG)
                               (= DF (linarith.scale -1 DG))))))))))

(define tsl.atom-complement?
  [f-not F] G -> (tsl.atom-equal? F G)
  F [f-not G] -> (tsl.atom-equal? F G)
  F G -> (let KF (tsl.cmp-key F)
           (if (= KF none)
               false
               (let KG (tsl.cmp-key G)
                 (if (= KG none)
                     false
                     (tsl.trichotomy? KF KG))))))

(define tsl.trichotomy?
  [lt D] [le E] -> (= E (linarith.scale -1 D))
  [le D] [lt E] -> (= E (linarith.scale -1 D))
  _ _ -> false)

(define tsl.member-atom?
  _ [] -> false
  F [G | Gs] -> (if (tsl.atom-equal? F G) true (tsl.member-atom? F Gs)))

(define tsl.refuted-atom?
  _ [] -> false
  F [G | Gs] -> (if (tsl.atom-complement? F G)
                    true
                    (tsl.refuted-atom? F Gs)))

(define tsl.simp
  [f-and Fs] Ctx -> (tsl.rebuild-and (tsl.simp-conjuncts Fs Ctx []))
  [f-or Fs] Ctx -> (tsl.rebuild-or (tsl.simp-disjuncts Fs Ctx []))
  [f-not F] Ctx -> (tsl.simp-not (tsl.simp F []))
  [f-imp A B] Ctx -> [f-imp (tsl.simp A Ctx) (tsl.simp B Ctx)]
  [f-iff A B] Ctx -> [f-iff (tsl.simp A Ctx) (tsl.simp B Ctx)]
  [f-some Bs F] Ctx -> [f-some Bs (tsl.simp F (tsl.ctx-drop Bs Ctx))]
  [f-all Bs F] Ctx -> [f-all Bs (tsl.simp F (tsl.ctx-drop Bs Ctx))]
  [f-all-types Vs F] Ctx -> [f-all-types Vs (tsl.simp F Ctx)]
  F Ctx -> (if (tsl.member-atom? F Ctx)
               [f-true]
               (if (tsl.refuted-atom? F Ctx) [f-false] F)))

(define tsl.simp-not
  [f-not G] -> G
  [f-true] -> [f-false]
  [f-false] -> [f-true]
  F -> [f-not F])

\\ Facts mentioning a rebound name cannot cross the binder.
(define tsl.ctx-drop
  Bs Ctx -> (tsl.ctx-drop-names (tsl.binding-names Bs) Ctx))

(define tsl.ctx-drop-names
  _ [] -> []
  Names [F | Fs] ->
    (if (tsl.mentions-any? (tsl.formula-vars F) Names)
        (tsl.ctx-drop-names Names Fs)
        [F | (tsl.ctx-drop-names Names Fs)]))

(define tsl.mentions-any?
  [] _ -> false
  [V | Vs] Names -> (if (element? V Names)
                        true
                        (tsl.mentions-any? Vs Names)))

(define tsl.simp-conjuncts
  [] _ Acc -> (reverse Acc)
  [F | Fs] Ctx Acc ->
    (let F1 (tsl.simp F (append Ctx (reverse Acc)))
      (if (= F1 [f-true])
          (tsl.simp-conjuncts Fs Ctx Acc)
          (if (cons? (tsl.and-members F1))
              (tsl.simp-conjuncts (append (tsl.and-members F1) Fs) Ctx Acc)
              (if (or (= F1 [f-false])
                      (tsl.refuted-atom? F1 (append Ctx (reverse Acc))))
                  [[f-false]]
                  (if (tsl.member-atom? F1 (append Ctx (reverse Acc)))
                      (tsl.simp-conjuncts Fs Ctx Acc)
                      (tsl.simp-conjuncts Fs Ctx [F1 | Acc])))))))

(define tsl.and-members
  [f-and Gs] -> Gs
  _ -> not-an-and)

(define tsl.or-members
  [f-or Gs] -> Gs
  _ -> not-an-or)

(define tsl.simp-disjuncts
  [] _ Acc -> (reverse Acc)
  [F | Fs] Ctx Acc ->
    (let Ctx1 (append Ctx (map (/. G (tsl.neg G)) (reverse Acc)))
      (let F1 (tsl.simp F Ctx1)
        (if (or (= F1 [f-false]) (tsl.refuted-atom? F1 Ctx1))
            (tsl.simp-disjuncts Fs Ctx Acc)
            (if (cons? (tsl.or-members F1))
                (tsl.simp-disjuncts (append (tsl.or-members F1) Fs) Ctx Acc)
                (if (or (= F1 [f-true]) (tsl.member-atom? F1 Ctx1))
                    [[f-true]]
                    (if (tsl.member-atom? F1 (reverse Acc))
                        (tsl.simp-disjuncts Fs Ctx Acc)
                        (tsl.simp-disjuncts Fs Ctx [F1 | Acc]))))))))

(define tsl.rebuild-and
  [] -> [f-true]
  [F] -> F
  Fs -> (if (element? [f-false] Fs) [f-false] [f-and Fs]))

(define tsl.rebuild-or
  [] -> [f-false]
  [F] -> F
  Fs -> (if (element? [f-true] Fs) [f-true] [f-or Fs]))

\\ Reduce an obligation list under fixed assumptions; assumptions are
\\ never deleted, only used.
(define tsl.simp-obligations
  Obligs Ctx -> (tsl.simp-conjuncts Obligs Ctx []))

(define tsl.pattern-terms
  [] -> []
  [P | Ps] -> [(tsl.pattern-term P) | (tsl.pattern-terms Ps)])

(define tsl.pattern-term
  [p-var X] -> [e-var X]
  [p-lit L] -> [e-value L]
  [p-ctor Tag Ps] -> [e-ctor Tag (tsl.pattern-terms Ps)]
  [p-wild] -> [e-var _])

\\ --- clause priority exclusions ------------------------------------------

(define tsl.exclusion-formulas
  [] _ _ _ -> []
  [TC | TCs] CurrentPs Avoid Totality ->
    (let App (tsl.applicable TC [] CurrentPs Avoid false Totality)
      (if (= App disjoint)
          (tsl.exclusion-formulas TCs CurrentPs Avoid Totality)
          [[f-not (hd (tl App))] |
           (tsl.exclusion-formulas TCs CurrentPs Avoid Totality)])))

\\ Whether a clause can fire on the given argument patterns.  Returns
\\ disjoint (statically impossible, justified by the constructor
\\ disjointness axioms and literal distinctness) or [formula F], where F
\\ existentially binds the clause's own unresolved variables.  Priors are
\\ earlier clauses whose exclusions are specialized against this clause's
\\ patterns and carried inside the same closure (used by the inversion
\\ axiom; the equations path passes [] because tsl.clause-conditions emits
\\ exclusions at the top level).
\\
\\ The clause is alpha-renamed away from the current names FIRST:
\\ substitution and existential closure are by symbol name, so a shared
\\ name would otherwise be captured and corrupt the formula.
(define tsl.applicable
  TC Priors CurrentPs Avoid WithOblig Totality ->
    (tsl.applicable1 (tsl.alpha-prior TC Avoid) Priors CurrentPs Avoid
      WithOblig Totality))

(define tsl.applicable1
  [t-clause I Ps G B Bindings] Priors CurrentPs Avoid WithOblig Totality ->
    (let M (tsl.match-pairs Ps CurrentPs [] [])
      (if (= M disjoint)
          disjoint
          (let Env (hd (tl M))
            (let Exts (tsl.exclusion-formulas Priors Ps
                        (append Avoid (tsl.binding-names Bindings))
                        Totality)
              (let Conds (tsl.subst-formulas (reverse (hd (tl (tl M)))) Env)
                (let Guard (tsl.subst-formulas
                             (tsl.guard-formula G) Env)
                  (let Obligs (if WithOblig
                                  (tsl.subst-formulas
                                    (tsl.unique-formulas
                                      (tsl.obligations B Totality))
                                    Env)
                                  [])
                    (let Assumed (append Conds
                                   (append (tsl.subst-formulas Exts Env)
                                     Guard))
                      (let All (append Assumed
                                 (tsl.simp-obligations Obligs Assumed))
                        (tsl.close-over All Bindings Env Avoid)))))))))))

\\ Rename any prior-clause variable that collides with a current-clause
\\ name (or with another renamed variable) to a fresh E-name.
(define tsl.alpha-prior
  [t-clause I Ps G B Bindings] Avoid ->
    (let Names (tsl.binding-names Bindings)
      (let Map (tsl.alpha-map Names Avoid Names [])
        (if (= Map [])
            [t-clause I Ps G B Bindings]
            [t-clause I (tsl.rename-patterns Ps Map)
             (tsl.rename-guard G Map)
             (tsl.subst-expr B (tsl.alpha-terms Map))
             (tsl.rename-bindings Bindings Map)]))))

(define tsl.alpha-map
  [] _ _ Acc -> (reverse Acc)
  [V | Vs] Avoid Others Acc ->
    (if (element? V Avoid)
        (let W (tsl.fresh-exist 0 (append Avoid (append Others
                                    (map (/. P (hd (tl P))) Acc))))
          (tsl.alpha-map Vs Avoid Others [[V W] | Acc]))
        (tsl.alpha-map Vs Avoid Others Acc)))

(define tsl.alpha-terms
  [] -> []
  [[V W] | Ms] -> [[V [e-var W]] | (tsl.alpha-terms Ms)])

(define tsl.rename-patterns
  [] _ -> []
  [P | Ps] Map -> [(tsl.rename-pattern P Map) | (tsl.rename-patterns Ps Map)])

(define tsl.rename-pattern
  [p-var X] Map -> (let F (tsl.env-lookup X Map)
                     (if (= F not-found) [p-var X] [p-var (hd (tl F))]))
  [p-ctor Tag Ps] Map -> [p-ctor Tag (tsl.rename-patterns Ps Map)]
  P _ -> P)

(define tsl.rename-guard
  none _ -> none
  [some G] Map -> [some (tsl.subst-expr G (tsl.alpha-terms Map))]
  G Map -> [some (tsl.subst-expr G (tsl.alpha-terms Map))])

(define tsl.rename-bindings
  [] _ -> []
  [[V T] | Bs] Map ->
    (let F (tsl.env-lookup V Map)
      [[(if (= F not-found) V (hd (tl F))) T] |
       (tsl.rename-bindings Bs Map)]))

\\ Existentially close a condition list over the prior clause's variables
\\ that were not resolved to current-clause terms, renaming to avoid
\\ capture.
(define tsl.close-over
  All Bindings Env Avoid ->
    (let Free (tsl.free-priors (tsl.binding-names Bindings) Env
                (tsl.formulas-vars All))
      (if (= Free [])
          [formula (tsl.flatten-and All)]
          (let Renames (tsl.rename-map Free Avoid [])
            [formula [f-some (tsl.renamed-bindings Free Renames Bindings)
                      (tsl.flatten-and
                        (tsl.subst-formulas All Renames))]]))))

(define tsl.free-priors
  [] _ _ -> []
  [V | Vs] Env Used ->
    (if (and (= (tsl.env-lookup V Env) not-found) (element? V Used))
        [V | (tsl.free-priors Vs Env Used)]
        (tsl.free-priors Vs Env Used)))

(define tsl.rename-map
  [] _ _ -> []
  [V | Vs] Avoid Taken ->
    (let W (if (or (element? V Avoid) (element? V Taken))
               (tsl.fresh-exist 0 (append Avoid Taken))
               V)
      [[V [e-var W]] | (tsl.rename-map Vs Avoid [W | Taken])]))

(define tsl.fresh-exist
  N Avoid -> (let V (intern (cn "E" (str N)))
               (if (element? V Avoid)
                   (tsl.fresh-exist (+ N 1) Avoid)
                   V)))

(define tsl.renamed-bindings
  [] _ _ -> []
  [V | Vs] Renames Bindings ->
    (let T (tsl.env-lookup V Bindings)
      (let R (tsl.env-lookup V Renames)
        [[(tsl.term-var (hd (tl R))) (if (= T not-found) value (hd (tl T)))] |
         (tsl.renamed-bindings Vs Renames Bindings)])))

(define tsl.term-var
  [e-var V] -> V)

\\ Match a prior clause's patterns against the current clause's patterns.
\\ Result: disjoint | [m Env Conds] with Env mapping prior variables to
\\ current terms and Conds accumulated in reverse.
(define tsl.match-pairs
  [] [] Env Conds -> [m Env Conds]
  [P | Ps] [A | As] Env Conds ->
    (let R (tsl.match-one P A Env Conds)
      (if (= R disjoint)
          disjoint
          (tsl.match-pairs Ps As (hd (tl R)) (hd (tl (tl R))))))
  _ _ _ _ -> disjoint)

(define tsl.match-one
  [p-wild] _ Env Conds -> [m Env Conds]
  [p-var X] A Env Conds ->
    (let Old (tsl.env-lookup X Env)
      (if (= Old not-found)
          [m [[X (tsl.pattern-term A)] | Env] Conds]
          [m Env [[f-eq (hd (tl Old)) (tsl.pattern-term A)] | Conds]]))
  [p-lit L] [p-lit L] Env Conds -> [m Env Conds]
  [p-lit _] [p-lit _] _ _ -> disjoint
  [p-lit L] [p-var V] Env Conds ->
    [m Env [[f-eq [e-var V] [e-value L]] | Conds]]
  [p-lit L] [p-wild] Env Conds -> [m Env Conds]
  [p-lit _] [p-ctor _ _] _ _ -> disjoint
  [p-ctor Tag Ps] [p-ctor Tag As] Env Conds ->
    (if (= (length Ps) (length As))
        (tsl.match-fields Ps As Env Conds)
        disjoint)
  [p-ctor _ _] [p-ctor _ _] _ _ -> disjoint
  [p-ctor Tag Ps] [p-var V] Env Conds ->
    [m Env [[f-eq [e-var V] [e-ctor Tag (tsl.pattern-terms Ps)]] | Conds]]
  [p-ctor Tag Ps] [p-wild] Env Conds -> [m Env Conds]
  [p-ctor _ _] [p-lit _] _ _ -> disjoint
  _ _ _ _ -> disjoint)

(define tsl.match-fields
  [] [] Env Conds -> [m Env Conds]
  [P | Ps] [A | As] Env Conds ->
    (let R (tsl.match-one P A Env Conds)
      (if (= R disjoint)
          disjoint
          (tsl.match-fields Ps As (hd (tl R)) (hd (tl (tl R)))))))

\\ --- definedness obligations ---------------------------------------------

(define tsl.obligations
  [e-var _] _ -> []
  [e-value _] _ -> []
  [e-ctor _ Args] Totality -> (tsl.obligations-list Args Totality)
  [e-prim _ Args] Totality -> (tsl.obligations-list Args Totality)
  [e-call F Args] Totality ->
    (append (tsl.obligations-list Args Totality)
            (if (tsl.total-function? F Totality)
                []
                [[f-defined (tsl.defined-name F) Args]]))
  [e-apply F Args] Totality ->
    (append (tsl.obligations-list Args Totality)
            [[f-defined (tsl.apply-defined-name (length Args))
              [[e-var F] | Args]]])
  \\ Obligations shared by both branches hold whichever way the condition
  \\ goes (excluded middle), so they factor out; only the residues stay
  \\ branch-conditional, and an empty residue collapses its side of the
  \\ disjunction (C or (~C and R) is equivalent to C or R).
  [e-if C T F] Totality ->
    (append (tsl.obligations C Totality)
      (let OT (tsl.unique-formulas (tsl.obligations T Totality))
        (let OF (tsl.unique-formulas (tsl.obligations F Totality))
          (let Common (tsl.inter-formulas OT OF)
            (let Rt (tsl.minus-formulas OT Common)
              (let Rf (tsl.minus-formulas OF Common)
                (append Common
                  (tsl.branch-residue (tsl.formula-of C) Rt Rf))))))))
  [e-and A B] Totality ->
    (append (tsl.obligations A Totality)
      (let OB (tsl.obligations B Totality)
        (if (= OB [])
            []
            [[f-or [[f-not (tsl.formula-of A)] (tsl.flatten-and OB)]]])))
  [e-or A B] Totality ->
    (append (tsl.obligations A Totality)
      (let OB (tsl.obligations B Totality)
        (if (= OB [])
            []
            [[f-or [(tsl.formula-of A) (tsl.flatten-and OB)]]])))
  \\ let is strict: the binding's obligations hold unconditionally even if
  \\ the body drops or branches on the bound variable.
  [e-let X A B] Totality ->
    (append (tsl.obligations A Totality)
            (tsl.obligations
              (tsl.subst-expr B [[X (tsl.inline A)]]) Totality))
  _ _ -> [])

(define tsl.inter-formulas
  [] _ -> []
  [F | Fs] Gs -> (if (element? F Gs)
                     [F | (tsl.inter-formulas Fs Gs)]
                     (tsl.inter-formulas Fs Gs)))

(define tsl.minus-formulas
  [] _ -> []
  [F | Fs] Gs -> (if (element? F Gs)
                     (tsl.minus-formulas Fs Gs)
                     [F | (tsl.minus-formulas Fs Gs)]))

(define tsl.branch-residue
  _ [] [] -> []
  C [] Rf -> [[f-or [C (tsl.flatten-and Rf)]]]
  C Rt [] -> [[f-or [[f-not C] (tsl.flatten-and Rt)]]]
  C Rt Rf -> [[f-or [(tsl.flatten-and [C | Rt])
                     (tsl.flatten-and [[f-not C] | Rf])]]])

(define tsl.obligations-list
  [] _ -> []
  [E | Es] Totality -> (append (tsl.obligations E Totality)
                               (tsl.obligations-list Es Totality)))

\\ --- boolean expressions as formulas -------------------------------------

(define tsl.formula-of
  [e-value true] -> [f-true]
  [e-value false] -> [f-false]
  [e-prim = [A B]] -> [f-eq A B]
  [e-prim neq [A B]] -> [f-not [f-eq A B]]
  [e-prim < [A B]] -> [f-cmp < A B]
  [e-prim > [A B]] -> [f-cmp > A B]
  [e-prim <= [A B]] -> [f-cmp <= A B]
  [e-prim >= [A B]] -> [f-cmp >= A B]
  [e-and A B] -> [f-and [(tsl.formula-of A) (tsl.formula-of B)]]
  [e-or A B] -> [f-or [(tsl.formula-of A) (tsl.formula-of B)]]
  E -> [f-eq E [e-value true]])

\\ --- let inlining --------------------------------------------------------

(define tsl.inline
  [e-let X A B] -> (tsl.subst-expr (tsl.inline B) [[X (tsl.inline A)]])
  [e-ctor Tag Args] -> [e-ctor Tag (map (/. E (tsl.inline E)) Args)]
  [e-call F Args] -> [e-call F (map (/. E (tsl.inline E)) Args)]
  [e-apply F Args] -> [e-apply F (map (/. E (tsl.inline E)) Args)]
  [e-prim Op Args] -> [e-prim Op (map (/. E (tsl.inline E)) Args)]
  [e-if C T F] -> [e-if (tsl.inline C) (tsl.inline T) (tsl.inline F)]
  [e-and A B] -> [e-and (tsl.inline A) (tsl.inline B)]
  [e-or A B] -> [e-or (tsl.inline A) (tsl.inline B)]
  E -> E)

\\ --- substitution --------------------------------------------------------

(define tsl.subst-expr
  [e-var X] Env -> (let F (tsl.env-lookup X Env)
                     (if (= F not-found) [e-var X] (hd (tl F))))
  [e-ctor Tag Args] Env -> [e-ctor Tag (tsl.subst-exprs Args Env)]
  [e-call F Args] Env -> [e-call F (tsl.subst-exprs Args Env)]
  [e-apply F Args] Env -> [e-apply (tsl.subst-head F Env)
                                   (tsl.subst-exprs Args Env)]
  [e-prim Op Args] Env -> [e-prim Op (tsl.subst-exprs Args Env)]
  [e-if C T F] Env -> [e-if (tsl.subst-expr C Env) (tsl.subst-expr T Env)
                            (tsl.subst-expr F Env)]
  [e-and A B] Env -> [e-and (tsl.subst-expr A Env) (tsl.subst-expr B Env)]
  [e-or A B] Env -> [e-or (tsl.subst-expr A Env) (tsl.subst-expr B Env)]
  [e-let X A B] Env -> [e-let X (tsl.subst-expr A Env)
                              (tsl.subst-expr B (tsl.env-drop X Env))]
  E _ -> E)

(define tsl.subst-exprs
  [] _ -> []
  [E | Es] Env -> [(tsl.subst-expr E Env) | (tsl.subst-exprs Es Env)])

(define tsl.env-drop
  _ [] -> []
  X [[X _] | Rest] -> (tsl.env-drop X Rest)
  X [B | Rest] -> [B | (tsl.env-drop X Rest)])

\\ An apply head is a variable; substitution can rename it or replace it by
\\ a named function.
(define tsl.subst-head
  F Env -> (let R (tsl.env-lookup F Env)
             (if (= R not-found) F (tsl.head-name (hd (tl R)) F))))

(define tsl.head-name
  [e-var G] _ -> G
  [e-value S] _ -> S
  _ F -> F)

(define tsl.subst-formulas
  [] _ -> []
  [F | Fs] Env -> [(tsl.subst-formula F Env) | (tsl.subst-formulas Fs Env)])

(define tsl.subst-formula
  [f-eq A B] Env -> [f-eq (tsl.subst-expr A Env) (tsl.subst-expr B Env)]
  [f-cmp Op A B] Env -> [f-cmp Op (tsl.subst-expr A Env)
                               (tsl.subst-expr B Env)]
  [f-not F] Env -> [f-not (tsl.subst-formula F Env)]
  [f-and Fs] Env -> [f-and (tsl.subst-formulas Fs Env)]
  [f-or Fs] Env -> [f-or (tsl.subst-formulas Fs Env)]
  [f-imp F G] Env -> [f-imp (tsl.subst-formula F Env)
                            (tsl.subst-formula G Env)]
  [f-iff F G] Env -> [f-iff (tsl.subst-formula F Env)
                            (tsl.subst-formula G Env)]
  [f-defined N Ts] Env -> [f-defined N (tsl.subst-exprs Ts Env)]
  [f-pred P Ts] Env -> [f-pred P (tsl.subst-exprs Ts Env)]
  [f-some Bs F] Env ->
    [f-some Bs (tsl.subst-formula F
                 (tsl.env-drop-all (tsl.binding-names Bs) Env))]
  [f-all Bs F] Env ->
    [f-all Bs (tsl.subst-formula F
                (tsl.env-drop-all (tsl.binding-names Bs) Env))]
  F _ -> F)

(define tsl.env-drop-all
  [] Env -> Env
  [X | Xs] Env -> (tsl.env-drop-all Xs (tsl.env-drop X Env)))

\\ --- variable collection -------------------------------------------------

(define tsl.formulas-vars
  [] -> []
  [F | Fs] -> (append (tsl.formula-vars F) (tsl.formulas-vars Fs)))

(define tsl.formula-vars
  [f-eq A B] -> (append (tsl.expr-vars A) (tsl.expr-vars B))
  [f-cmp _ A B] -> (append (tsl.expr-vars A) (tsl.expr-vars B))
  [f-not F] -> (tsl.formula-vars F)
  [f-and Fs] -> (tsl.formulas-vars Fs)
  [f-or Fs] -> (tsl.formulas-vars Fs)
  [f-imp F G] -> (append (tsl.formula-vars F) (tsl.formula-vars G))
  [f-iff F G] -> (append (tsl.formula-vars F) (tsl.formula-vars G))
  [f-defined _ Ts] -> (tsl.exprs-vars Ts)
  [f-pred _ Ts] -> (tsl.exprs-vars Ts)
  [f-some _ F] -> (tsl.formula-vars F)
  [f-all _ F] -> (tsl.formula-vars F)
  [f-all-types _ F] -> (tsl.formula-vars F)
  _ -> [])

\\ --- type-variable quantification ----------------------------------------

(define tsl.quantify-types
  F -> (let TVars (tsl.unique-keep-first (tsl.formula-tvars F) [])
         (if (= TVars []) F [f-all-types TVars F])))

(define tsl.unique-keep-first
  [] _ -> []
  [X | Xs] Seen -> (if (element? X Seen)
                       (tsl.unique-keep-first Xs Seen)
                       [X | (tsl.unique-keep-first Xs [X | Seen])]))

(define tsl.formula-tvars
  [f-some Bs F] -> (append (tsl.bindings-tvars Bs) (tsl.formula-tvars F))
  [f-all Bs F] -> (append (tsl.bindings-tvars Bs) (tsl.formula-tvars F))
  [f-not F] -> (tsl.formula-tvars F)
  [f-and Fs] -> (tsl.formulas-tvars Fs)
  [f-or Fs] -> (tsl.formulas-tvars Fs)
  [f-imp F G] -> (append (tsl.formula-tvars F) (tsl.formula-tvars G))
  [f-iff F G] -> (append (tsl.formula-tvars F) (tsl.formula-tvars G))
  [f-all-pred _ Args F] -> (append (tsl.types-tvars Args)
                                   (tsl.formula-tvars F))
  _ -> [])

(define tsl.types-tvars
  [] -> []
  [T | Ts] -> (append (reverse (tsl.tvars-type T []))
                      (tsl.types-tvars Ts)))

(define tsl.formulas-tvars
  [] -> []
  [F | Fs] -> (append (tsl.formula-tvars F) (tsl.formulas-tvars Fs)))

(define tsl.bindings-tvars
  [] -> []
  [[_ T] | Bs] -> (append (reverse (tsl.tvars-type T []))
                          (tsl.bindings-tvars Bs)))

\\ --- rendering -----------------------------------------------------------

(define tsl.render-formula
  [f-true] -> "true"
  [f-false] -> "false"
  [f-eq A B] -> (@s "(" (tsl.render-term A) " = " (tsl.render-term B) ")")
  [f-cmp Op A B] -> (@s "(" (str Op) " " (tsl.render-term A) " "
                        (tsl.render-term B) ")")
  [f-not F] -> (@s "(~ " (tsl.render-formula F) ")")
  [f-and []] -> "true"
  [f-and [F]] -> (tsl.render-formula F)
  [f-and Fs] -> (@s "(and " (tsl.render-formulas Fs) ")")
  [f-or []] -> "false"
  [f-or [F]] -> (tsl.render-formula F)
  [f-or Fs] -> (@s "(or " (tsl.render-formulas Fs) ")")
  [f-imp F G] -> (@s "(" (tsl.render-formula F) " => "
                     (tsl.render-formula G) ")")
  [f-iff F G] -> (@s "(" (tsl.render-formula F) " <=> "
                     (tsl.render-formula G) ")")
  [f-defined N []] -> (@s "(" (str N) ")")
  [f-defined N Ts] -> (@s "(" (str N) " " (tsl.render-terms Ts) ")")
  [f-pred P []] -> (@s "(" (str P) ")")
  [f-pred P Ts] -> (@s "(" (str P) " " (tsl.render-terms Ts) ")")
  [f-some [] F] -> (tsl.render-formula F)
  [f-some [[V T] | Bs] F] ->
    (@s "(some " (str V) " : " (tsl.render-type T) " "
        (tsl.render-formula [f-some Bs F]) ")")
  [f-all [] F] -> (tsl.render-formula F)
  [f-all [[V T] | Bs] F] ->
    (@s "(all " (str V) " : " (tsl.render-type T) " "
        (tsl.render-formula [f-all Bs F]) ")")
  [f-all-types [] F] -> (tsl.render-formula F)
  [f-all-types [A | As] F] ->
    (@s "(all " (str A) " : type "
        (tsl.render-formula [f-all-types As F]) ")")
  [f-all-pred P Args F] ->
    (@s "(all " (str P) " : " (tsl.pred-type Args) " "
        (tsl.render-formula F) ")"))

(define tsl.render-formulas
  [] -> ""
  [F] -> (tsl.render-formula F)
  [F | Fs] -> (@s (tsl.render-formula F) " " (tsl.render-formulas Fs)))

(define tsl.render-term
  [e-var X] -> (str X)
  [e-value V] -> (tsl.render-literal V)
  [e-ctor nil []] -> "()"
  [e-ctor Tag []] -> (@s "(" (str Tag) ")")
  [e-ctor Tag Args] -> (@s "(" (str Tag) " " (tsl.render-terms Args) ")")
  [e-call F []] -> (@s "(" (str F) ")")
  [e-call F Args] -> (@s "(" (str F) " " (tsl.render-terms Args) ")")
  [e-apply F Args] -> (@s "(" (str F) " " (tsl.render-terms Args) ")")
  [e-prim Op Args] -> (@s "(" (str Op) " " (tsl.render-terms Args) ")")
  [e-if C T F] -> (@s "(if " (tsl.render-term C) " " (tsl.render-term T)
                      " " (tsl.render-term F) ")")
  [e-and A B] -> (@s "(and " (tsl.render-term A) " " (tsl.render-term B) ")")
  [e-or A B] -> (@s "(or " (tsl.render-term A) " " (tsl.render-term B) ")")
  X -> (str X))

(define tsl.render-terms
  [] -> ""
  [T] -> (tsl.render-term T)
  [T | Ts] -> (@s (tsl.render-term T) " " (tsl.render-terms Ts)))

(define tsl.render-literal
  V -> (if (string? V)
           (@s (n->string 34) V (n->string 34))
           (str V)))

(define tsl.render-type
  [list T] -> (@s "(list " (tsl.render-type T) ")")
  [arrow Args R] -> (@s "(" (tsl.render-arrow-parts (append Args [R])) ")")
  T -> (str T))

(define tsl.render-arrow-parts
  [T] -> (tsl.render-type T)
  [T | Ts] -> (@s (tsl.render-type T) " --> " (tsl.render-arrow-parts Ts)))
