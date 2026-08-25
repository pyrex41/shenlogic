\\ ShenLogic deterministic Shen-native regression runner.
\\ This file is the Bifrost script entrypoint.  It deliberately uses only
\\ ShenLogic's public API and emits one machine-readable completion marker.

(load "shenlogic.shen")
(load "tests/certificate.shen")

(define sl-check
  Label true -> (do (output (cn "PASS " (cn Label "~%"))) true)
  Label _ -> (do (output (cn "FAIL " (cn Label "~%"))) false))

(define sl-all-true
  [] -> true
  [true | Xs] -> (sl-all-true Xs)
  _ -> false)

(define sl-render
  Path Format -> (shenlogic.translate-file Path Format))

(define sl-eval
  Path Expr -> (shenlogic.evaluate-file Path Expr 2000))

(define sl-read
  Path -> (read-file-as-string Path))

(define sl-rejected?
  Path -> (trap-error (do (shenlogic.program Path) false) (/. E true)))

(define sl-translation-rejected?
  Path Format -> (trap-error (do (shenlogic.translate-file Path Format) false)
                              (/. E true)))

(define sl-translation-succeeds?
  Path Format -> (trap-error (do (shenlogic.translate-file Path Format) true)
                             (/. E false)))

(define sl-has-tag?
  Tag X -> (if (cons? X)
               (or (= (hd X) Tag) (sl-has-tag-list? Tag X))
               false))

(define sl-has-tag-list?
  _ [] -> false
  Tag [X | Xs] -> (or (sl-has-tag? Tag X) (sl-has-tag-list? Tag Xs)))

(define sl-has-form?
  Form X -> (if (= Form X)
                true
                (if (cons? X) (sl-has-form-list? Form X) false)))

(define sl-has-form-list?
  _ [] -> false
  Form [X | Xs] ->
    (or (sl-has-form? Form X) (sl-has-form-list? Form Xs)))

(define sl-repair-factorial
  Spec MaxCost -> (shenlogic.repair-file "examples/factorial.shen"
                    "tests/fixtures/repair-factorial.tsl.logic"
                    Spec 2000 100 MaxCost))

(define sl-repair-ordered
  -> (shenlogic.repair-file "examples/ordered.shen"
        "tests/fixtures/repair-ordered.tsl.logic"
        "tests/fixtures/repair-ordered.spec" 2000 100 50))

(define sl-repair-query
  [ok _ _ _ _ Query] -> Query
  _ -> "")

(define sl-repair-program
  [ok _ _ Source _] ->
    (let Parsed (shenlogic.reader.parse-program
                  (read-from-string-unprocessed Source))
      (if (= (hd Parsed) ok)
          (shenlogic.ast.normalize-program (hd (tl Parsed)))
          [program []]))
  _ -> [program []])


(define sl-repair-source
  [ok _ _ Source _] -> Source
  _ -> "")

\\ Write the spliced source, then retranslate the file.  This is the
\\ PO11 composition: translate(written splice) vs the edited view.
(define sl-written-retranslate?
  "" _ -> false
  Source LogicFile ->
    (let Path "tests/repair-roundtrip-splice.shen"
      (do (write-to-file Path Source)
        (let Got (repair.parse-tsl (sl-render Path "tsl"))
          (let Want (repair.parse-tsl (sl-read LogicFile))
            (and (= (hd Got) ok)
                 (= (hd Want) ok)
                 (= (hd (tl Got)) (hd (tl Want)))
                 (= (repair.alpha-list-top (hd (tl (tl Got))))
                    (repair.alpha-list-top (hd (tl (tl Want)))))))))))

(define sl-repair-templates
  File Logic Name ->
    (let Raw (shenlogic.source-program File)
      (let EP (repair.parse-tsl (read-file-as-string Logic))
        (if (= (hd EP) ok)
            (let Eqs (repair.equations-for Name (hd (tl (tl EP))))
              (let Def (repair.find-definition Name
                         (shenlogic.ast.program-definitions Raw))
                (if (= Def not-found)
                    [error not-found Name]
                    (repair.templates Eqs Name
                      (shenlogic.ast.definition-clauses Def) []))))
            EP))))

(define sl-alpha-eq
  V -> [all V : number
         [[and [~ [V = 0]] [defined-factorial [- V 1]]]
          => [[factorial V] = [* V [factorial [- V 1]]]]]])

\\ Hand-built guard pools for PO13.  Not inverted from a tsl file.
(define sl-search-pool-2x2
  -> [[template 0 [x] 1 [a b]]
      [template 1 [y] 2 [c d]]])

(define sl-search-pool-none
  -> [[template 0 [x] 1 [[some true] [some false] none]]])

(define sl-run
  -> (let Results
         [(sl-check "factorial-surface"
                    (= (sl-render "examples/factorial.shen" "surface")
                       (sl-read "tests/golden/factorial.surface.logic")))
          (sl-check "factorial-graph"
                    (= (sl-render "examples/factorial.shen" "graph")
                       (sl-read "tests/golden/factorial.graph.logic")))
          (sl-check "fib-surface"
                    (= (sl-render "examples/fib.shen" "surface")
                       (sl-read "tests/golden/fib.surface.logic")))
          (sl-check "mutual-graph"
                    (= (sl-render "examples/mutual.shen" "graph")
                       (sl-read "tests/golden/mutual.graph.logic")))
          (sl-check "v2-mutual-graph"
                    (= (sl-render "examples/v2-mutual.shen" "graph")
                       (sl-read "tests/golden/v2-mutual.graph.logic")))
          (sl-check "ordered-surface"
                    (= (sl-render "examples/ordered.shen" "surface")
                       (sl-read "tests/golden/ordered.surface.logic")))
          (sl-check "guards-graph"
                    (= (sl-render "examples/guards.shen" "graph")
                       (sl-read "tests/golden/guards.graph.logic")))
          (sl-check "lists-graph"
                    (= (sl-render "examples/lists.shen" "graph")
                       (sl-read "tests/golden/lists.graph.logic")))
          (sl-check "factorial-slir"
                    (= (sl-render "examples/factorial.shen" "slir")
                       (sl-read "tests/golden/factorial.slir")))
          (sl-check "factorial-chc"
                    (= (sl-render "examples/factorial.shen" "chc")
                       (sl-read "tests/golden/factorial.chc")))
          (sl-check "factorial-thf"
                    (= (sl-render "examples/factorial.shen" "thf")
                       (sl-read "tests/golden/factorial.thf")))
          (sl-check "mutual-thf"
                    (= (sl-render "examples/mutual.shen" "thf")
                       (sl-read "tests/golden/mutual.thf")))
          (sl-check "factorial-tsl"
                    (= (sl-render "examples/factorial.shen" "tsl")
                       (sl-read "tests/golden/factorial.tsl.logic")))
          (sl-check "d-tsl"
                    (= (sl-render "examples/d.shen" "tsl")
                       (sl-read "tests/golden/d.tsl.logic")))
          (sl-check "repair-factorial-edited-equation"
                    (let R (sl-repair-factorial
                              "tests/fixtures/repair-factorial.spec" 4)
                      (and (= (hd R) ok)
                           (= (hd (tl R)) factorial)
                           (= (hd (tl (tl R))) 1)
                           (= (evaluator-evaluate (sl-repair-program R)
                                [factorial 1] 2000)
                              [value 2]))))
          (sl-check "repair-respects-max-cost"
                    (= (sl-repair-factorial
                         "tests/fixtures/repair-factorial.spec" 0)
                       [error repair-no-candidate]))
          (sl-check "repair-rejects-example-mismatch"
                    (= (sl-repair-factorial
                         "tests/fixtures/repair-factorial-bad.spec" 4)
                       [error repair-no-candidate]))
          (sl-check "repair-whole-definition-edit"
                    (let R (sl-repair-ordered)
                      (and (= (hd R) ok)
                           (= (hd (tl (tl (tl R))))
                              (sl-read
                                "tests/fixtures/repair-ordered.expected.shen")))))
          (sl-check "repair-preserves-declared-signature-style"
                    (let R (shenlogic.repair-file
                              "tests/fixtures/declared.shen"
                              "tests/fixtures/repair-declared.tsl.logic"
                              "tests/fixtures/repair-declared.spec"
                              2000 100 10)
                      (and (= (hd R) ok)
                           (= (hd (tl (tl (tl R))))
                              (sl-read
                                "tests/fixtures/repair-declared.expected.shen")))))
          (sl-check "repair-preserves-wildcard-patterns"
                    (let R (shenlogic.repair-file
                              "examples/tsl-values.shen"
                              "tests/fixtures/repair-wildcard.tsl.logic"
                              "tests/fixtures/repair-wildcard.spec"
                              2000 100 10)
                      (and (= (hd R) ok)
                           (= (hd (tl (tl (tl R))))
                              (sl-read
                                "tests/fixtures/repair-wildcard.expected.shen")))))
          (sl-check "repair-rejects-law-without-solver"
                    (= (sl-repair-factorial
                         "tests/fixtures/repair-factorial-law.spec" 4)
                       [error repair-law-solver-required]))
          (sl-check "repair-prepares-quantified-law"
                    (let R (shenlogic.repair-prepare-file
                              "examples/factorial.shen"
                              "tests/fixtures/repair-factorial.tsl.logic"
                              "tests/fixtures/repair-factorial-law-true.spec"
                              2000 100 4)
                      (and (= (hd R) ok)
                           (not (= (sl-repair-query R) "")))))
          (sl-check "repair-ranked-candidates-exhaust"
                    (= (shenlogic.repair-prepare-file-nth
                         "examples/factorial.shen"
                         "tests/fixtures/repair-factorial.tsl.logic"
                         "tests/fixtures/repair-factorial.spec"
                         2000 100 4 1)
                       [error repair-no-candidate]))
          (sl-check "repair-rejects-noop-logic"
                    (= (shenlogic.repair-file "examples/factorial.shen"
                         "tests/golden/factorial.tsl.logic"
                         "tests/fixtures/repair-factorial.spec" 2000 100 4)
                       [error repair-no-equation-change]))
          (sl-check "repair-rejects-scaffolding-edit"
                    (= (shenlogic.repair-file "examples/factorial.shen"
                         "tests/fixtures/repair-factorial-scaffold.tsl.logic"
                         "tests/fixtures/repair-factorial.spec" 2000 100 4)
                       [error repair-edited-scaffolding]))
          (sl-check "repair-templates-factorial"
                    (let X (intern "X")
                      (= (sl-repair-templates "examples/factorial.shen"
                            "tests/fixtures/repair-factorial.tsl.logic" factorial)
                         [ok [[template 0 [0] 2 [[some true] none]]
                              [template 1 [X] [* X [factorial [- X 1]]] [none]]]])))
          (sl-check "repair-templates-ordered"
                    (let X (intern "X")
                      (= (sl-repair-templates "examples/ordered.shen"
                            "tests/fixtures/repair-ordered.tsl.logic" classify)
                         [ok [[template 0 [X] nonpositive
                                [[some [< X 0]] [some [<= X 0]] none]]
                              [template 1 [1] one [none]]
                              [template 2 [2] two [none]]
                              [template 3 [X] positive [none]]]])))
          (sl-check "repair-templates-declared"
                    (let X (intern "X")
                      (= (sl-repair-templates "tests/fixtures/declared.shen"
                            "tests/fixtures/repair-declared.tsl.logic" declared-id)
                         [ok [[template 0 [X] [+ X 1] [[some true] none]]]])))
          (sl-check "repair-templates-wildcard"
                    (= (sl-repair-templates "examples/tsl-values.shen"
                          "tests/fixtures/repair-wildcard.tsl.logic" box-name)
                       [ok [[template 0 [[box _]] boxed-again [[some true] none]]
                            [template 1 [[pair _ _]] paired [[some true] none]]]]))
          (sl-check "repair-alpha-binder-rename"
                    (= (repair.alpha (sl-alpha-eq (intern "X")))
                       (repair.alpha (sl-alpha-eq (intern "N")))))

          (sl-check "repair-splice-retranslates-factorial"
                    (let R (sl-repair-factorial
                              "tests/fixtures/repair-factorial.spec" 4)
                      (and (= (hd R) ok)
                           (sl-written-retranslate? (sl-repair-source R)
                             "tests/fixtures/repair-factorial.tsl.logic"))))
          (sl-check "repair-enum-2x2-product"
                    (= (repair.guard-selections (sl-search-pool-2x2) 100)
                       [[b d] [b c] [a d] [a c]]))
          (sl-check "repair-enum-limit-drops-none"
                    (= (repair.guard-selections (sl-search-pool-none) 2)
                       [[[some false]] [[some true]]]))
          (sl-check "repair-rank-equal-cost-canonical"
                    (and (= (repair.insert-best [best 1 "zz" z z]
                              (repair.insert-best [best 1 "aa" a a] []))
                            [[best 1 "aa" a a] [best 1 "zz" z z]])
                         (= (repair.insert-best [best 1 "aa" a a]
                              (repair.insert-best [best 1 "zz" z z] []))
                            [[best 1 "aa" a a] [best 1 "zz" z z]])))
          (sl-check "tsl-rejects-missing-signature"
                    (sl-translation-rejected?
                      "tests/fixtures/tsl-no-signature.shen" "tsl"))
          (sl-check "tsl-rejects-sort-mixing"
                    (sl-translation-rejected?
                      "examples/v2-constructors.shen" "tsl"))
          (sl-check "tsl-guards-supported"
                    (sl-translation-succeeds? "examples/guards.shen" "tsl"))
          (sl-check "tsl-mutual-supported"
                    (sl-translation-succeeds? "examples/mutual.shen" "tsl"))
          (sl-check "tsl-lists-tsl"
                    (= (sl-render "examples/tsl-lists.shen" "tsl")
                       (sl-read "tests/golden/tsl-lists.tsl.logic")))
          (sl-check "tsl-values-tsl"
                    (= (sl-render "examples/tsl-values.shen" "tsl")
                       (sl-read "tests/golden/tsl-values.tsl.logic")))
          (sl-check "tsl-lists-eval"
                    (= (sl-eval "examples/tsl-lists.shen"
                                "(append2 [1 2] [3])")
                       [value [1 2 3]]))
          (sl-check "ho-map-eval"
                    (= (sl-eval "examples/v2-map.shen" "(map double [1 2 3])")
                       [value [2 4 6]]))
          (sl-check "ho-map-empty-eval"
                    (= (sl-eval "examples/v2-map.shen" "(map double [])")
                       [value []]))
          (sl-check "ho-filter-eval"
                    (= (sl-eval "examples/v2-map.shen"
                                "(filter positive? [1 -2 3])")
                       [value [1 3]]))
          (sl-check "ho-twice-eval"
                    (= (sl-eval "examples/v2-map.shen" "(twice double 3)")
                       [value 12]))
          (sl-check "reject-ho-no-signature"
                    (sl-rejected? "tests/fixtures/ho-no-signature.shen"))
          (sl-check "reject-ho-partial-apply"
                    (sl-rejected? "tests/fixtures/ho-partial-apply.shen"))
          (sl-check "reject-ho-result-arrow"
                    (sl-rejected? "tests/fixtures/ho-result-arrow.shen"))
          (sl-check "reject-ho-nested-arrow"
                    (sl-rejected? "tests/fixtures/ho-nested-arrow.shen"))
          (sl-check "reject-ho-escape"
                    (sl-rejected? "tests/fixtures/ho-escape.shen"))
          (sl-check "reject-ho-bad-fn-arg"
                    (sl-rejected? "tests/fixtures/ho-bad-fn-arg.shen"))
          (sl-check "reject-ho-reserved-name"
                    (sl-rejected? "tests/fixtures/ho-reserved-name.shen"))
          (sl-check "map-graph"
                    (= (sl-render "examples/v2-map.shen" "graph")
                       (sl-read "tests/golden/map.graph.logic")))
          (sl-check "map-slir"
                    (= (sl-render "examples/v2-map.shen" "slir")
                       (sl-read "tests/golden/map.slir")))
          (sl-check "map-chc"
                    (= (sl-render "examples/v2-map.shen" "chc")
                       (sl-read "tests/golden/map.chc")))
          (sl-check "map-thf"
                    (= (sl-render "examples/v2-map.shen" "thf")
                       (sl-read "tests/golden/map.thf")))
          (sl-check "map-surface"
                    (= (sl-render "examples/v2-map.shen" "surface")
                       (sl-read "tests/golden/map.surface.logic")))
          (sl-check "map-certificate"
                    (certificate-test-file-success "examples/v2-map.shen"))
          (sl-check "map-tsl"
                    (= (sl-render "examples/v2-map.shen" "tsl")
                       (sl-read "tests/golden/map.tsl.logic")))
          (sl-check "tsl-regress-tsl"
                    (= (sl-render "examples/tsl-regress.shen" "tsl")
                       (sl-read "tests/golden/tsl-regress.tsl.logic")))
          (sl-check "tsl-simplify-tsl"
                    (= (sl-render "examples/tsl-simplify.shen" "tsl")
                       (sl-read "tests/golden/tsl-simplify.tsl.logic")))
          (sl-check "tsl-linarith-tsl"
                    (= (sl-render "examples/tsl-linarith.shen" "tsl")
                       (sl-read "tests/golden/tsl-linarith.tsl.logic")))
          (sl-check "linarith-eval-countdown"
                    (= (sl-eval "examples/tsl-linarith.shen" "(countdown 7)")
                       [value 0]))
          (sl-check "linarith-eval-countup"
                    (= (sl-eval "examples/tsl-linarith.shen" "(countup -3)")
                       [value 1]))
          (sl-check "linarith-classify"
                    (= (termination.classify
                         (shenlogic.program "examples/tsl-linarith.shen"))
                       [totality [[countdown total [int-measure 0]]
                                  [halveish total [int-measure 0]]
                                  [countup total [int-ascent 0]]
                                  [wobble unknown [no-descent]]]]))
          (sl-check "simp-unit-context-drop"
                    (= (tsl.simp-obligations
                         [[f-defined d [[e-var vx]]]
                          [f-or [[f-not [f-cmp < [e-var vx] [e-value 0]]]
                                 [f-defined d [[e-var vx]]]]]]
                         [])
                       [[f-defined d [[e-var vx]]]]))
          (sl-check "simp-unit-complement"
                    (= (tsl.simp [f-and [[f-defined d [[e-var vx]]]
                                         [f-not [f-defined d [[e-var vx]]]]]]
                                 [])
                       [f-false]))
          (sl-check "simp-unit-units-flatten"
                    (= (tsl.simp [f-and [[f-true]
                                         [f-and [[f-defined d [[e-var vx]]]
                                                 [f-true]]]]]
                                 [])
                       [f-defined d [[e-var vx]]]))
          (sl-check "simp-unit-fail-closed"
                    (= (tsl.simp [f-or [[f-cmp < [e-var vx] [e-value 0]]
                                        [f-defined d [[e-var vx]]]]]
                                 [])
                       [f-or [[f-cmp < [e-var vx] [e-value 0]]
                              [f-defined d [[e-var vx]]]]]))
          (sl-check "simp-unit-linarith-equal"
                    (= (tsl.simp [f-cmp < [e-prim + [[e-var vx] [e-value 0]]]
                                  [e-value 2]]
                                 [[f-cmp < [e-var vx] [e-value 2]]])
                       [f-true]))
          (sl-check "simp-unit-swapped-spelling"
                    (= (tsl.simp [f-cmp > [e-value 2] [e-var vx]]
                                 [[f-cmp < [e-var vx] [e-value 2]]])
                       [f-true]))
          (sl-check "simp-unit-trichotomy"
                    (= (tsl.simp [f-cmp >= [e-var vx] [e-value 0]]
                                 [[f-cmp < [e-var vx] [e-value 0]]])
                       [f-false]))
          (sl-check "simp-unit-linarith-fail-closed"
                    (= (tsl.simp [f-cmp < [e-var vx] [e-value 2]]
                                 [[f-cmp < [e-var vx] [e-value 3]]])
                       [f-cmp < [e-var vx] [e-value 2]]))
          (sl-check "simp-unit-idempotent"
                    (let Once (tsl.simp [f-and [[f-defined d [[e-var vx]]]
                                                [f-or [[f-cmp < [e-var vx]
                                                        [e-value 0]]
                                                       [f-defined g
                                                        [[e-var vx]]]]]]]
                                        [])
                      (= (tsl.simp Once []) Once)))
          (sl-check "term-nonlinear-unknown"
                    (= (termination.classify
                         (shenlogic.program "tests/fixtures/term-nonlinear.shen"))
                       [totality [[part unknown [non-exhaustive part]]
                                  [h2 unknown [non-exhaustive h2]]]]))
          (sl-check "term-shadow-unknown"
                    (= (termination.classify
                         (shenlogic.program "tests/fixtures/term-shadow.shen"))
                       [totality [[spin unknown [no-descent]]
                                  [grow unknown [no-descent]]]]))
          (sl-check "reject-name-collision-chc"
                    (sl-translation-rejected?
                      "tests/fixtures/name-collide.shen" "chc"))
          (sl-check "reject-name-collision-thf"
                    (sl-translation-rejected?
                      "tests/fixtures/name-collide.shen" "thf"))
          (sl-check "reject-apply-name-collision-chc"
                    (sl-translation-rejected?
                      "tests/fixtures/name-collide-apply.shen" "chc"))
          (sl-check "body-cons-eval"
                    (= (sl-eval "tests/fixtures/body-cons.shen" "(wrap 5)")
                       [value [5]]))
          (sl-check "body-cons-chc"
                    (sl-translation-succeeds?
                      "tests/fixtures/body-cons.shen" "chc"))
          (sl-check "reject-ho-guard-escape"
                    (sl-rejected? "tests/fixtures/ho-guard-escape.shen"))
          (sl-check "map-query-chc"
                    (= (hd (shenlogic.query-file "examples/v2-map.shen"
                             "(map double [1 2])" "[2 4]" "chc"))
                       ok))
          (sl-check "strict-let-eval"
                    (= (sl-eval "examples/strict.shen" "(strict-probe 4)")
                       [value 10]))
          (sl-check "guard-false-fallback"
                    (= (sl-eval "examples/guards.shen" "(sign 0)")
                       [value zero]))
          (sl-check "guard-negative-clause"
                    (= (sl-eval "examples/guards.shen" "(sign -2)")
                       [value negative]))
          (sl-check "total-guard-graph-supported"
                    (sl-translation-succeeds? "examples/guards.shen" "graph"))
          (sl-check "total-guard-chc-supported"
                    (sl-translation-succeeds? "examples/guards.shen" "chc"))
          (sl-check "total-guard-thf-supported"
                    (sl-translation-succeeds? "examples/guards.shen" "thf"))
          (sl-check "factorial-eval-5"
                    (= (sl-eval "examples/factorial.shen" "(factorial 5)")
                       [value 120]))
          (sl-check "factorial-query-chc"
                    (let R (shenlogic.query-file "examples/factorial.shen"
                                                 "(factorial 5)" "120" "chc")
                      (and (= (hd R) ok) (= (hd (tl R)) "chc"))))
          (sl-check "query-expected-value-is-emitted"
                    (let Good (shenlogic.query-file "examples/factorial.shen"
                                                    "(factorial 5)" "120" "chc")
                         Bad (shenlogic.query-file "examples/factorial.shen"
                                                   "(factorial 5)" "121" "chc")
                      (not (= (hd (tl (tl Good)))
                              (hd (tl (tl Bad)))))))
          (sl-check "query-rejects-open-value"
                    (= (shenlogic.query-file "examples/factorial.shen"
                                             "(factorial X)" "120" "chc")
                       [error open-query-value]))
          (sl-check "query-rejects-malformed-expression"
                    (= (shenlogic.query-file "examples/factorial.shen"
                                             "factorial" "120" "chc")
                       [error malformed-query-expression]))
          (sl-check "factorial-eval-zero"
                    (= (sl-eval "examples/factorial.shen" "(factorial 0)")
                       [value 1]))
          (sl-check "negative-factorial-timeout"
                    (= (shenlogic.evaluate-file "examples/factorial.shen"
                                                "(factorial -1)" 50)
                       [timeout]))
          (sl-check "mutual-eval-even"
                    (= (sl-eval "examples/mutual.shen" "(even? 6)")
                       [value true]))
          (sl-check "mutual-eval-odd"
                    (= (sl-eval "examples/mutual.shen" "(odd? 5)")
                       [value true]))
          (sl-check "repeated-pattern"
                    (= (sl-eval "examples/lists.shen" "(same-pair? [a a])")
                       [value true]))
          (sl-check "repeated-pattern-mismatch"
                    (= (sl-eval "examples/lists.shen" "(same-pair? [a b])")
                       [value false]))
          (sl-check "repeated-pattern-priority-ir"
                    (if (sl-has-tag? not-applicable
                          (rules.compile (shenlogic.program "examples/lists.shen")))
                        false
                        true))
          (sl-check "constructor-chc-supported"
                    (sl-translation-succeeds? "examples/v2-constructors.shen" "chc"))
          (sl-check "control-graph-supported"
                    (sl-translation-succeeds? "examples/v2-control.shen" "graph"))
          (sl-check "control-type-errors-have-no-arithmetic-rule"
                    (not (sl-has-form? [i-lit v-true]
                           (rules.compile
                             (shenlogic.program "examples/v2-control.shen")))))
          (sl-check "control-thf-supported"
                    (sl-translation-succeeds? "examples/v2-control.shen" "thf"))
          (sl-check "canonical-string-roundtrip"
                    (let S (cn "a"
                               (cn (n->string 34)
                                   (cn (n->string 92)
                                       (cn (n->string 10) "b"))))
                      (= S (hd (read-from-string-unprocessed
                                 (serialize.canonical S))))))
          (sl-check "separate-declare-eval"
                    (= (sl-eval "tests/fixtures/declared.shen" "(declared-id 7)")
                       [value 7]))
          (sl-check "certificate-replay"
                    (certificate-test-success))
          (sl-check "certificate-rejects-bad-conclusion"
                    (certificate-test-rejected))
          (sl-check "certificate-rejects-unknown-rule"
                    (certificate-test-unknown-rule))
          (sl-check "certificate-rejects-missing-rule-premise"
                    (certificate-test-missing-rule-premise))
          (sl-check "certificate-rejects-unavailable-premise"
                    (certificate-test-unavailable-premise))
          (sl-check "certificate-rejects-malformed-step"
                    (certificate-test-malformed-step))
          (sl-check "certificate-v2-bundle"
                    (certificate-test-bundle-success))
          (sl-check "certificate-v2-rejects-malformed-rule"
                    (certificate-test-bundle-rejects-rule-shape))
          (sl-check "certificate-v2-rejects-stale-value-signature"
                    (certificate-test-bundle-rejects-stale-vs))
          (sl-check "certificate-v2-rejects-edited-chc"
                    (certificate-test-bundle-rejects-artifact-edit))
          (sl-check "certificate-v2-rejects-missing-lowering"
                    (certificate-test-bundle-rejects-missing-lowering))
          (sl-check "certificate-v2-rejects-duplicate-lowering"
                    (certificate-test-bundle-rejects-duplicate-lowering))
          (sl-check "certificate-v2-rejects-unknown-lowering"
                    (certificate-test-bundle-rejects-unknown-lowering))
          (sl-check "certificate-v2-rejects-raw-source"
                    (certificate-test-bundle-rejects-raw-source))
          (sl-check "v2-nested-if-let-negative"
                    (= (sl-eval "examples/v2-control.shen" "(nested-if-let -2)")
                       [value 11]))
          (sl-check "v2-nested-if-let-zero"
                    (= (sl-eval "examples/v2-control.shen" "(nested-if-let -1)")
                       [value 99]))
          (sl-check "v2-nested-if-let-positive"
                    (= (sl-eval "examples/v2-control.shen" "(nested-if-let 2)")
                       [value 6]))
          (sl-check "v2-short-circuit-and-skips-divergence"
                    (= (sl-eval "examples/v2-control.shen" "(short-circuit-and 0)")
                       [value false]))
          (sl-check "v2-short-circuit-or-skips-divergence"
                    (= (sl-eval "examples/v2-control.shen" "(short-circuit-or 0)")
                       [value true]))
          (sl-check "v2-strict-call-order"
                    (= (sl-eval "examples/v2-control.shen" "(strict-call-order 0)")
                       [error type-error]))
          (sl-check "v2-guard-error-blocks-fallback"
                    (= (sl-eval "tests/fixtures/v2-guard-error.shen" "(guard-error 1)")
                       [error type-error]))
          (sl-check "v2-proper-empty-list"
                    (= (sl-eval "examples/v2-lists.shen" "(list-shape [])")
                       [value empty]))
          (sl-check "v2-proper-singleton-list"
                    (= (sl-eval "examples/v2-lists.shen" "(list-shape [a])")
                       [value singleton]))
          (sl-check "v2-proper-nested-list"
                    (= (sl-eval "examples/v2-lists.shen" "(nested-list-shape [[a b] c])")
                       [value nested-pair]))
          (sl-check "v2-improper-list"
                    (= (sl-eval "examples/v2-lists.shen" "(list-shape [a | tail])")
                       [value improper]))
          (sl-check "v2-nested-improper-list"
                    (= (sl-eval "examples/v2-lists.shen" "(nested-list-shape [[a | tail] c])")
                       [value nested-improper]))
          (sl-check "v2-repeated-nested-variable"
                    (= (sl-eval "examples/v2-lists.shen" "(same-nested [[a a]])")
                       [value true]))
          (sl-check "v2-repeated-nested-variable-mismatch"
                    (= (sl-eval "examples/v2-lists.shen" "(same-nested [[a b]])")
                       [value false]))
          (sl-check "v2-constructor-node"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-tag (node 7))")
                       [value node]))
          (sl-check "v2-constructor-pair"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-tag (pair 1 2))")
                       [value pair]))
          (sl-check "v2-constructor-bundle"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-tag (bundle 1 2))")
                       [value bundle]))
          (sl-check "v2-constructor-zero-arity"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-tag (unit))")
                       [value unit-constructor]))
          (sl-check "v2-constructor-symbol-no-confusion"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-tag unit)")
                       [value unit-symbol]))
          (sl-check "v2-constructor-overlap-specific"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-overlap (node 0))")
                       [value zero]))
          (sl-check "v2-constructor-overlap-fallback"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-overlap (node 2))")
                       [value node]))
          (sl-check "v2-constructor-collision"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-collision (same 1))")
                       [value constructor]))
          (sl-check "v2-constructor-symbol-collision"
                    (= (sl-eval "examples/v2-constructors.shen" "(constructor-collision same)")
                       [value symbol]))
          (sl-check "v2-constructor-string-collision"
                    (= (sl-eval "examples/v2-constructors.shen"
                                "(constructor-collision (constructor-string-probe))")
                       [value string]))
          (sl-check "v2-constructor-wrap"
                    (= (sl-eval "examples/v2-constructors.shen" "(wrap-constructor 4)")
                       [value [ctor-value box [4]]]))
          (sl-check "v2-constructor-unwrap"
                    (= (sl-eval "examples/v2-constructors.shen"
                                "(unwrap-constructor (box 4))")
                       [value 4]))
          (sl-check "v2-mixed-arithmetic-constructor"
                    (= (sl-eval "examples/v2-constructors.shen" "(mixed-constructor 3)")
                       [value [ctor-value bundle [4 [ctor-value pair [3 [ctor-value node [2]]]]]]]))
          (sl-check "v2-symbol-literal"
                    (= (sl-eval "examples/v2-literals.shen" "(literal-kind foo)")
                       [value symbol-foo]))
          (sl-check "v2-string-literal"
                    (= (sl-eval "examples/v2-literals.shen" "(literal-string-probe)")
                       [value string-foo]))
          (sl-check "v2-mutual-even"
                    (= (sl-eval "examples/v2-mutual.shen" "(even-v2? 8)")
                       [value true]))
          (sl-check "v2-mutual-odd"
                    (= (sl-eval "examples/v2-mutual.shen" "(odd-v2? 7)")
                       [value true]))
          (sl-check "v2-mutual-parity"
                    (= (sl-eval "examples/v2-mutual.shen" "(parity-v2 8)")
                       [value even]))
          (sl-check "v2-reject-guard-user-call"
                    (sl-rejected? "tests/fixtures/v2-guard-rejection.shen"))
          (sl-check "v2-reject-partial-primitives"
                    (sl-rejected? "tests/fixtures/v2-rejections.shen"))
          (sl-check "v2-reject-separate-definition"
                    (sl-rejected? "tests/fixtures/v2-separate-definition.shen"))
          (sl-check "v2-reject-constructor-arity-collision"
                    (sl-rejected? "tests/fixtures/v2-constructor-arity.shen"))
          (sl-check "version"
                    (= (shenlogic.version) "0.2.0"))
          (sl-check "reject-unverified-fragment"
                    (sl-rejected? "tests/fixtures/rejections.shen"))
          (sl-check "reject-user-call-in-guard"
                    (sl-rejected? "tests/fixtures/guard-user-call.shen"))
          (sl-check "reject-higher-order-callee"
                    (sl-rejected? "tests/fixtures/higher-order-callee.shen"))
          (sl-check "reject-separate-declaration"
                    (sl-rejected? "tests/fixtures/separate-declaration.shen"))]
       (if (sl-all-true Results)
           (do (output "SHENLOGIC|ALL PASS~%") true)
           (do (output "SHENLOGIC|SOME FAIL~%")
               (error "ShenLogic regression failure")))))

(sl-run)
