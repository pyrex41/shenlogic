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
          (sl-check "ordered-surface"
                    (= (sl-render "examples/ordered.shen" "surface")
                       (sl-read "tests/golden/ordered.surface.logic")))
          (sl-check "factorial-slir"
                    (= (sl-render "examples/factorial.shen" "slir")
                       (sl-read "tests/golden/factorial.slir")))
          (sl-check "factorial-chc"
                    (= (sl-render "examples/factorial.shen" "chc")
                       (sl-read "tests/golden/factorial.chc")))
          (sl-check "factorial-thf"
                    (= (sl-render "examples/factorial.shen" "thf")
                       (sl-read "tests/golden/factorial.thf")))
          (sl-check "strict-let-eval"
                    (= (sl-eval "examples/strict.shen" "(strict-probe 4)")
                       [value 10]))
          (sl-check "guard-false-fallback"
                    (= (sl-eval "examples/guards.shen" "(sign 0)")
                       [value zero]))
          (sl-check "guard-negative-clause"
                    (= (sl-eval "examples/guards.shen" "(sign -2)")
                       [value negative]))
          (sl-check "factorial-eval-5"
                    (= (sl-eval "examples/factorial.shen" "(factorial 5)")
                       [value 120]))
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
           (do (output "SHENLOGIC|SOME FAIL~%") false))))

(sl-run)
