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
                    (sl-has-tag? not-applicable
                      (rules.compile (shenlogic.program "examples/lists.shen"))))
          (sl-check "constructor-chc-rejected"
                    (sl-translation-rejected? "examples/lists.shen" "chc"))
          (sl-check "control-translation-rejected"
                    (sl-translation-rejected? "examples/strict.shen" "graph"))
          (sl-check "separate-declare-eval"
                    (= (sl-eval "tests/fixtures/declared.shen" "(declared-id 7)")
                       [value 7]))
          (sl-check "certificate-replay"
                    (certificate-test-success))
          (sl-check "certificate-rejects-bad-conclusion"
                    (certificate-test-rejected))
          (sl-check "version"
                    (= (shenlogic.version) "0.1.0"))
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
