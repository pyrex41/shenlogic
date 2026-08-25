\\ System-S oracle checks that involve arithmetic primitive typings.
\\ Kept outside the Bifrost-shared suite: shen-lua's kernel System S
\\ currently rejects judgments like (* 2 3) : number that shen-go and
\\ shen-cl accept -- a host kernel divergence this oracle discovered.

(load "shenlogic.shen")

(define oa-check
  Label true -> (do (output (cn "PASS " (cn Label "~%"))) true)
  Label _ -> (do (output (cn "FAIL " (cn Label "~%"))) false))

(define oa-all
  [] -> true
  [true | Xs] -> (oa-all Xs)
  _ -> false)

(define oa-run
  -> (let Results
       [(oa-check "oracle-factorial"
          (= (shenlogic.oracle-file "examples/factorial.shen") [ok 2 0]))
        (oa-check "oracle-higher-order"
          (= (shenlogic.oracle-file "examples/v2-map.shen") [ok 7 0]))
        (oa-check "oracle-linarith"
          (= (shenlogic.oracle-file "examples/tsl-linarith.shen") [ok 8 0]))]
       (if (oa-all Results)
           (output "SHENLOGIC|ORACLE ARITH PASS~%")
           (do (output "SHENLOGIC|ORACLE ARITH FAIL~%")
               (error "oracle arithmetic checks failed")))))

(oa-run)
