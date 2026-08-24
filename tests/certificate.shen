\\ Certificate replay regression cases. Load this file after shen/certificate.shen.

(define certificate-test-theory
  -> [theory [value-signature []] []
              [[rule r0 fact clause0 path0 [x] [x] [] [fact 0 1]]
               [rule r1 fact clause1 path1 [x] [x] [[fact 0 1]] [fact 1 2]]]
              [] [name-map []]])

(define certificate-test-success
  -> (= (certificate-replay-check (certificate-test-theory)
                                  [[step r0 [[x 0]] [] [fact 0 1]]
                                   [step r1 [[x 1]] [[fact 0 1]] [fact 1 2]]])
         [ok]))

(define certificate-test-rejected
  -> (= (certificate-replay-check (certificate-test-theory)
                                  [[step r0 [[x 0]] [] [fact 9 9]]])
         [error conclusion-mismatch]))

\\ Corruption cases exercise every conservative rejection boundary: an
\\ unknown rule, omitted rule premise, unavailable earlier premise, and a
\\ malformed step.  These are intentionally independent of backend output.
(define certificate-test-unknown-rule
  -> (= (certificate-replay-check (certificate-test-theory)
                                  [[step missing [[x 0]] [] [fact 0 1]]])
         [error unknown-rule]))

(define certificate-test-missing-rule-premise
  -> (= (certificate-replay-check (certificate-test-theory)
                                  [[step r0 [[x 0]] [] [fact 0 1]]
                                   [step r1 [[x 1]] [] [fact 1 2]]])
         [error rule-premises-mismatch]))

(define certificate-test-unavailable-premise
  -> (= (certificate-replay-check (certificate-test-theory)
                                  [[step r1 [[x 1]] [[fact 0 1]] [fact 1 2]]])
         [error premise-mismatch]))

(define certificate-test-malformed-step
  -> (= (certificate-replay-check (certificate-test-theory)
                                  [[garbage]])
         [error malformed-step]))

\\ Complete v2 bundles are checked through the one-argument public entrypoint.
(define certificate-test-bundle
  -> (certificate-test-v2-bundle))

(define certificate-test-v2-source
  -> [program [[definition fact none
                 [[clause 0 [] none [e-value 1]]] 0]]])

(define certificate-test-v2-bundle
  -> (let P (certificate-test-v2-source)
       (let T (rules.compile P)
         (let C (shenlogic.unwrap (shenlogic.chc.render T nonlinear))
           (let H (shenlogic.unwrap (shenlogic.thf.render T full-model))
             (let VS (certificate-theory-value-signature T)
               (let NM (certificate-theory-name-map T)
                 (let D (decision.compile P)
                   (let Steps (shenlogic.workflow.lowering-steps
                                 (shenlogic.workflow.theory-rules T))
                     [shenlogic-certificate 1 P VS D T [chc C] [thf H]
                      Steps NM])))))))))

(define certificate-test-bundle-success
  -> (= (certificate-check (certificate-test-bundle)) [ok]))

\\ Same in-memory bundle construction from a source file; exercises the
\\ generated sl.apply rules when the file uses function parameters.
(define certificate-test-file-bundle
  File -> (let P (shenlogic.program File)
            (let T (rules.compile P)
              (let C (shenlogic.unwrap (shenlogic.chc.render T nonlinear))
                (let H (shenlogic.unwrap (shenlogic.thf.render T full-model))
                  (let VS (certificate-theory-value-signature T)
                    (let NM (certificate-theory-name-map T)
                      (let D (decision.compile P)
                        (let Steps (shenlogic.workflow.lowering-steps
                                      (shenlogic.workflow.theory-rules T))
                          [shenlogic-certificate 1 P VS D T [chc C] [thf H]
                           Steps NM])))))))))

(define certificate-test-file-success
  File -> (= (certificate-check (certificate-test-file-bundle File)) [ok]))

(define certificate-test-bundle-rejects-rule-shape
  -> (= (certificate-check
          (certificate-test-bundle-bad-theory (certificate-test-v2-bundle)))
         [error malformed-rule-ir]))

(define certificate-test-bundle-bad-theory
  [shenlogic-certificate V P VS D _ C H S NM] ->
    [shenlogic-certificate V P VS D
     [theory VS [] [[bad]] [] NM] C H S NM])

(define certificate-test-bundle-rejects-stale-vs
  -> (= (certificate-check
          (certificate-test-bundle-stale-vs (certificate-test-v2-bundle)))
         [error value-signature-mismatch]))

(define certificate-test-bundle-stale-vs
  [shenlogic-certificate V P _ D T C H S NM] ->
    [shenlogic-certificate V P [value-signature []] D T C H S NM])

(define certificate-test-bundle-rejects-artifact-edit
  -> (= (certificate-check
          (certificate-test-bundle-artifact-edit (certificate-test-v2-bundle)))
         [error chc-mismatch]))

(define certificate-test-bundle-artifact-edit
  [shenlogic-certificate V P VS D T [chc C] H S NM] ->
    [shenlogic-certificate V P VS D T [chc (cn C "x")] H S NM])

(define certificate-test-bundle-rejects-missing-lowering
  -> (= (certificate-check
          (certificate-test-bundle-missing-lowering (certificate-test-v2-bundle)))
         [error invalid-lowering-coverage]))

(define certificate-test-bundle-missing-lowering
  [shenlogic-certificate V P VS D T C H [_ | Ss] NM] ->
    [shenlogic-certificate V P VS D T C H Ss NM])

(define certificate-test-bundle-rejects-duplicate-lowering
  -> (= (certificate-check
          (certificate-test-bundle-duplicate-lowering (certificate-test-v2-bundle)))
         [error invalid-lowering-coverage]))

(define certificate-test-bundle-duplicate-lowering
  [shenlogic-certificate V P VS D T C H [S | Ss] NM] ->
    [shenlogic-certificate V P VS D T C H [S S | Ss] NM])

(define certificate-test-bundle-rejects-unknown-lowering
  -> (= (certificate-check
          (certificate-test-bundle-unknown-lowering (certificate-test-v2-bundle)))
         [error invalid-lowering-coverage]))

(define certificate-test-bundle-unknown-lowering
  [shenlogic-certificate V P VS D T C H S NM] ->
    [shenlogic-certificate V P VS D T C H
     [[lowering-step unknown [0] chc] | S] NM])

(define certificate-test-bundle-rejects-raw-source
  -> (= (certificate-check
          (certificate-test-bundle-raw-source (certificate-test-v2-bundle)))
         [error malformed-normalized-source]))

(define certificate-test-bundle-raw-source
  [shenlogic-certificate V _ VS D T C H S NM] ->
    [shenlogic-certificate V [define fact] VS D T C H S NM])

(define certificate-test-bundle-rejects-unsupported-source
  -> (= (certificate-check
          (certificate-test-bundle-unsupported-source
            (certificate-test-v2-bundle)))
         [error unsupported-source]))

(define certificate-test-bundle-unsupported-source
  [shenlogic-certificate V _ VS D T C H S NM] ->
    (let P [program [[definition fact none
                       [[clause 0 [] none
                         [e-prim do [[e-value 1]]]]] 0]]]
      [shenlogic-certificate V P VS (decision.compile P) T C H S NM]))
