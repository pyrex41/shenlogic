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
  -> [shenlogic-certificate 1
      [program]
      [value-signature []]
      []
      [[rule r0 fact clause0 [path] [] [] [] [v-int [i-lit 1]]]]
      []
      []
      []
      [name-map []]])

(define certificate-test-bundle-success
  -> (= (certificate-check (certificate-test-bundle)) [ok]))

(define certificate-test-bundle-rejects-rule-shape
  -> (= (certificate-check
          [shenlogic-certificate 1 [program] [value-signature []] []
           [[rule r0 fact clause0 [path] [] [] []]] [] [] [] [name-map []]])
         [error malformed-rule-ir]))
