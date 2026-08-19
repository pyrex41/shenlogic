\\ Certificate replay regression cases. Load this file after shen/certificate.shen.

(define certificate-test-theory
  -> [theory [] [[rule r0 fact [x] [x] [] [fact 0 1]]
                 [rule r1 fact [x] [x] [[fact 0 1]] [fact 1 2]]] []])

(define certificate-test-success
  -> (= (certificate-check (certificate-test-theory)
                           [[step r0 [[x 0]] [] [fact 0 1]]
                            [step r1 [[x 1]] [[fact 0 1]] [fact 1 2]]])
         [ok]))

(define certificate-test-rejected
  -> (= (certificate-check (certificate-test-theory)
                           [[step r0 [[x 0]] [] [fact 9 9]]])
         [error conclusion-mismatch]))
