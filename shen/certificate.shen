\\ Finite derivation certificate checker.  Theory contract:
\\ [theory Declarations Rules SCCs], rules are
\\ [rule Id Function Args Bound Premises Result].
\\ Certificate steps are [step Id Substitution Premises Result], ordered so
\\ premises precede their conclusion.  Checker is deliberately conservative.

(define certificate-check
  Theory Certificate -> (certificate-replay Theory Certificate))

(define certificate-replay
  Theory Certificate -> (certificate-replay-previous Theory Certificate []))

(define certificate-replay-previous
  Theory [] Earlier -> [ok]
  Theory [S | Ss] Earlier -> (let R (certificate-step Theory S Earlier)
                               (if (= (hd R) ok)
                                   (certificate-replay-previous Theory Ss [S | Earlier]) R)))

(define certificate-step
  Theory [step Id Sub Premises Result] Earlier -> (let Rule (certificate-rule Id (certificate-rules Theory))
    (if (= Rule false) [error unknown-rule]
      (let Expected (certificate-instantiate (certificate-rule-result Rule) Sub)
        (let Required (certificate-instantiate-list (certificate-rule-premises Rule) Sub)
          (if (= Expected Result)
              (if (= Required Premises)
                  (if (certificate-premises? Theory Premises Earlier Sub) [ok] [error premise-mismatch])
                  [error rule-premises-mismatch])
              [error conclusion-mismatch])))))
  Theory [derive Id Sub Premises Result] Earlier -> (certificate-step Theory [step Id Sub Premises Result] Earlier)
  Theory _ Earlier -> [error malformed-step])

(define certificate-rules
  [theory D Rs Ss] -> Rs
  [_] -> [])

(define certificate-rule
  Id [] -> false
  Id [[rule I F A B Ps R] | Rs] -> (if (= Id I) [rule I F A B Ps R] (certificate-rule Id Rs))
  Id [_ | Rs] -> (certificate-rule Id Rs))

(define certificate-rule-result
  [rule I F A B Ps R] -> R)

(define certificate-rule-premises
  [rule I F A B Ps R] -> Ps)

(define certificate-instantiate-list
  [] S -> []
  [X | Xs] S -> [(certificate-instantiate X S) |
                  (certificate-instantiate-list Xs S)])

(define certificate-instantiate
  X [] -> X
  X [[A B] | S] -> (if (= X A) B (certificate-instantiate X S))
  [X | Xs] S -> [(certificate-instantiate X S) | (certificate-instantiate Xs S)]
  X S -> X)

(define certificate-premises?
  T [] Earlier Sub -> true
  T [P | Ps] Earlier Sub -> (if (certificate-has-premise? (certificate-instantiate P Sub) Earlier)
                                (certificate-premises? T Ps Earlier Sub) false))

(define certificate-has-premise?
  P [] -> false
  P [[step I S Ps R] | Ss] -> (if (= P R) true (certificate-has-premise? P Ss))
  P [[derive I S Ps R] | Ss] -> (if (= P R) true (certificate-has-premise? P Ss))
  P [_ | Ss] -> (certificate-has-premise? P Ss))

\\ Aliases used by early clients.
(define shenlogic-check-certificate
  Theory Certificate -> (certificate-check Theory Certificate))
