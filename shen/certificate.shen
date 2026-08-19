\\ Certificate artifacts.
\\
\\ v2 certificates are self-describing bundles.  The checker validates the
\\ bundle shape and the references which can be checked without a backend
\\ (rule ids and lowering paths); it deliberately does not claim to replay an
\\ SMT/THF proof.  The small v1 derivation replay is retained for compatibility.

(define certificate-check
  [shenlogic-certificate 1 NormalizedSource ValueSignature DecisionIR RuleIR
                          CHCAST THFAST LoweringSteps NameMap] ->
    (certificate-check-v2 NormalizedSource ValueSignature DecisionIR RuleIR
                           CHCAST THFAST LoweringSteps NameMap)
  _ -> [error malformed-certificate])

(define shenlogic.certificate.check
  Certificate -> (certificate-check Certificate))

\\ Legacy finite replay remains available explicitly, but is not the v2
\\ certificate entry point.
(define certificate-replay-check
  Theory Certificate -> (certificate-replay Theory Certificate))

(define certificate-check-v2
  Source [value-signature Constructors] DecisionIR RuleIR CHCAST THFAST
  LoweringSteps [name-map Pairs] ->
    (if (certificate-constructors? Constructors)
        (if (certificate-theory-v2? RuleIR [value-signature Constructors]
                                  [name-map Pairs])
            (if (certificate-list? DecisionIR)
                (if (certificate-list? CHCAST)
                    (if (certificate-list? THFAST)
                        (if (certificate-name-pairs? Pairs)
                            (if (certificate-lowering-valid? LoweringSteps RuleIR)
                                [ok]
                                [error invalid-lowering-path])
                            [error malformed-name-map])
                        [error malformed-thfast])
                    [error malformed-chcast])
                [error malformed-decision-ir])
            [error malformed-rule-ir])
        [error malformed-value-signature])
  _ _ _ _ _ _ _ _ -> [error malformed-certificate])

(define certificate-list?
  [] -> true
  [_ | Xs] -> (certificate-list? Xs)
  _ -> false)

(define certificate-constructors?
  [] -> true
  [[constructor Source Target Arity] | Cs] ->
    (certificate-constructors? Cs)
  _ -> false)

(define certificate-theory-v2?
  [theory ValueSignature Relations Rules SCCs NameMap]
  ExpectedValueSignature ExpectedNameMap ->
    (if (= ValueSignature ExpectedValueSignature)
        (if (= NameMap ExpectedNameMap)
            (if (certificate-list? Relations)
                (if (certificate-rules-v2? Rules [])
                    (certificate-list? SCCs)
                    false)
                false)
            false)
        false)
  _ _ _ -> false)

(define certificate-name-pairs?
  [] -> true
  [[_ _] | Ps] -> (certificate-name-pairs? Ps)
  _ -> false)

(define certificate-rule-ir?
  [rule-ir Rules] -> (certificate-rules-v2? Rules [])
  Rules -> (certificate-rules-v2? Rules []))

(define certificate-rules-v2?
  [] _ -> true
  [[rule Id Function Clause Path Args Bound Premises Result] | Rs] Seen ->
    (if (element? Id Seen)
        false
        (if (and (certificate-list? Args) (certificate-list? Bound))
            (if (certificate-list? Premises)
                (certificate-rules-v2? Rs [Id | Seen])
                false)
            false))
  _ _ -> false)

(define certificate-rule-ids
  [rule-ir Rules] -> (certificate-rule-ids Rules)
  [] -> []
  [[rule Id _ _ _ _ _ _ _] | Rs] -> [Id | (certificate-rule-ids Rs)]
  [_ | Rs] -> (certificate-rule-ids Rs))

(define certificate-rule-path
  Id [rule-ir Rules] -> (certificate-rule-path Id Rules)
  _ [] -> not-found
  Id [[rule Id _ _ Path _ _ _ _] | _] -> [found Path]
  Id [_ | Rs] -> (certificate-rule-path Id Rs))

\\ Lowering steps in released artifacts have appeared as either
\\ [lowering-step RuleId Path ...] or [step RuleId Path ...].  Accept both,
\\ while recursively accepting tagged containers and opaque backend records.
(define certificate-lowering-valid?
  [] _ -> true
  [S | Ss] Rules -> (if (certificate-lowering-step-valid? S Rules)
                        (certificate-lowering-valid? Ss Rules)
                        false)
  S Rules -> (certificate-lowering-step-valid? S Rules))

(define certificate-lowering-step-valid?
  [lowering-steps Steps] Rules -> (certificate-lowering-valid? Steps Rules)
  [lowering-step Id Path | _] Rules ->
    (certificate-path-ref? Id Path Rules)
  [lower Id Path | _] Rules -> (certificate-path-ref? Id Path Rules)
  [step Id Path | _] Rules -> (certificate-path-ref? Id Path Rules)
  [Tag | _] _ -> (certificate-known-lowering-tag? Tag)
  _ _ -> false)

(define certificate-known-lowering-tag?
  lowering-step -> true
  lowering -> true
  step -> true
  backend -> true
  rule -> true
  source -> true
  decision -> true
  chc -> true
  thf -> true
  _ -> false)

(define certificate-path-ref?
  Id Path Rules -> (let Found (certificate-rule-path Id Rules)
                     (if (= Found not-found)
                         false
                         (= (hd (tl Found)) Path))))

\\ v1 finite derivation replay.
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
  [theory VS D Rs Ss NM] -> Rs
  [_] -> [])

(define certificate-rule
  Id [] -> false
  Id [[rule I F A B Ps R] | Rs] -> (if (= Id I) [rule I F A B Ps R] (certificate-rule Id Rs))
  Id [[rule I F C P A B Ps R] | Rs] ->
    (if (= Id I) [rule I F C P A B Ps R] (certificate-rule Id Rs))
  Id [_ | Rs] -> (certificate-rule Id Rs))

(define certificate-rule-result
  [rule _ _ _ _ _ _ _ R] -> R
  [rule _ _ _ _ _ R] -> R)

(define certificate-rule-premises
  [rule _ _ _ _ _ _ Ps _] -> Ps
  [rule _ _ _ _ Ps _] -> Ps)

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

(define shenlogic-check-certificate
  Certificate -> (certificate-check Certificate))
