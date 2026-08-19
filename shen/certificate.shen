\\ Certificate artifacts.
\\
\\ v2 certificates are self-describing bundles.  The checker validates the
\\ bundle shape and the references which can be checked without a backend
\\ (rule ids and lowering paths); it deliberately does not claim to replay an
\\ SMT/THF proof.  The small v1 derivation replay is retained for compatibility.

(define certificate-check
  [shenlogic-certificate 1 NormalizedSource ValueSignature DecisionIR Theory
                          [chc CHCAST] [thf THFAST] LoweringSteps NameMap] ->
    (certificate-check-v2 NormalizedSource ValueSignature DecisionIR Theory
                           CHCAST THFAST LoweringSteps NameMap)
  _ -> [error malformed-certificate])

(define shenlogic.certificate.check
  Certificate -> (certificate-check Certificate))

\\ Legacy finite replay remains available explicitly, but is not the v2
\\ certificate entry point.
(define certificate-replay-check
  Theory Certificate -> (certificate-replay Theory Certificate))

(define certificate-check-v2
  Source ValueSignature DecisionIR Theory CHCAST THFAST LoweringSteps NameMap ->
    (if (certificate-normalized-program? Source)
        (if (certificate-theory-v2-shape? Theory)
            (if (= ValueSignature (certificate-theory-value-signature Theory))
                (if (= NameMap (certificate-theory-name-map Theory))
                    (if (certificate-value-signature? ValueSignature)
                        (if (certificate-name-map? NameMap)
                            (if (certificate-decision-exact? Source DecisionIR)
                                (certificate-check-compiled-theory Source Theory
                                  CHCAST THFAST LoweringSteps)
                                [error decision-mismatch])
                            [error malformed-name-map])
                        [error malformed-value-signature])
                    [error name-map-mismatch])
                [error value-signature-mismatch])
            [error malformed-rule-ir])
        [error malformed-normalized-source])
  _ _ _ _ _ _ _ _ -> [error malformed-certificate])

\\ The normalized AST is the trust boundary.  Reject raw source terms and any
\\ tagged node outside the fixed v2 vocabulary.
(define certificate-normalized-program?
  [program Definitions] -> (certificate-definitions? Definitions)
  _ -> false)

(define certificate-definitions?
  [] -> true
  [[definition Name Signature Clauses Arity] | Ds] ->
    (and (symbol? Name) (certificate-signature? Signature)
         (integer? Arity) (>= Arity 0) (certificate-clauses? Clauses)
         (certificate-definitions? Ds))
  _ -> false)

(define certificate-signature?
  none -> true
  [signature Args Result] ->
    (and (certificate-term-list-schema? Args)
         (certificate-term-schema? Result))
  _ -> false)

(define certificate-clauses?
  [] -> true
  [[clause Index Patterns Guard Body] | Cs] ->
    (and (integer? Index) (certificate-patterns? Patterns)
         (certificate-guard-schema? Guard) (certificate-expr-schema? Body)
         (certificate-clauses? Cs))
  _ -> false)

(define certificate-patterns?
  [] -> true
  [P | Ps] -> (and (certificate-pattern-schema? P)
                   (certificate-patterns? Ps))
  _ -> false)

(define certificate-pattern-schema?
  [p-wild] -> true
  [p-var X] -> (variable? X)
  [p-lit X] -> (certificate-atom? X)
  [p-ctor Tag Fields] ->
    (and (symbol? Tag) (certificate-patterns? Fields))
  _ -> false)

(define certificate-guard-schema?
  none -> true
  [some E] -> (certificate-expr-schema? E)
  _ -> false)

(define certificate-expr-schema?
  [e-var X] -> (variable? X)
  [e-value X] -> (certificate-atom? X)
  [e-ctor Tag Args] -> (and (symbol? Tag) (certificate-exprs? Args))
  [e-call Name Args] -> (and (symbol? Name) (certificate-exprs? Args))
  [e-if C T F] -> (and (certificate-expr-schema? C)
                       (certificate-expr-schema? T)
                       (certificate-expr-schema? F))
  [e-let X A B] -> (and (variable? X)
                        (certificate-expr-schema? A)
                        (certificate-expr-schema? B))
  [e-and A B] -> (and (certificate-expr-schema? A)
                      (certificate-expr-schema? B))
  [e-or A B] -> (and (certificate-expr-schema? A)
                     (certificate-expr-schema? B))
  [e-prim Op Args] -> (and (symbol? Op) (certificate-exprs? Args))
  _ -> false)

(define certificate-exprs?
  [] -> true
  [E | Es] -> (and (certificate-expr-schema? E)
                   (certificate-exprs? Es))
  _ -> false)

(define certificate-atom?
  X -> (or (number? X) (string? X) (symbol? X)))

(define certificate-term-schema?
  X -> (if (cons? X)
           (certificate-term-list-schema? X)
           true))

(define certificate-term-list-schema?
  [] -> true
  [X | Xs] -> (and (certificate-term-schema? X)
                   (certificate-term-list-schema? Xs))
  _ -> false)

(define certificate-theory-v2-shape?
  [theory [value-signature Constructors] Relations Rules SCCs [name-map Pairs]] ->
    (and (certificate-constructors? Constructors)
         (certificate-relations? Relations)
         (certificate-rules-v2? Rules [])
         (certificate-sccs? SCCs) (certificate-name-pairs? Pairs))
  _ -> false)

(define certificate-theory-value-signature
  [theory VS _ _ _ _] -> VS
  _ -> malformed)

(define certificate-theory-name-map
  [theory _ _ _ _ NM] -> NM
  _ -> malformed)

(define certificate-value-signature?
  [value-signature Constructors] -> (certificate-constructors? Constructors)
  _ -> false)

(define certificate-name-map?
  [name-map Pairs] -> (certificate-name-pairs? Pairs)
  _ -> false)

(define certificate-relations?
  [] -> true
  [[relation Name Sorts Result] | Rs] ->
    (and (symbol? Name) (certificate-list? Sorts) (= Result value)
         (certificate-relations? Rs))
  _ -> false)

(define certificate-sccs?
  [] -> true
  [[scc Names] | Ss] ->
    (and (certificate-symbol-list? Names) (certificate-sccs? Ss))
  _ -> false)

(define certificate-symbol-list?
  [] -> true
  [X | Xs] -> (and (symbol? X) (certificate-symbol-list? Xs))
  _ -> false)

\\ Decision and Rule IR are deterministic functions of normalized source.
(define certificate-decision-exact?
  Source Decision ->
    (let Expected (trap-error (decision.compile Source) (/. E malformed))
      (and (not (= Expected malformed)) (= Expected Decision))))

(define certificate-check-compiled-theory
  Source Theory CHCAST THFAST LoweringSteps ->
    (if (certificate-source-logic-valid? Source)
        (let Expected (trap-error (rules.compile Source) (/. E malformed))
          (if (= Expected malformed)
              [error theory-unavailable]
              (if (= Expected Theory)
                  (if (certificate-chc-equal? Theory CHCAST)
                      (if (certificate-thf-equal? Theory THFAST)
                          (if (certificate-lowering-valid? LoweringSteps Theory)
                              [ok]
                              [error invalid-lowering-coverage])
                          [error thf-mismatch])
                      [error chc-mismatch])
                  [error theory-mismatch])))
        [error unsupported-source]))

(define certificate-source-logic-valid?
  Source ->
    (and (certificate-supported-program? Source)
         (let R (trap-error (shenlogic.validate.logic Source)
                            (/. E invalid-source))
           (and (cons? R) (= (hd R) ok)))))

\\ validate.logic predates the normalized e-* nodes and therefore cannot see
\\ an effect hidden behind e-prim.  Keep the explicit supported-fragment gate
\\ here so a forged normalized certificate cannot smuggle one through.
(define certificate-supported-program?
  [program Definitions] -> (certificate-supported-definitions? Definitions)
  _ -> false)

(define certificate-supported-definitions?
  [] -> true
  [[definition _ _ Clauses _] | Ds] ->
    (and (certificate-supported-clauses? Clauses)
         (certificate-supported-definitions? Ds))
  _ -> false)

(define certificate-supported-clauses?
  [] -> true
  [[clause _ _ Guard Body] | Cs] ->
    (and (certificate-supported-guard? Guard)
         (certificate-supported-expr? Body)
         (certificate-supported-clauses? Cs))
  _ -> false)

(define certificate-supported-guard?
  none -> true
  [some E] -> (certificate-supported-expr? E)
  _ -> false)

(define certificate-supported-expr?
  [e-var _] -> true
  [e-value _] -> true
  [e-ctor _ Args] -> (certificate-supported-exprs? Args)
  [e-call _ Args] -> (certificate-supported-exprs? Args)
  [e-if C T F] -> (and (certificate-supported-expr? C)
                       (certificate-supported-expr? T)
                       (certificate-supported-expr? F))
  [e-let _ A B] -> (and (certificate-supported-expr? A)
                        (certificate-supported-expr? B))
  [e-and A B] -> (and (certificate-supported-expr? A)
                      (certificate-supported-expr? B))
  [e-or A B] -> (and (certificate-supported-expr? A)
                     (certificate-supported-expr? B))
  [e-prim Op Args] ->
    (and (element? Op [+ - * = neq < > <= >=])
         (certificate-supported-exprs? Args))
  _ -> false)

(define certificate-supported-exprs?
  [] -> true
  [E | Es] -> (and (certificate-supported-expr? E)
                   (certificate-supported-exprs? Es))
  _ -> false)

(define certificate-chc-equal?
  Theory Artifact ->
    (if (string? Artifact)
        (let R (trap-error (shenlogic.chc.render Theory nonlinear)
                           (/. E render-error))
          (if (and (cons? R) (= (hd R) ok))
              (= (hd (tl R)) Artifact) false))
        false))

(define certificate-thf-equal?
  Theory Artifact ->
    (if (string? Artifact)
        (let R (trap-error (shenlogic.thf.render Theory full-model)
                           (/. E render-error))
          (if (and (cons? R) (= (hd R) ok))
              (= (hd (tl R)) Artifact) false))
        false))

(define certificate-list?
  [] -> true
  [_ | Xs] -> (certificate-list? Xs)
  _ -> false)

(define certificate-constructors?
  [] -> true
  [[constructor Source Target Arity] | Cs] ->
    (and (certificate-constructor-tag? Source)
         (certificate-constructor-tag? Target)
         (integer? Arity)
         (>= Arity 0) (certificate-constructors? Cs))
  _ -> false)

(define certificate-constructor-tag?
  X -> (or (symbol? X) (= X true) (= X false)))

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
  [[A B] | Ps] -> (and (symbol? A) (symbol? B)
                       (certificate-name-pairs? Ps))
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
  Id [theory _ _ Rules _ _] -> (certificate-rule-path Id Rules)
  Id [rule-ir Rules] -> (certificate-rule-path Id Rules)
  _ [] -> not-found
  Id [[rule Id _ _ Path _ _ _ _] | _] -> [found Path]
  Id [_ | Rs] -> (certificate-rule-path Id Rs))

\\ Lowering coverage is a multiset, not a loose set of references.  Require
\\ exactly one CHC and one THF record for every compiled rule/path.
(define certificate-lowering-valid?
  Steps [theory _ _ Rules _ _] ->
    (certificate-lowering-consume Steps
      (certificate-lowering-expected Rules))
  _ _ -> false)

(define certificate-lowering-expected
  [] -> []
  [[rule Id _ _ Path _ _ _ _] | Rs] ->
    (append [[key Id Path chc] [key Id Path thf]]
      (certificate-lowering-expected Rs))
  _ -> [invalid])

(define certificate-lowering-consume
  [] [] -> true
  [] _ -> false
  [S | Ss] Expected ->
    (let K (certificate-lowering-key S)
      (if (= K invalid)
          false
          (if (element? K Expected)
              (certificate-lowering-consume Ss
                (certificate-lowering-remove K Expected))
              false)))
  _ _ -> false)

(define certificate-lowering-key
  [lowering-step Id Path chc] -> [key Id Path chc]
  [lowering-step Id Path thf] -> [key Id Path thf]
  _ -> invalid)

(define certificate-lowering-remove
  K [K | Ks] -> Ks
  K [X | Xs] -> [X | (certificate-lowering-remove K Xs)]
  _ [] -> [])

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
