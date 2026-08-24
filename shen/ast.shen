\\ A small data-only AST. Payloads remain raw Shen values.
(define shenlogic.ast.make-program Definitions -> [program Definitions])
(define shenlogic.ast.program-definitions [program Definitions] -> Definitions)

(define shenlogic.ast.make-definition Name Signature Clauses Arity -> [definition Name Signature Clauses Arity])
(define shenlogic.ast.definition-name [definition Name _ _ _] -> Name)
(define shenlogic.ast.definition-signature [definition _ Signature _ _] -> Signature)
(define shenlogic.ast.definition-clauses [definition _ _ Clauses _] -> Clauses)
(define shenlogic.ast.definition-arity [definition _ _ _ Arity] -> Arity)

(define shenlogic.ast.make-signature Args Result -> [signature Args Result])
(define shenlogic.ast.make-no-signature -> none)
(define shenlogic.ast.signature-args [signature Args _] -> Args)
(define shenlogic.ast.signature-result [signature _ Result] -> Result)

\\ Normalize Shen's right-associated arrow notation into a first-order
\\ signature.  The result is [signature ArgumentTypes ResultType].
(define shenlogic.ast.normalize-signature
  none -> none
  [signature Args Result] -> [signature Args Result]
  Type -> (let Parts (shenlogic.ast.signature-parts
                        (shenlogic.ast.signature-source-list Type) [] false)
             (if (= (hd Parts) ok)
                 [signature (map (/. T (shenlogic.ast.normalize-type T))
                                 (hd (hd (tl Parts))))
                            (shenlogic.ast.normalize-type
                              (hd (tl (hd (tl Parts)))))]
                 [error sl-a001 Type])))

\\ Normalize the explicit cons-chain representation that declare-form types
\\ arrive in, recursively, so nested arrow types compare and destructure the
\\ same way whichever surface syntax produced them.
(define shenlogic.ast.normalize-type
  [cons X Xs] -> (map (/. T (shenlogic.ast.normalize-type T))
                      (shenlogic.ast.signature-source-list [cons X Xs]))
  T -> (if (cons? T)
           (map (/. U (shenlogic.ast.normalize-type U)) T)
           T))

\\ Helpers over normalized types: a top-level arrow type is a flat list
\\ with at least one --> separator.
(define shenlogic.ast.arrow-type?
  T -> (if (cons? T)
           (= (hd (shenlogic.ast.signature-parts T [] false)) ok)
           false))

(define shenlogic.ast.arrow-parts
  T -> (let Parts (shenlogic.ast.signature-parts T [] false)
         (if (= (hd Parts) ok)
             [found (hd (hd (tl Parts))) (hd (tl (hd (tl Parts))))]
             none)))

(define shenlogic.ast.arrow-args
  T -> (let P (shenlogic.ast.arrow-parts T)
         (if (= P none) [] (hd (tl P)))))

(define shenlogic.ast.arrow-result
  T -> (let P (shenlogic.ast.arrow-parts T)
         (if (= P none) none (hd (tl (tl P))))))

(define shenlogic.ast.arrow-arity
  T -> (length (shenlogic.ast.arrow-args T)))

\\ A declaration's bracketed type arrives from the raw reader as an explicit
\\ cons chain (unlike an inline brace signature's token list).  Flatten only
\\ that representation; leave ordinary terms untouched for diagnostics.
(define shenlogic.ast.signature-source-list
  [cons X Xs] -> [X | (shenlogic.ast.signature-source-list Xs)]
  [] -> []
  X -> X)

(define shenlogic.ast.signature-parts
  [] _ _ -> [error sl-a001 []]
  [X] Acc Seen ->
    (if (and Seen (not (shenlogic.ast.atom-spelling? X "-->")))
        [ok [(reverse Acc) X]]
        [error sl-a001 [X | Acc]])
  [X | Xs] Acc Seen ->
    (if (shenlogic.ast.atom-spelling? X "-->")
        (shenlogic.ast.signature-parts Xs Acc true)
        (shenlogic.ast.signature-parts Xs [X | Acc] Seen)))

(define shenlogic.ast.atom-spelling?
  [] _ -> false
  X _ -> false where (cons? X)
  X Spelling -> (= (str X) Spelling))

(define shenlogic.ast.signature-args-from
  [_] -> []
  Parts -> (shenlogic.ast.signature-drop-last Parts []))

(define shenlogic.ast.signature-result-from
  Parts -> (shenlogic.ast.signature-last Parts))

(define shenlogic.ast.signature-drop-last
  [_] _ -> []
  [X | Xs] Acc -> (shenlogic.ast.signature-drop-last Xs [X | Acc]))

(define shenlogic.ast.signature-last
  [X] -> X
  [_ | Xs] -> (shenlogic.ast.signature-last Xs))

(define shenlogic.ast.make-clause Index Patterns Guard Body -> [clause Index Patterns Guard Body])
(define shenlogic.ast.clause-index [clause I _ _ _] -> I)
(define shenlogic.ast.clause-patterns [clause _ P _ _] -> P)
(define shenlogic.ast.clause-guard [clause _ _ G _] -> G)
(define shenlogic.ast.clause-body [clause _ _ _ B] -> B)

(define shenlogic.ast.make-some-guard G -> [some G])

\\ Canonical v2 frontend nodes.  The reader deliberately keeps source terms
\\ lossless; these helpers provide the small, tagged vocabulary consumed by
\\ later IR passes without changing the public program wrapper.
(define shenlogic.ast.normalize-pattern
  P -> (if (cons? P)
           (if (= (hd P) cons)
               [p-ctor cons
                [(shenlogic.ast.normalize-pattern (hd (tl P)))
                 (shenlogic.ast.normalize-pattern (hd (tl (tl P))))]]
               [p-ctor (hd P)
                (shenlogic.ast.normalize-pattern-list (tl P))])
           (if (= P [])
               [p-ctor nil []]
               (if (number? P)
                   [p-lit P]
                   (if (string? P)
                       [p-lit P]
                       (if (shenlogic.ast.atom-spelling? P "_")
                           [p-wild]
                           (if (variable? P) [p-var P] [p-lit P])))))))

(define shenlogic.ast.normalize-pattern-list
  [] -> []
  [P | Ps] -> [(shenlogic.ast.normalize-pattern P) |
               (shenlogic.ast.normalize-pattern-list Ps)])

(define shenlogic.ast.normalize-expr-default
  E -> (shenlogic.ast.normalize-expr E [] []))

(define shenlogic.ast.normalize-expr
  E Names Constructors ->
    (if (variable? E)
        [e-var E]
        (if (number? E)
            [e-value E]
            (if (string? E)
                [e-value E]
                (if (= E [])
                    [e-ctor nil []]
                    (if (cons? E)
                        (shenlogic.ast.normalize-application E Names Constructors)
                        [e-value E]))))))

(define shenlogic.ast.normalize-application
  [if C T F] Names Constructors ->
    [e-if (shenlogic.ast.normalize-expr C Names Constructors)
          (shenlogic.ast.normalize-expr T Names Constructors)
          (shenlogic.ast.normalize-expr F Names Constructors)]
  [let X A B] Names Constructors ->
    [e-let X (shenlogic.ast.normalize-expr A Names Constructors)
            (shenlogic.ast.normalize-expr B Names Constructors)]
  [and A B] Names Constructors ->
    [e-and (shenlogic.ast.normalize-expr A Names Constructors)
           (shenlogic.ast.normalize-expr B Names Constructors)]
  [or A B] Names Constructors ->
    [e-or (shenlogic.ast.normalize-expr A Names Constructors)
          (shenlogic.ast.normalize-expr B Names Constructors)]
  \\ cons is a builtin constructor in expressions as well as patterns; the
  \\ pattern-led constructor environment must not decide it.
  [cons A B] Names Constructors ->
    [e-ctor cons [(shenlogic.ast.normalize-expr A Names Constructors)
                  (shenlogic.ast.normalize-expr B Names Constructors)]]
  [Op | Args] Names Constructors ->
    (if (variable? Op)
        [e-apply Op (shenlogic.ast.normalize-pattern-list-expr Args Names Constructors)]
        (if (element? Op [+ - * = neq < > <= >= / div mod])
            [e-prim Op (shenlogic.ast.normalize-pattern-list-expr Args Names Constructors)]
            (if (element? Op Names)
                [e-call Op (shenlogic.ast.normalize-pattern-list-expr Args Names Constructors)]
                (if (shenlogic.ast.constructor-known? Op Constructors)
                    [e-ctor Op (shenlogic.ast.normalize-pattern-list-expr Args Names Constructors)]
                    [e-call Op (shenlogic.ast.normalize-pattern-list-expr Args Names Constructors)])))))

(define shenlogic.ast.normalize-pattern-list-expr
  [] _ _ -> []
  [X | Xs] Names Constructors ->
    [(shenlogic.ast.normalize-expr X Names Constructors) |
     (shenlogic.ast.normalize-pattern-list-expr Xs Names Constructors)])

(define shenlogic.ast.constructor-known?
  Tag [value-signature Cs] -> (shenlogic.ast.constructor-known? Tag Cs)
  _ [] -> false
  Tag [[constructor Source Target _] | Cs] ->
    (if (or (= Tag Source) (= Tag Target)) true
        (shenlogic.ast.constructor-known? Tag Cs))
  Tag [_ | Cs] -> (shenlogic.ast.constructor-known? Tag Cs))

\\ Constructor discovery is intentionally pattern-led: an application whose
\\ tag appears only in an expression is not silently admitted as a free value.
(define shenlogic.ast.constructor-environment
  [program Definitions] ->
    [value-signature (shenlogic.ast.constructor-definitions Definitions [])]
  _ -> [value-signature []])

(define shenlogic.ast.constructor-definitions
  [] Acc -> (reverse Acc)
  [[definition _ _ Clauses _] | Ds] Acc ->
    (shenlogic.ast.constructor-definitions Ds
      (shenlogic.ast.constructor-clauses Clauses Acc)))

(define shenlogic.ast.constructor-clauses
  [] Acc -> Acc
  [[clause _ Patterns _ _] | Cs] Acc ->
    (shenlogic.ast.constructor-clauses Cs
      (shenlogic.ast.constructor-patterns Patterns Acc)))

(define shenlogic.ast.constructor-patterns
  [] Acc -> Acc
  [P | Ps] Acc ->
    (shenlogic.ast.constructor-patterns Ps
      (shenlogic.ast.constructor-pattern P Acc)))

(define shenlogic.ast.constructor-pattern
  [p-ctor Tag Ps] Acc ->
    (let Next (if (shenlogic.ast.constructor-entry-arity? Tag (length Ps) Acc)
                  Acc
                  [[constructor Tag Tag (length Ps)] | Acc])
      (shenlogic.ast.constructor-patterns-normalized Ps Next))
  P Acc ->
    (let N (shenlogic.ast.normalize-pattern P)
      (shenlogic.ast.constructor-node N Acc)))

(define shenlogic.ast.constructor-node
  [p-ctor Tag Ps] Acc ->
    (let Arity (length Ps)
      (let Next (if (shenlogic.ast.constructor-entry-arity? Tag Arity Acc)
                    Acc
                    [[constructor Tag Tag Arity] | Acc])
        (shenlogic.ast.constructor-patterns-normalized Ps Next)))
  _ Acc -> Acc)

(define shenlogic.ast.constructor-patterns-normalized
  [] Acc -> Acc
  [P | Ps] Acc ->
    (shenlogic.ast.constructor-patterns-normalized Ps
      (shenlogic.ast.constructor-node P Acc)))

(define shenlogic.ast.constructor-entry?
  _ [] -> false
  Tag [[constructor Tag _ _] | _] -> true
  Tag [[constructor _ Tag _] | _] -> true
  Tag [_ | Cs] -> (shenlogic.ast.constructor-entry? Tag Cs))

(define shenlogic.ast.constructor-entry-arity?
  _ _ [] -> false
  Tag Arity [[constructor Tag _ Arity] | _] -> true
  Tag Arity [[constructor _ Tag Arity] | _] -> true
  Tag Arity [_ | Cs] ->
    (shenlogic.ast.constructor-entry-arity? Tag Arity Cs))

(define shenlogic.ast.normalize-program
  [program Definitions] ->
    (let Names (map (/. D (shenlogic.ast.definition-name D)) Definitions)
      (let Env (shenlogic.ast.constructor-environment [program Definitions])
        [program (shenlogic.ast.normalize-definitions Definitions Names
          (hd (tl Env)))]))
  X -> X)

(define shenlogic.ast.normalize-definitions
  [] _ _ -> []
  [[definition Name Sig Clauses Arity] | Ds] Names Constructors ->
    [[definition Name Sig (shenlogic.ast.normalize-clauses Clauses Names Constructors) Arity] |
      (shenlogic.ast.normalize-definitions Ds Names Constructors)])

(define shenlogic.ast.normalize-clauses
  [] _ _ -> []
  [[clause I Patterns Guard Body] | Cs] Names Constructors ->
    [[clause I (map (/. P (shenlogic.ast.normalize-pattern P)) Patterns)
            (shenlogic.ast.normalize-guard Guard Names Constructors)
            (shenlogic.ast.normalize-expr Body Names Constructors)] |
      (shenlogic.ast.normalize-clauses Cs Names Constructors)])

(define shenlogic.ast.normalize-guard
  none _ _ -> none
  [some G] Names Constructors ->
    [some (shenlogic.ast.normalize-expr G Names Constructors)]
  G Names Constructors ->
    [some (shenlogic.ast.normalize-expr G Names Constructors)])
