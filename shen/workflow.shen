\\ Public workflow orchestration for ShenLogic 0.2.
\\
\\ This module deliberately sits above the parser, validator, and backends.  It
\\ is the CLI trust boundary: source is normalized and validated once, then
\\ every workflow consumes the same checked Rule IR.

(define shenlogic.workflow.expected
  Text -> (hd (read-from-string-unprocessed Text)))

\\ Query arguments are deliberately read without evaluation.  The query
\\ boundary accepts one closed source form and lowers only literal Values;
\\ this prevents an open term from becoming an unconstrained solver query.
(define shenlogic.workflow.read-one
  Text -> (let Forms (read-from-string-unprocessed Text)
             (if (and (cons? Forms) (= (tl Forms) []))
                 [ok (hd Forms)]
                 [error malformed-query-source])))

(define shenlogic.workflow.safe-read-one
  Text -> (trap-error (shenlogic.workflow.read-one Text)
                      (/. E [error malformed-query-source])))

(define shenlogic.workflow.definition-arity
  _ [] -> not-found
  Name [[definition Name _ _ Arity] | _] -> Arity
  Name [_ | Ds] -> (shenlogic.workflow.definition-arity Name Ds))

(define shenlogic.workflow.constructor-arity-list
  Tag [] -> not-found
  Tag [[constructor Source Target Arity] | Cs] ->
    (if (or (= Tag Source) (= Tag Target)) Arity
        (shenlogic.workflow.constructor-arity-list Tag Cs)))

(define shenlogic.workflow.closed-value
  X Constructors ->
    (if (variable? X)
        [error open-query-value]
        (if (integer? X)
            [ok [v-int [i-lit X]]]
            (if (string? X)
                [ok [v-string X]]
                (if (= X true)
                    [ok v-true]
                    (if (= X false)
                        [ok v-false]
                        (if (= X [])
                            [ok [v-ctor nil []]]
                            (if (cons? X)
                                (shenlogic.workflow.closed-application X Constructors)
                                [ok [v-symbol X]]))))))))

(define shenlogic.workflow.closed-application
  [cons H T] Constructors ->
    (let A (shenlogic.workflow.closed-value H Constructors)
      (if (= (hd A) ok)
          (let B (shenlogic.workflow.closed-value T Constructors)
            (if (= (hd B) ok)
                [ok [v-ctor cons [(hd (tl A)) (hd (tl B))]]] B)) A))
  [nil] _ -> [ok [v-ctor nil []]]
  [ctor Tag Args] Constructors ->
    (shenlogic.workflow.closed-constructor Tag Args Constructors)
  [constructor Tag Args] Constructors ->
    (shenlogic.workflow.closed-constructor Tag Args Constructors)
  [Tag | Args] Constructors ->
    (let Arity (shenlogic.workflow.constructor-arity-list Tag Constructors)
      (if (= Arity not-found)
          [error unsupported-query-value]
          (if (= Arity (length Args))
              (shenlogic.workflow.closed-constructor Tag Args Constructors)
              [error query-constructor-arity]))))

(define shenlogic.workflow.closed-constructor
  Tag Args Constructors ->
    (let Arity (shenlogic.workflow.constructor-arity-list Tag Constructors)
      (if (= Arity not-found)
          [error unknown-query-constructor]
          (if (= Arity (length Args))
              (let Values (shenlogic.workflow.closed-values Args Constructors)
                (if (= (hd Values) ok)
                    [ok [v-ctor Tag (hd (tl Values))]] Values))
              [error query-constructor-arity]))))

(define shenlogic.workflow.closed-values
  [] _ -> [ok []]
  [X | Xs] Constructors ->
    (let A (shenlogic.workflow.closed-value X Constructors)
      (if (= (hd A) ok)
          (let B (shenlogic.workflow.closed-values Xs Constructors)
            (if (= (hd B) ok)
                [ok [(hd (tl A)) | (hd (tl B))]] B)) A)))

(define shenlogic.workflow.query-expression
  [Name | Args] Definitions Constructors ->
    (let Arity (shenlogic.workflow.definition-arity Name Definitions)
      (if (= Arity not-found)
          [error unknown-query-function]
          (if (= Arity (length Args))
              (let Values (shenlogic.workflow.closed-values Args Constructors)
                (if (= (hd Values) ok)
                    [ok [Name (hd (tl Values))]] Values))
              [error query-function-arity])))
  _ _ _ -> [error malformed-query-expression])

(define shenlogic.workflow.backend-name
  X -> (if (string? X) X (str X)))

(define shenlogic.workflow.output
  Out Name Text -> (write-to-file (cn Out (cn "/" Name)) Text))

(define shenlogic.workflow.source
  File -> (let Read (shenlogic.unwrap (shenlogic.reader.read-program File))
               Checked (shenlogic.unwrap (shenlogic.validate.program Read))
               (shenlogic.ast.normalize-program Checked)))

(define shenlogic.workflow.theory
  Program -> (let Logic (shenlogic.unwrap (shenlogic.validate.logic Program))
                  (rules.compile Logic)))

\\ A certificate bundle is deterministic and solver-neutral.  Solver/proof
\\ adapters may consume theory.slir, theory.chc, and theory.thf independently.
(define shenlogic.certify-file
  File Out -> (let Program (shenlogic.workflow.source File)
                   Decision (decision.compile Program)
                   Theory (shenlogic.workflow.theory Program)
                   Slir (serialize.canonical [shenlogic-ir 2 Theory])
                   Graph (shenlogic.unwrap (graph.render Theory))
                   Chc (shenlogic.unwrap (shenlogic.chc.render Theory nonlinear))
                   Thf (shenlogic.unwrap (shenlogic.thf.render Theory full-model))
                   ValueSignature (certificate-theory-value-signature Theory)
                   Rules (shenlogic.workflow.theory-rules Theory)
                   NameMap (certificate-theory-name-map Theory)
                   LoweringSteps (shenlogic.workflow.lowering-steps Rules)
                   Certificate [shenlogic-certificate 1 Program ValueSignature
                     Decision Theory [chc Chc] [thf Thf] LoweringSteps NameMap]
                   Checked (certificate-check Certificate)
                   (if (= Checked [ok])
                       (do (shenlogic.workflow.output Out "normalized.ast"
                                                        (serialize.canonical Program))
                           (shenlogic.workflow.output Out "decision.slir"
                                                        (serialize.canonical Decision))
                           (shenlogic.workflow.output Out "theory.slir" Slir)
                           (shenlogic.workflow.output Out "theory.graph" Graph)
                           (shenlogic.workflow.output Out "theory.chc" Chc)
                           (shenlogic.workflow.output Out "theory.thf" Thf)
                           (shenlogic.workflow.output Out "certificate"
                                                        (serialize.canonical Certificate))
                           (shenlogic.workflow.output Out "manifest"
                             (serialize.canonical [shenlogic-cert 2 File
                                                   normalized.ast decision.slir
                                                   theory.slir theory.graph
                                                   theory.chc theory.thf certificate]))
                       [ok Out])
                       (error (serialize.canonical Checked)))))

(define shenlogic.workflow.theory-rules
  [theory _ _ Rules _ _] -> Rules
  _ -> [])

(define shenlogic.workflow.lowering-steps
  [] -> []
  [[rule Id _ _ Path _ _ _ _] | Rules] ->
    [[lowering-step Id Path chc]
     [lowering-step Id Path thf] |
     (shenlogic.workflow.lowering-steps Rules)])

\\ Query first compiles the selected backend, then checks the executable
\\ semantics for the requested closed value.  External CHC/THF solver hooks
\\ can replace this final check without changing the CLI contract.
(define shenlogic.query-file
  File Expr Expected Backend ->
    (if (or (= (shenlogic.workflow.backend-name Backend) "chc")
            (= (shenlogic.workflow.backend-name Backend) "thf"))
        (let Program (shenlogic.workflow.source File)
             Definitions (shenlogic.ast.program-definitions Program)
             Constructors (hd (tl (shenlogic.ast.constructor-environment Program)))
             ParsedExpr (shenlogic.workflow.safe-read-one Expr)
             ParsedExpected (shenlogic.workflow.safe-read-one Expected)
             (if (= (hd ParsedExpr) ok)
                 (if (= (hd ParsedExpected) ok)
                     (let QueryExpr (shenlogic.workflow.query-expression
                                      (hd (tl ParsedExpr)) Definitions Constructors)
                          QueryValue (shenlogic.workflow.closed-value
                                      (hd (tl ParsedExpected)) Constructors)
                          (if (= (hd QueryExpr) ok)
                              (if (= (hd QueryValue) ok)
                                  (let Theory (shenlogic.workflow.theory Program)
                                       CanonicalBackend
                                         (if (= (shenlogic.workflow.backend-name Backend)
                                                "chc") "chc" "thf")
                                       Model (shenlogic.translate-theory
                                                CanonicalBackend Program Theory)
                                       ValueSignature
                                         (certificate-theory-value-signature Theory)
                                       TheoryConstructors (hd (tl ValueSignature))
                                       NameMap (certificate-theory-name-map Theory)
                                       QueryForm (hd (tl QueryExpr))
                                       Name (hd QueryForm)
                                       QArgs (hd (tl QueryForm))
                                       Query (if (= CanonicalBackend "chc")
                                                 (shenlogic.chc.query-fact Model Name
                                                   QArgs (hd (tl QueryValue))
                                                   TheoryConstructors NameMap)
                                                 (shenlogic.thf.query-fact Model Name
                                                   QArgs (hd (tl QueryValue)) NameMap))
                                       [ok Backend Query])
                                  QueryValue)
                              QueryExpr))
                     ParsedExpected)
                 ParsedExpr))
        [error invalid-backend Backend]))
