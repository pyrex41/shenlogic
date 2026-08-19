\\ Public workflow orchestration for ShenLogic 0.2.
\\
\\ This module deliberately sits above the parser, validator, and backends.  It
\\ is the CLI trust boundary: source is normalized and validated once, then
\\ every workflow consumes the same checked Rule IR.

(define shenlogic.workflow.expected
  Text -> (hd (read-from-string-unprocessed Text)))

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
             Theory (shenlogic.workflow.theory Program)
             CanonicalBackend (if (= (shenlogic.workflow.backend-name Backend) "chc")
                                 "chc" "thf")
             Model (shenlogic.translate-theory CanonicalBackend Program Theory)
             Query (if (= CanonicalBackend "chc")
                       (shenlogic.chc.query Model "shenlogic_query")
                       (@s Model (n->string 10)
                           "thf(shenlogic_query,conjecture,($true))."
                           (n->string 10)))
             [ok Backend Query])
        [error invalid-backend Backend]))
