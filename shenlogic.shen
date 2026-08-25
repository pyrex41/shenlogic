\\ ShenLogic public loader. Keep this list explicit and deterministic.
(load "shen/ast.shen")
(load "shen/reader.shen")
(load "shen/validate.shen")
(load "shen/decision.shen")
(load "shen/rules.shen")
(load "shen/serialize.shen")
(load "shen/evaluator.shen")
(load "shen/certificate.shen")
(load "shen/surface.shen")
(load "shen/graph.shen")
(load "shen/chc.shen")
(load "shen/thf.shen")
(load "shen/typing.shen")
(load "shen/linarith.shen")
(load "shen/termination.shen")
(load "shen/tsl.shen")
(load "shen/prove.shen")
(load "shen/repair.shen")
(load "shen/workflow.shen")

(define shenlogic.version
  -> "0.2.0")

\\ Stable orchestration API used by the command line and external callers.
(define shenlogic.unwrap
  [ok X] -> X
  [error E] -> (error (if (string? E) E (serialize.canonical E)))
  [error E Context] -> (error (@s (str E) ": " (serialize.canonical Context)))
  [errors Es] -> (error (serialize.canonical Es))
  X -> X)

(define shenlogic.source-program
  File -> (let Parsed (shenlogic.unwrap (shenlogic.reader.read-program File))
                (shenlogic.unwrap (shenlogic.validate.program Parsed))))

(define shenlogic.program
  File -> (shenlogic.ast.normalize-program (shenlogic.source-program File)))

(define shenlogic.translate-file
  File Format ->
    (let Source (shenlogic.source-program File)
      (if (= Format "surface")
          (surface.translate Source)
          (let Program (shenlogic.ast.normalize-program Source)
            (let Checked (shenlogic.unwrap (shenlogic.validate.logic Program))
              (let Theory (rules.compile Checked)
                (shenlogic.translate-theory Format Checked Theory)))))))

(define shenlogic.translate-theory
  "surface" Program _ -> (surface.translate Program)
  "graph" _ Theory -> (graph.render Theory)
  "slir" _ Theory -> (serialize.canonical [shenlogic-ir 2 Theory])
  "chc" _ Theory -> (shenlogic.unwrap (shenlogic.chc.render Theory nonlinear))
  "thf" _ Theory -> (shenlogic.unwrap (shenlogic.thf.render Theory full-model))
  "tsl" Program Theory -> (shenlogic.unwrap (shenlogic.tsl.render Program Theory))
  Format _ _ -> (error (cn "unsupported format: " Format)))

(define shenlogic.check-file
  File Backend -> (let Output (shenlogic.translate-file File Backend)
                       (do Output true)))

(define shenlogic.evaluate-file
  File Expr Fuel -> (let Program (shenlogic.program File)
                         Expression (hd (read-from-string-unprocessed Expr))
                         (evaluator-evaluate Program Expression Fuel)))

\\ Public repair API.  The edited logic and repair contract remain separate
\\ files so callers can retain the exact artifacts used to produce a patch.
(define shenlogic.repair-file
  File LogicFile SpecFile Fuel MaxCandidates MaxCost ->
    (repair.result File (read-file-as-string LogicFile)
      (read-file-as-string SpecFile) Fuel MaxCandidates MaxCost))

\\ Preparation is the pure half of law checking.  It returns the same patch
\\ plus a self-contained CHC query for an external Z3 process.  The wrapper
\\ commits the source only after that query is unsatisfiable.
(define shenlogic.repair-prepare-file
  File LogicFile SpecFile Fuel MaxCandidates MaxCost ->
    (shenlogic.repair-prepare-file-nth File LogicFile SpecFile Fuel
      MaxCandidates MaxCost 0))

(define shenlogic.repair-prepare-file-nth
  File LogicFile SpecFile Fuel MaxCandidates MaxCost Rank ->
    (let SpecText (read-file-as-string SpecFile)
      (let Result (repair.prepare-result-nth File (read-file-as-string LogicFile)
                     SpecText Fuel MaxCandidates MaxCost Rank)
        (if (= (hd Result) ok)
            (shenlogic.repair-prepared Result SpecText)
            Result))))

(define shenlogic.repair-prepared
  [ok Name Cost Source Diff] SpecText ->
    (let Parsed (repair.source-text-program Source)
      (if (= (hd Parsed) ok)
          (let Specs (repair.constraints SpecText)
            (if (= (hd Specs) ok)
                (let Query (repair.law-query (hd (tl Parsed)) (hd (tl Specs)))
                  (if (= (hd Query) ok)
                      [ok Name Cost Source Diff (hd (tl Query))]
                      Query))
                Specs))
          Parsed)))
