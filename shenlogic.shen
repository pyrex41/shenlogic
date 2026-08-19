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

(define shenlogic.version
  -> "0.1.0")

\\ Stable orchestration API used by the command line and external callers.
(define shenlogic.unwrap
  [ok X] -> X
  [error E] -> (error E)
  [error E Context] -> (error (@s (str E) ": " (serialize.canonical Context)))
  [errors Es] -> (error (serialize.canonical Es))
  X -> X)

(define shenlogic.program
  File -> (let Parsed (shenlogic.unwrap (shenlogic.reader.read-program File))
                Checked (shenlogic.unwrap (shenlogic.validate.program Parsed))
                Checked))

(define shenlogic.translate-file
  File Format -> (let Source (shenlogic.program File)
                      Program (shenlogic.unwrap (shenlogic.validate.logic Source))
                      Theory (rules.compile Program)
                      (shenlogic.translate-theory Format Program Theory)))

(define shenlogic.translate-theory
  "surface" Program _ -> (surface.translate Program)
  "graph" _ Theory -> (graph.render Theory)
  "slir" _ Theory -> (serialize.canonical [shenlogic-ir 1 Theory])
  "chc" _ Theory -> (shenlogic.unwrap (shenlogic.chc.render Theory nonlinear))
  "thf" _ Theory -> (shenlogic.unwrap (shenlogic.thf.render Theory standard))
  Format _ _ -> (error (cn "unsupported format: " Format)))

(define shenlogic.check-file
  File Backend -> (let Output (shenlogic.translate-file File Backend)
                       (do Output true)))

(define shenlogic.evaluate-file
  File Expr Fuel -> (let Program (shenlogic.program File)
                         Expression (hd (read-from-string-unprocessed Expr))
                         (evaluator-evaluate Program Expression Fuel)))
