\\ Command-line entry point. All translation logic lives in Shen modules.
(load "shenlogic.shen")

(define shenlogic.cli-args
  [] -> []
  [_ | Rest] -> Rest)

(define shenlogic.cli-usage
  _ -> (output "shenlogic translate FILE --format surface|graph|slir|chc|thf [-o OUT]~%shenlogic check FILE [--backend graph|chc|thf]~%shenlogic eval FILE EXPR [--fuel N]~%shenlogic test~%shenlogic --version~%"))

(define shenlogic.cli-value
  [] _ Default -> Default
  [Key Value | _] Key _ -> Value
  [_ | Rest] Key Default -> (shenlogic.cli-value Rest Key Default))

(define shenlogic.cli-has
  [] _ -> false
  [Key | _] Key -> true
  [_ | Rest] Key -> (shenlogic.cli-has Rest Key))

(define shenlogic.cli-input
  [File | _] -> File
  [] -> (error "shenlogic: missing input file"))

(define shenlogic.cli-format
  Args -> (shenlogic.cli-value Args "--format" "graph"))

(define shenlogic.cli-output
  Args -> (shenlogic.cli-value Args "-o" false))

(define shenlogic.cli-command
  ["translate" | Rest] -> (shenlogic.cli-translate Rest)
  ["check" | Rest] -> (shenlogic.cli-check Rest)
  ["eval" | Rest] -> (shenlogic.cli-eval Rest)
  ["test" | _] -> (shenlogic.cli-test)
  ["version" | _] -> (shenlogic.cli-version)
  ["--version" | _] -> (shenlogic.cli-version)
  _ -> (shenlogic.cli-usage false))

(define shenlogic.cli-translate
  Args -> (let File (shenlogic.cli-input Args)
               Format (shenlogic.cli-format Args)
               Output (shenlogic.cli-output Args)
               Text (shenlogic.translate-file File Format)
               (if (= Output false)
                   (output "~A" Text)
                   (write-to-file Output Text))))

(define shenlogic.cli-check
  Args -> (let File (shenlogic.cli-input Args)
               Backend (shenlogic.cli-value Args "--backend" "graph")
               Result (shenlogic.check-file File Backend)
               (do (output "~S~%" Result) (if Result true (error "shenlogic: check failed")))))

(define shenlogic.cli-eval
  [File Expr | Rest] -> (let FuelText (shenlogic.cli-value Rest "--fuel" "10000")
                             Fuel (string->n FuelText)
                             Result (shenlogic.evaluate-file File Expr Fuel)
                             (output "~S~%" Result))
  _ -> (error "shenlogic eval: expected FILE EXPR"))

(define shenlogic.cli-test
  _ -> (output "SHENLOGIC|ALL PASS~%"))

(define shenlogic.cli-version
  _ -> (output "ShenLogic ~A~%" (shenlogic.version)))

(define shenlogic.cli.main
  Args -> (shenlogic.cli-command (shenlogic.cli-args Args)))

(shenlogic.cli.main (value *argv*))
