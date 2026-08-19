\\ Command-line definitions. The root shenlogic-cli.shen launcher loads these
\\ after the implementation and then invokes shenlogic.cli.main.

(define shenlogic.cli-args
  [] -> []
  [_ | Rest] -> Rest)

(define shenlogic.cli-usage
  _ -> (output "shenlogic translate FILE --format surface|graph|slir|chc|thf [-o OUT]~%shenlogic check FILE [--backend graph|chc|thf]~%shenlogic eval FILE EXPR [--fuel N]~%shenlogic certify FILE --out DIR~%shenlogic query FILE EXPR EXPECTED --backend chc|thf~%shenlogic test~%shenlogic --version~%"))

(define shenlogic.cli-value
  [] _ Default -> Default
  [Found Value | Rest] Key Default -> (if (= (shenlogic.cli-name Found)
                                               (shenlogic.cli-name Key)) Value
                                       (shenlogic.cli-value [Value | Rest] Key Default))
  [Found | Rest] Key Default -> (shenlogic.cli-value Rest Key Default))

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
  Args -> (if (= Args [])
              (error "shenlogic: missing command (try --help)")
              (let Name (shenlogic.cli-name (hd Args))
                (let Rest (tl Args)
                   (if (= Name "translate") (shenlogic.cli-translate Rest)
                   (if (= Name "check") (shenlogic.cli-check Rest)
                   (if (= Name "eval") (shenlogic.cli-eval Rest)
                   (if (= Name "certify") (shenlogic.cli-certify Rest)
                   (if (= Name "query") (shenlogic.cli-query Rest)
                   (if (= Name "test") (shenlogic.cli-test)
                   (if (or (= Name "version") (= Name "--version"))
                       (shenlogic.cli-version)
                   (if (or (= Name "help") (= Name "--help") (= Name "-h"))
                       (shenlogic.cli-usage false)
                       (error (cn "shenlogic: unknown command: " Name))))))))))))))

(define shenlogic.cli-name
  X -> (if (string? X) X (str X)))

(define shenlogic.cli-translate
  Args -> (let File (shenlogic.cli-input Args)
            (let Format (shenlogic.cli-format Args)
              (let Output (shenlogic.cli-output Args)
                (let Text (shenlogic.translate-file File Format)
                  (if (= Output false)
                      (output "~A" Text)
                      (write-to-file Output Text)))))))

(define shenlogic.cli-check
  Args -> (let File (shenlogic.cli-input Args)
            (let Backend (shenlogic.cli-value Args "--backend" "graph")
              (let Result (shenlogic.check-file File Backend)
                (do (output "~S~%" Result)
                    (if Result true (error "shenlogic: check failed")))))))

(define shenlogic.cli-eval
  [File Expr | Rest] -> (let FuelText (shenlogic.cli-value Rest "--fuel" "10000")
                           (let Fuel (string->n FuelText)
                             (let Result (shenlogic.evaluate-file File Expr Fuel)
                               (output "~S~%" Result))))
  _ -> (error "shenlogic eval: expected FILE EXPR"))

(define shenlogic.cli-certify
  [File | Rest] -> (let Out (shenlogic.cli-value Rest "--out" false)
                        (if (= Out false)
                            (error "shenlogic certify: expected --out DIR")
                            (let Result (shenlogic.certify-file File Out)
                              (output "~S~%" Result))))
  _ -> (error "shenlogic certify: expected FILE --out DIR"))

(define shenlogic.cli-query
  [File Expr Expected | Rest] ->
    (let Backend (shenlogic.cli-value Rest "--backend" "chc")
      (let Result (shenlogic.query-file File Expr Expected Backend)
        (if (= (hd Result) ok)
            (output "~A" (hd (tl (tl Result))))
            (error (serialize.canonical Result)))))
  _ -> (error "shenlogic query: expected FILE EXPR EXPECTED --backend chc|thf"))

(define shenlogic.cli-test
  -> (output "SHENLOGIC|ALL PASS~%"))

(define shenlogic.cli-version
  -> (output "ShenLogic ~A~%" (shenlogic.version)))

(define shenlogic.cli.main
  Args -> (shenlogic.cli-command (shenlogic.cli-args Args)))
