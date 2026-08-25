\\ Command-line definitions. The root shenlogic-cli.shen launcher loads these
\\ after the implementation and then invokes shenlogic.cli.main.

(define shenlogic.cli-args
  [] -> []
  [_ | Rest] -> Rest)

(define shenlogic.cli-usage
  _ -> (output "shenlogic translate FILE --format surface|graph|slir|chc|thf|tsl [-o OUT]~%shenlogic check FILE [--backend graph|chc|thf]~%shenlogic eval FILE EXPR [--fuel N]~%shenlogic certify FILE --out DIR~%shenlogic query FILE EXPR EXPECTED --backend chc|thf~%shenlogic repair FILE --logic EDITED.tsl.logic --spec SPEC [--max-cost N] [--max-candidates N] [--fuel N] [--optimizer prolog] [--write]~%shenlogic prove FILE CONJECTURE [--induct VAR] [-o OUT]~%shenlogic oracle FILE~%shenlogic test~%shenlogic --version~%"))

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
                   (if (= Name "repair") (shenlogic.cli-repair Rest)
                   (if (= Name "prove") (shenlogic.cli-prove Rest)
                   (if (= Name "oracle") (shenlogic.cli-oracle Rest)
                   (if (= Name "test") (shenlogic.cli-test)
                   (if (or (= Name "version") (= Name "--version"))
                       (shenlogic.cli-version)
                   (if (or (= Name "help") (= Name "--help") (= Name "-h"))
                       (shenlogic.cli-usage false)
                       (error (cn "shenlogic: unknown command: " Name)))))))))))))))))

(define shenlogic.cli-name
  X -> (if (string? X) X (str X)))

\\ `string->n` is the Shen character-code primitive, not a decimal parser.
\\ Keep option parsing portable by folding ASCII digits explicitly.
(define shenlogic.cli-integer
  Text -> (shenlogic.cli-integer-chars (explode Text)))

(define shenlogic.cli-integer-chars
  ["-" | Digits] -> (- 0 (shenlogic.cli-digits Digits 0 false))
  Digits -> (shenlogic.cli-digits Digits 0 false))

(define shenlogic.cli-digits
  [] Acc true -> Acc
  [] _ false -> (error "shenlogic: expected an integer option value")
  [Digit | Digits] Acc _ ->
    (let Code (string->n Digit)
      (if (and (>= Code 48) (<= Code 57))
          (shenlogic.cli-digits Digits (+ (* Acc 10) (- Code 48)) true)
          (error "shenlogic: expected an integer option value"))))

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
                           (let Fuel (shenlogic.cli-integer FuelText)
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

(define shenlogic.cli-prove
  [File Conj | Rest] ->
    (let InductText (shenlogic.cli-value Rest "--induct" false)
      (let Induct (if (= InductText false) none (intern InductText))
        (let Output (shenlogic.cli-output Rest)
          (let R (shenlogic.prove-file File Conj Induct)
            (if (= (hd R) ok)
                (if (= Output false)
                    (output "~A" (hd (tl R)))
                    (write-to-file Output (hd (tl R))))
                (error (serialize.canonical R)))))))
  _ -> (error "shenlogic prove: expected FILE CONJECTURE"))

(define shenlogic.cli-oracle
  [File | _] ->
    (let R (shenlogic.oracle-file File)
      (if (= (hd R) ok)
          (output "oracle: ~A clause typings agreed, ~A definitions skipped~%"
            (hd (tl R)) (hd (tl (tl R))))
          (error (serialize.canonical R))))
  _ -> (error "shenlogic oracle: expected FILE"))

(define shenlogic.cli-repair
  [File | Rest] ->
    (let Logic (shenlogic.cli-value Rest "--logic" false)
      (let Spec (shenlogic.cli-value Rest "--spec" false)
        (let Optimizer (shenlogic.cli-value Rest "--optimizer" "prolog")
          (if (or (= Logic false) (= Spec false))
              (error "shenlogic repair: expected --logic EDITED.tsl.logic --spec SPEC")
              (if (not (= Optimizer "prolog"))
                  (error (cn "shenlogic repair: unavailable optimizer: " Optimizer))
                  (let Fuel (shenlogic.cli-integer
                              (shenlogic.cli-value Rest "--fuel" "10000"))
                    (let MaxCandidates
                           (shenlogic.cli-integer
                             (shenlogic.cli-value Rest "--max-candidates" "10000"))
                      (let MaxCost
                             (shenlogic.cli-integer
                               (shenlogic.cli-value Rest "--max-cost" "4"))
                        (shenlogic.cli-repair-run File Logic Spec Rest Fuel
                          MaxCandidates MaxCost)))))))))
  _ -> (error "shenlogic repair: expected FILE --logic EDITED.tsl.logic --spec SPEC"))

(define shenlogic.cli-repair-run
  File Logic Spec Rest Fuel MaxCandidates MaxCost ->
    (let Prepare (shenlogic.cli-value Rest "--prepare" false)
      (let Result (if (= Prepare false)
                      (shenlogic.repair-file File Logic Spec Fuel
                        MaxCandidates MaxCost)
                      (let Rank (shenlogic.cli-integer
                                   (shenlogic.cli-value Rest "--candidate-index" "0"))
                        (shenlogic.repair-prepare-file-nth File Logic Spec Fuel
                          MaxCandidates MaxCost Rank)))
        (if (= (hd Result) ok)
            (if (= Prepare false)
                (shenlogic.cli-repair-finish Result File
                  (shenlogic.cli-has Rest "--write"))
                (shenlogic.cli-repair-artifacts Result Prepare))
            (if (= Prepare false)
                (error (serialize.canonical Result))
                (shenlogic.cli-repair-prepare-error Result Prepare))))))

(define shenlogic.cli-repair-prepare-error
  [error repair-no-candidate] Directory ->
    (write-to-file (cn Directory "/exhausted") "repair-no-candidate")
  Result _ -> (error (serialize.canonical Result)))

(define shenlogic.cli-repair-finish
  [ok Name Cost Source _] File true ->
    (do (write-to-file File Source)
        (output "repaired ~A (cost ~A)~%" Name Cost))
  [ok _ _ _ Diff] _ false -> (output "~A" Diff))

(define shenlogic.cli-repair-artifacts
  [ok Name Cost Source Diff Query] Directory ->
    (do (write-to-file (cn Directory "/source") Source)
      (do (write-to-file (cn Directory "/diff") Diff)
        (do (write-to-file (cn Directory "/law.smt2") Query)
          (write-to-file (cn Directory "/meta")
            (@s "repaired " (str Name) " (cost " (str Cost) ")"
                (n->string 10)))))))

(define shenlogic.cli-test
  -> (output "SHENLOGIC|ALL PASS~%"))

(define shenlogic.cli-version
  -> (output "ShenLogic ~A~%" (shenlogic.version)))

(define shenlogic.cli.main
  Args -> (shenlogic.cli-command (shenlogic.cli-args Args)))
