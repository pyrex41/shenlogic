\\ Raw, non-evaluating Shen source reader.

(define shenlogic.reader.read-forms
  Text -> (read-from-string-unprocessed Text))

(define shenlogic.reader.read-program
  Path -> (shenlogic.reader.parse-program
            (shenlogic.reader.read-forms (read-file-as-string Path))))

(define shenlogic.reader.parse-program
  Forms -> (shenlogic.reader.parse-forms Forms [] (shenlogic.reader.declarations Forms)))

(define shenlogic.reader.parse-forms
  [] Acc _ -> [ok [program (reverse Acc)]]
  [[define Name | Tail] | Forms] Acc Sigs ->
    (let Parsed (shenlogic.reader.parse-define Name Tail)
      (if (= (hd Parsed) ok)
          (shenlogic.reader.parse-forms Forms
            [(shenlogic.reader.attach-signature (hd (tl Parsed)) Sigs) | Acc] Sigs)
          Parsed))
  [[declare Name Type] | Forms] Acc Sigs -> (shenlogic.reader.parse-forms Forms Acc [[Name Type] | Sigs])
  [_ | Forms] Acc Sigs -> (shenlogic.reader.parse-forms Forms Acc Sigs))

(define shenlogic.reader.parse-define
  Name Tail ->
    (let Split (shenlogic.reader.signature Tail)
      (let Signature (hd Split)
        (let Tokens (hd (tl Split))
          (let Parsed (shenlogic.reader.clauses Tokens 0 [])
            (if (= (hd Parsed) error)
                Parsed
                (let Clauses (hd (tl Parsed))
                  (if (= Clauses [])
                      [error sl-r001 Name]
                      [ok [definition Name Signature Clauses
                           (length (shenlogic.ast.clause-patterns (hd Clauses)))]]))))))))

(define shenlogic.reader.signature
  Tail -> (if (and (cons? Tail)
                       (shenlogic.ast.atom-spelling? (hd Tail) "{"))
              (shenlogic.reader.signature-loop (tl Tail) [])
              [none Tail]))

(define shenlogic.reader.signature-loop
  [] _ -> [none []]
  [X | Tail] Rev ->
    (if (shenlogic.ast.atom-spelling? X "}")
        [(shenlogic.ast.normalize-signature (reverse Rev)) Tail]
        (shenlogic.reader.signature-loop Tail [X | Rev])))

(define shenlogic.reader.clauses
  [] _ Acc -> [ok (reverse Acc)]
  Tokens Index Acc ->
    (let Split (shenlogic.reader.until-arrow Tokens [])
      (if (= (hd Split) error)
          Split
          (let Patterns (hd (tl Split))
            (let After (hd (tl (tl Split)))
              (if (= After [])
                  [error sl-r003 Index]
                  (let Body (hd After)
                    (let Rest (tl After)
                      (let Guarded (shenlogic.reader.guard Rest)
                        (let Guard (hd Guarded)
                          (let More (hd (tl Guarded))
                            (shenlogic.reader.clauses More (+ Index 1)
                              [[clause Index Patterns Guard Body] | Acc]))))))))))))

(define shenlogic.reader.until-arrow
  [] _ -> [error sl-r002]
  [X | Rest] Rev ->
    (if (shenlogic.ast.atom-spelling? X "->")
        [ok (reverse Rev) Rest]
        (shenlogic.reader.until-arrow Rest [X | Rev])))

(define shenlogic.reader.guard
  [where G | Rest] -> [[some G] Rest]
  Rest -> [none Rest])

(define shenlogic.reader.declarations
  [] -> []
  [[declare Name Type] | Rest] -> [[Name Type] | (shenlogic.reader.declarations Rest)]
  [_ | Rest] -> (shenlogic.reader.declarations Rest))

(define shenlogic.reader.lookup-signature
  _ [] -> none
  Name [[Name Type] | _] -> (shenlogic.ast.normalize-signature Type)
  Name [_ | Rest] -> (shenlogic.reader.lookup-signature Name Rest))

(define shenlogic.reader.attach-signature
  [definition Name Sig Clauses Arity] Sigs ->
    (if (= Sig none)
        [definition Name (shenlogic.reader.lookup-signature Name Sigs) Clauses Arity]
        [definition Name Sig Clauses Arity]))
