\\ Bounded, forward-validated source repair for edited tsl equations.
\\
\\ The repairer deliberately treats generated logic as a view.  It accepts
\\ edits only below the `; equations` marker, reconstructs source-shaped
\\ clause candidates, and asks the ordinary ShenLogic pipeline to render the
\\ edited equations again.  Prolog is used only to enumerate finite guard
\\ choices; validation and translation remain the arbiter.

(define repair.nl -> (n->string 10))
(define repair.cr -> (n->string 13))
(define repair.backslash -> (n->string 92))

(define repair.chars-string
  [] -> ""
  [C | Cs] -> (cn C (repair.chars-string Cs)))

(define repair.take
  _ 0 -> []
  [] _ -> []
  [X | Xs] N -> [X | (repair.take Xs (- N 1))])

(define repair.drop
  Xs 0 -> Xs
  [] _ -> []
  [_ | Xs] N -> (repair.drop Xs (- N 1)))

(define repair.slice
  Xs Start End -> (repair.take (repair.drop Xs Start) (- End Start)))

(define repair.lines
  Text -> (repair.lines-chars (explode Text) [] []))

(define repair.lines-chars
  [] RevLine RevLines ->
    (reverse [(repair.chars-string (reverse RevLine)) | RevLines])
  [C | Cs] RevLine RevLines ->
    (if (= C (repair.nl))
        (repair.lines-chars Cs []
          [(repair.chars-string (reverse RevLine)) | RevLines])
        (if (= C (repair.cr))
            (repair.lines-chars Cs RevLine RevLines)
            (repair.lines-chars Cs [C | RevLine] RevLines))))

(define repair.join-lines
  [] -> ""
  [L] -> L
  [L | Ls] -> (@s L (repair.nl) (repair.join-lines Ls)))

(define repair.equation-parts
  Text -> (repair.equation-parts-lines (repair.lines Text) []))

(define repair.equation-parts-lines
  [] _ -> [error repair-missing-equations]
  ["; equations" | Lines] Prefix -> [ok (reverse Prefix) Lines]
  [L | Lines] Prefix -> (repair.equation-parts-lines Lines [L | Prefix]))

(define repair.nonempty-lines
  [] -> []
  ["" | Ls] -> (repair.nonempty-lines Ls)
  [L | Ls] -> [L | (repair.nonempty-lines Ls)])

(define repair.read-one
  Text -> (trap-error
            (let Forms (read-from-string-unprocessed Text)
              (if (and (cons? Forms) (= (tl Forms) []))
                  [ok (hd Forms)]
                  [error repair-malformed-equation Text]))
            (/. E [error repair-malformed-equation Text])))

(define repair.read-equations
  [] Acc -> [ok (reverse Acc)]
  [L | Ls] Acc ->
    (let R (repair.read-one L)
      (if (= (hd R) ok)
          (repair.read-equations Ls [(hd (tl R)) | Acc])
          R)))

(define repair.parse-tsl
  Text -> (let Parts (repair.equation-parts Text)
            (if (= (hd Parts) ok)
                (let Lines (repair.nonempty-lines (hd (tl (tl Parts))))
                  (let Equations (repair.read-equations Lines [])
                    (if (= (hd Equations) ok)
                        [ok (hd (tl Parts)) (hd (tl Equations))]
                        Equations)))
                Parts)))

\\ Alpha-normalization is used for comparison only.  Binder names are
\\ replaced by structural [bound N] terms, including occurrences in types.
(define repair.lookup-bound
  _ [] -> none
  X [[X N] | _] -> [found N]
  X [_ | Rest] -> (repair.lookup-bound X Rest))

(define repair.alpha
  Form -> (hd (repair.alpha-1 Form [] 0)))

(define repair.alpha-1
  [all X : T Body] Env N ->
    (let AT (hd (repair.alpha-1 T Env N))
      (let AB (repair.alpha-1 Body [[X N] | Env] (+ N 1))
        [[all [bound N] : AT (hd AB)] (hd (tl AB))]))
  [some X : T Body] Env N ->
    (let AT (hd (repair.alpha-1 T Env N))
      (let AB (repair.alpha-1 Body [[X N] | Env] (+ N 1))
        [[some [bound N] : AT (hd AB)] (hd (tl AB))]))
  [X | Xs] Env N ->
    (let A (repair.alpha-1 X Env N)
      (let As (repair.alpha-list Xs Env (hd (tl A)))
        [[(hd A) | (hd As)] (hd (tl As))]))
  X Env N ->
    (let F (repair.lookup-bound X Env)
      [(if (= F none) X [bound (hd (tl F))]) N]))

(define repair.alpha-list
  [] _ N -> [[] N]
  [X | Xs] Env N ->
    (let A (repair.alpha-1 X Env N)
      (let As (repair.alpha-list Xs Env (hd (tl A)))
        [[(hd A) | (hd As)] (hd (tl As))])))

(define repair.alpha-list-top
  [] -> []
  [F | Fs] -> [(repair.alpha F) | (repair.alpha-list-top Fs)])

(define repair.strip-quantifiers
  [all _ : _ Body] -> (repair.strip-quantifiers Body)
  [some _ : _ Body] -> (repair.strip-quantifiers Body)
  F -> F)

(define repair.core-equation
  Formula -> (let Core (repair.strip-quantifiers Formula)
               (if (and (cons? Core) (= (length Core) 3)
                        (= (hd (tl Core)) =>))
                   [ok (hd Core) (hd (tl (tl Core)))]
                   [ok true Core])))

(define repair.equation-info
  Formula -> (let C (repair.core-equation Formula)
               (if (= (hd C) ok)
                   (let Ante (hd (tl C))
                     (let Eq (hd (tl (tl C)))
                       (if (and (cons? Eq) (= (length Eq) 3)
                                (= (hd (tl Eq)) =))
                           (let Lhs (hd Eq)
                             (if (and (cons? Lhs) (symbol? (hd Lhs)))
                                 [ok (hd Lhs) (tl Lhs) (hd (tl (tl Eq)))
                                  Ante Formula]
                                 [error repair-malformed-equation Formula]))
                           [error repair-malformed-equation Formula])))
                   C)))

(define repair.equation-names
  [] Acc -> [ok (reverse Acc)]
  [F | Fs] Acc -> (let I (repair.equation-info F)
                    (if (= (hd I) ok)
                        (repair.equation-names Fs [(hd (tl I)) | Acc])
                        I)))

(define repair.unique
  [] -> []
  [X | Xs] -> (if (element? X Xs) (repair.unique Xs)
                  [X | (repair.unique Xs)]))

(define repair.equations-for
  _ [] -> []
  Name [F | Fs] -> (let I (repair.equation-info F)
                     (if (and (= (hd I) ok) (= (hd (tl I)) Name))
                         [F | (repair.equations-for Name Fs)]
                         (repair.equations-for Name Fs))))

(define repair.changed-names
  Names Original Edited Acc ->
    (if (= Names [])
        (reverse Acc)
        (let Name (hd Names)
          (let A (repair.alpha-list-top (repair.equations-for Name Original))
            (let B (repair.alpha-list-top (repair.equations-for Name Edited))
              (repair.changed-names (tl Names) Original Edited
                (if (= A B) Acc [Name | Acc])))))))

(define repair.target
  Original Edited ->
    (let ON (repair.equation-names Original [])
      (if (= (hd ON) ok)
          (let EN (repair.equation-names Edited [])
            (if (= (hd EN) ok)
                (let Names (repair.unique
                             (append (hd (tl ON)) (hd (tl EN))))
                  (let Changed (repair.changed-names Names Original Edited [])
                    (if (= Changed []) [error repair-no-equation-change]
                        (if (= (length Changed) 1) [ok (hd Changed)]
                            [error repair-multiple-functions Changed]))))
                EN))
          ON)))

\\ Inversion from source-shaped tsl terms to raw Shen terms and patterns.
(define repair.term-source
  [] -> []
  [cons H T] -> [cons (repair.term-source H) (repair.term-source T)]
  [F | Args] -> [F | (map (/. X (repair.term-source X)) Args)]
  X -> X)

(define repair.pattern-source
  X -> (repair.term-source X))

(define repair.contains-defined?
  X -> (if (cons? X)
           (or (repair.contains-defined? (hd X))
               (repair.contains-defined-list? (tl X)))
           (if (symbol? X)
               (shenlogic.validate.prefix? "defined-" (str X))
               false)))

(define repair.contains-defined-list?
  [] -> false
  [X | Xs] -> (or (repair.contains-defined? X)
                  (repair.contains-defined-list? Xs)))

(define repair.flatten-and
  [and | Fs] -> (repair.flatten-and-list Fs)
  F -> [F])

(define repair.flatten-and-list
  [] -> []
  [[and | Gs] | Fs] -> (append (repair.flatten-and-list Gs)
                               (repair.flatten-and-list Fs))
  [F | Fs] -> [F | (repair.flatten-and-list Fs)])

(define repair.guard-safe?
  F -> (and (not (repair.contains-defined? F))
            (not (repair.contains-symbol? => F))
            (not (repair.contains-symbol? (intern "~") F))))

(define repair.contains-symbol?
  S X -> (if (cons? X)
             (or (repair.contains-symbol? S (hd X))
                 (repair.contains-symbol-list? S (tl X)))
             (= S X)))

(define repair.contains-symbol-list?
  _ [] -> false
  S [X | Xs] -> (or (repair.contains-symbol? S X)
                    (repair.contains-symbol-list? S Xs)))

(define repair.safe-conditions
  [] -> []
  [F | Fs] -> (if (repair.guard-safe? F)
                  [F | (repair.safe-conditions Fs)]
                  (repair.safe-conditions Fs)))

(define repair.adjoin
  X Xs -> (if (element? X Xs) Xs [X | Xs]))

(define repair.guard-options
  Ante Original ->
    (let Conditions (repair.safe-conditions (repair.flatten-and Ante))
      (let Options (repair.guard-options-conditions Conditions [none])
        (if (= Original no-original) Options
            (repair.adjoin Original Options)))))

(define repair.guard-options-conditions
  Conditions Acc ->
    (repair.guard-options-subsets (tl (repair.guard-subsets Conditions)) Acc))

(define repair.guard-subsets
  [] -> [[]]
  [F | Fs] -> (let Rest (repair.guard-subsets Fs)
                (append Rest (repair.guard-prepend-all F Rest))))

(define repair.guard-prepend-all
  _ [] -> []
  F [Xs | Rest] -> [[F | Xs] | (repair.guard-prepend-all F Rest)])

(define repair.guard-options-subsets
  [] Acc -> Acc
  [Fs | Rest] Acc ->
    (repair.guard-options-subsets Rest
      (repair.adjoin (repair.guard-choice Fs) Acc)))

(define repair.guard-choice
  [F] -> [some (repair.term-source F)]
  Fs -> [some [and | (map (/. F (repair.term-source F)) Fs)]])

(define repair.definition-clauses
  _ [] -> []
  Name [[definition Name _ Clauses _] | _] -> Clauses
  Name [_ | Ds] -> (repair.definition-clauses Name Ds))

(define repair.nth-or
  _ [] Default -> Default
  0 [X | _] _ -> X
  N [_ | Xs] Default -> (repair.nth-or (- N 1) Xs Default))

(define repair.original-guard
  Clauses I -> (let C (repair.nth-or I Clauses no-original)
                 (if (= C no-original) no-original
                     (shenlogic.ast.clause-guard C))))

(define repair.original-patterns
  Clauses I -> (let C (repair.nth-or I Clauses no-original)
                 (if (= C no-original) []
                     (shenlogic.ast.clause-patterns C))))

(define repair.patterns-source
  [] _ _ -> []
  [P | Ps] [O | Os] Used ->
    [(repair.restore-wildcards (repair.pattern-source P) O Used) |
      (repair.patterns-source Ps Os Used)]
  Ps _ _ -> (map (/. P (repair.pattern-source P)) Ps))

(define repair.restore-wildcards
  Pattern Original Used -> Original
    where (and (= Original (intern "_"))
               (and (variable? Pattern)
                    (not (repair.contains-symbol? Pattern Used))))
  [H | Ps] [H | Os] Used ->
    [H | (repair.restore-wildcards-list Ps Os Used)]
  Pattern _ _ -> Pattern)

(define repair.restore-wildcards-list
  [] [] _ -> []
  [P | Ps] [O | Os] Used ->
    [(repair.restore-wildcards P O Used) |
      (repair.restore-wildcards-list Ps Os Used)]
  Ps _ _ -> Ps)

(define repair.templates
  [] _ _ Acc -> [ok (reverse Acc)]
  [F | Fs] Name OriginalClauses Acc ->
    (let I (repair.equation-info F)
      (if (= (hd I) ok)
          (if (= (hd (tl I)) Name)
              (repair.templates Fs Name OriginalClauses
                [[template (length Acc)
                  (repair.patterns-source (hd (tl (tl I)))
                    (repair.original-patterns OriginalClauses (length Acc))
                    [(hd (tl (tl (tl I)))) |
                      (repair.safe-conditions
                        (repair.flatten-and
                          (hd (tl (tl (tl (tl I)))))))])
                  (repair.term-source (hd (tl (tl (tl I)))))
                  (repair.guard-options (hd (tl (tl (tl (tl I)))))
                    (repair.original-guard OriginalClauses (length Acc)))] | Acc])
              [error repair-internal-target-mismatch])
          I)))

(defprolog shenlogic.repair.member
  X [X | _] <--;
  X [_ | Xs] <-- (shenlogic.repair.member X Xs);)

(defprolog shenlogic.repair.select-guards
  [] [] <--;
  [Options | Rest] [Choice | Choices] <--
    (shenlogic.repair.member Choice Options)
    (shenlogic.repair.select-guards Rest Choices);)

(define repair.guard-pools
  [] -> []
  [[template _ _ _ Options] | Ts] ->
    [Options | (repair.guard-pools Ts)])

(define repair.guard-selections
  Templates Limit ->
    (let Pools (repair.bound-guard-pools
                  (reverse (repair.guard-pools Templates)) Limit 1 [])
      (prolog?
        (findall Choices
          (shenlogic.repair.select-guards (receive Pools) Choices)
          Results)
        (return Results))))

\\ Bound the Cartesian product before Prolog's findall materializes it.
(define repair.bound-guard-pools
  [] _ _ Acc -> Acc
  [Pool | Pools] Limit Product Acc ->
    (let Capacity (div Limit Product)
      (let Kept (repair.take Pool
                  (if (< (length Pool) Capacity) (length Pool) Capacity))
        (repair.bound-guard-pools Pools Limit (* Product (length Kept))
          [Kept | Acc]))))

(define repair.make-clauses
  [] [] -> []
  [[template I Ps Body _] | Ts] [Guard | Gs] ->
    [[clause I Ps Guard Body] | (repair.make-clauses Ts Gs)])

(define repair.definition
  [definition Name Signature _ Arity] Clauses ->
    [definition Name Signature Clauses Arity])

(define repair.find-definition
  _ [] -> not-found
  Name [[definition Name Sig Cs Arity] | _] ->
    [definition Name Sig Cs Arity]
  Name [_ | Ds] -> (repair.find-definition Name Ds))

(define repair.replace-definition
  _ _ [] -> []
  Name New [[definition Name _ _ _] | Ds] -> [New | Ds]
  Name New [D | Ds] -> [D | (repair.replace-definition Name New Ds)])

(define repair.program-candidate
  [program Definitions] Name New ->
    [program (repair.replace-definition Name New Definitions)])

(define repair.program-tsl
  RawProgram ->
    (trap-error
      (let Checked (shenlogic.unwrap (shenlogic.validate.program RawProgram))
        (let Program (shenlogic.ast.normalize-program Checked)
          (let Logic (shenlogic.unwrap (shenlogic.validate.logic Program))
            (let Theory (rules.compile Logic)
              [ok Program (shenlogic.unwrap (shenlogic.tsl.render Logic Theory))]))))
      (/. E [error repair-invalid-candidate])))

(define repair.constraints
  Text -> (trap-error
            (let Forms (read-from-string-unprocessed Text)
              (if (and (= (length Forms) 1)
                       (cons? (hd Forms))
                       (= (hd (hd Forms)) shenlogic-repair)
                       (= (hd (tl (hd Forms))) 1))
                  (repair.validate-constraints (tl (tl (hd Forms))) [])
                  [error repair-invalid-spec]))
            (/. E [error repair-invalid-spec])))

(define repair.validate-constraints
  [] Acc -> [ok (reverse Acc)]
  [[expect Expr Value] | Cs] Acc ->
    (repair.validate-constraints Cs [[expect Expr Value] | Acc])
    where (and (repair.ground? Expr) (repair.ground? Value))
  [[expect Expr Value] | _] _ ->
    [error repair-nonground-constraint [expect Expr Value]]
  [[forbid Expr Value] | Cs] Acc ->
    (repair.validate-constraints Cs [[forbid Expr Value] | Acc])
    where (and (repair.ground? Expr) (repair.ground? Value))
  [[forbid Expr Value] | _] _ ->
    [error repair-nonground-constraint [forbid Expr Value]]
  [[law Formula] | Cs] Acc ->
    (repair.validate-constraints Cs [[law Formula] | Acc])
  [_ | _] _ -> [error repair-invalid-spec-constraint])

(define repair.ground?
  X -> (if (variable? X) false
           (if (cons? X)
               (and (repair.ground? (hd X)) (repair.ground? (tl X)))
               true)))

(define repair.has-law?
  [] -> false
  [[law _] | _] -> true
  [_ | Cs] -> (repair.has-law? Cs))

\\ Restricted quantified-law lowering.  A law is checked as a graph-safety
\\ property: if every call needed by the antecedent and both sides terminates,
\\ the two sides may not differ.  Z3 proves this by showing sl_repair_bad is
\\ unreachable in the candidate's existing CHC theory.
(define repair.law-var-name
  Kind Law N -> (@s "|ShenLogic law " Kind " " (str Law) " " (str N) "|"))

(define repair.law-bad-name
  -> "|ShenLogic repair bad state|")

(define repair.law-open
  [all X : Type Body] Law N Env ->
    \\ Quantified non-numeric Value domains need explicit recognizer
    \\ predicates in CHC.  Until those are emitted, accepting them would let
    \\ Z3 range over junk values and manufacture spurious counterexamples.
    (if (not (= Type number))
        [error repair-unsupported-law-binder X Type]
        (repair.law-open Body Law (+ N 1)
          [[X Type (repair.law-var-name "i" Law N)] | Env]))
  [some _ : _ _] _ _ _ -> [error repair-existential-law]
  Body _ _ Env -> [ok (reverse Env) Body])

(define repair.law-env-find
  _ [] -> none
  X [[X Type Name] | _] -> [found Type Name]
  X [_ | Env] -> (repair.law-env-find X Env))

(define repair.law-env-decls
  [] -> ""
  [[_ number Name] | Env] ->
    (@s "(declare-var " Name " Int)" (repair.nl)
        (repair.law-env-decls Env))
  [[_ _ Name] | Env] ->
    (@s "(declare-var " Name " Value)" (repair.nl)
        (repair.law-env-decls Env)))

(define repair.law-number
  X Env ->
    (if (integer? X) [ok (str X)]
        (if (variable? X)
            (let F (repair.law-env-find X Env)
              (if (and (not (= F none)) (= (hd (tl F)) number))
                  [ok (hd (tl (tl F)))]
                  [error repair-law-number X]))
            (if (cons? X)
                (repair.law-number-application X Env)
                [error repair-law-number X]))))

(define repair.law-number-application
  [Op A B] Env ->
    (if (element? Op [+ - *])
        (let RA (repair.law-number A Env)
          (if (= (hd RA) ok)
              (let RB (repair.law-number B Env)
                (if (= (hd RB) ok)
                    [ok (@s "(" (str Op) " " (hd (tl RA)) " "
                             (hd (tl RB)) ")")]
                    RB))
              RA))
        [error repair-law-number [Op A B]])
  X _ -> [error repair-law-number X])

(define repair.law-relations
  [theory _ Relations _ _ _] -> Relations
  _ -> [])

(define repair.law-constructors
  [theory [value-signature Constructors] _ _ _ _] -> Constructors
  _ -> [])

(define repair.law-name-map
  [theory _ _ _ _ NameMap] -> NameMap
  _ -> [])

(define repair.law-relation?
  _ [] -> false
  Name [[relation Name _ _] | _] -> true
  Name [_ | Rs] -> (repair.law-relation? Name Rs))

(define repair.law-term
  X Env Theory Law Counter ->
    (if (variable? X)
        (let F (repair.law-env-find X Env)
          (if (= F none) [error repair-free-law-variable X]
              (if (= (hd (tl F)) number)
                  [ok (@s "(VInt " (hd (tl (tl F))) ")") [] "" Counter]
                  [ok (hd (tl (tl F))) [] "" Counter])))
        (if (integer? X)
            [ok (@s "(VInt " (str X) ")") [] "" Counter]
            (if (string? X)
                [ok (@s "(VString " (shenlogic.chc.v2-quote X) ")") [] "" Counter]
                (if (= X true) [ok "VTrue" [] "" Counter]
                (if (= X false) [ok "VFalse" [] "" Counter]
                (if (= X []) [ok "VNil" [] "" Counter]
                (if (cons? X)
                    (repair.law-term-application X Env Theory Law Counter)
                    [ok (@s "(VSymbol " (shenlogic.chc.v2-quote (str X)) ")")
                        [] "" Counter]))))))))

(define repair.law-term-application
  [Op A B] Env Theory Law Counter ->
    (if (element? Op [+ - *])
        (let N (repair.law-number [Op A B] Env)
          (if (= (hd N) ok)
              [ok (@s "(VInt " (hd (tl N)) ")") [] "" Counter]
              N))
        (repair.law-term-compound [Op A B] Env Theory Law Counter))
  [Head | Args] Env Theory Law Counter ->
    (repair.law-term-compound [Head | Args] Env Theory Law Counter))

(define repair.law-term-compound
  [cons H T] Env Theory Law Counter ->
    (repair.law-term-cons H T Env Theory Law Counter)
  [Head | Args] Env Theory Law Counter ->
    (repair.law-term-head Head Args Env Theory Law Counter))

(define repair.law-term-cons
  H T Env Theory Law Counter ->
    (let RH (repair.law-term H Env Theory Law Counter)
      (if (= (hd RH) ok)
          (let RT (repair.law-term T Env Theory Law (repair.lt-counter RH))
            (if (= (hd RT) ok)
                [ok (@s "(VCons " (repair.lt-value RH) " "
                         (repair.lt-value RT) ")")
                    (append (repair.lt-premises RH) (repair.lt-premises RT))
                    (@s (repair.lt-decls RH) (repair.lt-decls RT))
                    (repair.lt-counter RT)]
                RT))
          RH)))

(define repair.law-term-head
  Head Args Env Theory Law Counter ->
    (let Relations (repair.law-relations Theory)
      (if (repair.law-relation? Head Relations)
          (if (= (shenlogic.chc.v2-relation-arity Head Relations)
                 (+ 1 (length Args)))
              (repair.law-term-call Head Args Env Theory Law Counter)
              [error repair-law-call-arity Head (length Args)])
          (let Constructors (repair.law-constructors Theory)
            (if (= (shenlogic.chc.v2-ctor-arity Head Constructors)
                   (length Args))
                (repair.law-term-constructor Head Args Env Theory Law Counter)
                [error repair-unknown-law-term Head (length Args)])))))

(define repair.law-term-call
  Head Args Env Theory Law Counter ->
    (let RArgs (repair.law-terms Args Env Theory Law Counter [] [] "")
      (if (= (hd RArgs) ok)
          (let N (repair.lts-counter RArgs)
            (let Result (repair.law-var-name "r" Law N)
              [ok Result
               (append (repair.lts-premises RArgs)
                 [(@s "(" (shenlogic.chc.v2-relation-name Head
                             (repair.law-name-map Theory)) " "
                        (repair.join-space
                          (append (repair.lts-values RArgs) [Result])) ")")])
               (@s (repair.lts-decls RArgs)
                   "(declare-var " Result " Value)" (repair.nl))
               (+ N 1)]))
          RArgs)))

(define repair.law-term-constructor
  Head Args Env Theory Law Counter ->
    (let RArgs (repair.law-terms Args Env Theory Law Counter [] [] "")
      (if (= (hd RArgs) ok)
          [ok (if (= Args [])
                  (shenlogic.chc.v2-ctor-symbol Head
                    (repair.law-constructors Theory))
                  (@s "(" (shenlogic.chc.v2-ctor-symbol Head
                             (repair.law-constructors Theory)) " "
                      (repair.join-space (repair.lts-values RArgs)) ")"))
              (repair.lts-premises RArgs) (repair.lts-decls RArgs)
              (repair.lts-counter RArgs)]
          RArgs)))

(define repair.lt-value [ok V _ _ _] -> V)
(define repair.lt-premises [ok _ Ps _ _] -> Ps)
(define repair.lt-decls [ok _ _ Ds _] -> Ds)
(define repair.lt-counter [ok _ _ _ N] -> N)

(define repair.law-terms
  [] _ _ _ Counter Values Premises Decls ->
    [ok (reverse Values) Premises Decls Counter]
  [X | Xs] Env Theory Law Counter Values Premises Decls ->
    (let R (repair.law-term X Env Theory Law Counter)
      (if (= (hd R) ok)
          (repair.law-terms Xs Env Theory Law (repair.lt-counter R)
            [(repair.lt-value R) | Values]
            (append Premises (repair.lt-premises R))
            (@s Decls (repair.lt-decls R)))
          R)))

(define repair.lts-values [ok Vs _ _ _] -> Vs)
(define repair.lts-premises [ok _ Ps _ _] -> Ps)
(define repair.lts-decls [ok _ _ Ds _] -> Ds)
(define repair.lts-counter [ok _ _ _ N] -> N)

(define repair.join-space
  [] -> ""
  [X] -> X
  [X | Xs] -> (@s X " " (repair.join-space Xs)))

(define repair.law-formula
  true _ _ _ Counter -> [ok "true" [] "" Counter]
  false _ _ _ Counter -> [ok "false" [] "" Counter]
  [and | Fs] Env Theory Law Counter ->
    (repair.law-formulas "and" Fs Env Theory Law Counter [] [] "")
  [or | Fs] Env Theory Law Counter ->
    (repair.law-formulas "or" Fs Env Theory Law Counter [] [] "")
  [Not F] Env Theory Law Counter ->
    (let R (repair.law-formula F Env Theory Law Counter)
      (if (= (hd R) ok)
          [ok (@s "(not " (repair.lf-value R) ")")
              (repair.lf-premises R) (repair.lf-decls R)
              (repair.lf-counter R)]
          R))
    where (= Not (intern "~"))
  [Op A B] Env Theory Law Counter ->
    (repair.law-prefix-formula Op A B Env Theory Law Counter)
      where (element? Op [< > <= >=])
  [A Op B] Env Theory Law Counter ->
    (if (element? Op [< > <= >=])
        (let RA (repair.law-number A Env)
          (if (= (hd RA) ok)
              (let RB (repair.law-number B Env)
                (if (= (hd RB) ok)
                    [ok (@s "(" (str Op) " " (hd (tl RA)) " "
                             (hd (tl RB)) ")") [] "" Counter]
                    RB))
              RA))
        (if (= Op =)
            (let RA (repair.law-term A Env Theory Law Counter)
              (if (= (hd RA) ok)
                  (let RB (repair.law-term B Env Theory Law
                             (repair.lt-counter RA))
                    (if (= (hd RB) ok)
                        [ok (@s "(= " (repair.lt-value RA) " "
                                 (repair.lt-value RB) ")")
                            (append (repair.lt-premises RA)
                              (repair.lt-premises RB))
                            (@s (repair.lt-decls RA) (repair.lt-decls RB))
                            (repair.lt-counter RB)]
                        RB))
                  RA))
            [error repair-unsupported-law-formula [A Op B]]))
  F _ _ _ _ -> [error repair-unsupported-law-formula F])

(define repair.law-prefix-formula
  Op A B Env _ _ Counter ->
    (let RA (repair.law-number A Env)
      (if (= (hd RA) ok)
          (let RB (repair.law-number B Env)
            (if (= (hd RB) ok)
                [ok (@s "(" (str Op) " " (hd (tl RA)) " "
                         (hd (tl RB)) ")") [] "" Counter]
                RB))
          RA)))

(define repair.law-formulas
  Op [] _ _ _ Counter Values Premises Decls ->
    [ok (if (= Op "and") "true" "false") Premises Decls Counter]
  Op Fs Env Theory Law Counter Values Premises Decls ->
    (repair.law-formulas-1 Op Fs Env Theory Law Counter Values Premises Decls))

(define repair.law-formulas-1
  Op [] _ _ _ Counter Values Premises Decls ->
    [ok (@s "(" Op " " (repair.join-space (reverse Values)) ")")
        Premises Decls Counter]
  Op [F | Fs] Env Theory Law Counter Values Premises Decls ->
    (let R (repair.law-formula F Env Theory Law Counter)
      (if (= (hd R) ok)
          (repair.law-formulas-1 Op Fs Env Theory Law (repair.lf-counter R)
            [(repair.lf-value R) | Values]
            (append Premises (repair.lf-premises R))
            (@s Decls (repair.lf-decls R)))
          R)))

(define repair.lf-value [ok V _ _ _] -> V)
(define repair.lf-premises [ok _ Ps _ _] -> Ps)
(define repair.lf-decls [ok _ _ Ds _] -> Ds)
(define repair.lf-counter [ok _ _ _ N] -> N)

(define repair.law-core
  [Ante => Conclusion] -> [Ante Conclusion]
  Conclusion -> [true Conclusion])

(define repair.law-one
  Formula Theory Law ->
    (let Open (repair.law-open Formula Law 0 [])
      (if (= (hd Open) ok) (repair.law-one-open Open Theory Law) Open)))

(define repair.law-one-open
  [ok Env Body] Theory Law ->
    (let Core (repair.law-core Body)
      (let Ante (repair.law-formula (hd Core) Env Theory Law 0)
        (if (= (hd Ante) ok)
            (repair.law-one-conclusion Env Theory Law Ante (hd (tl Core)))
            Ante))))

(define repair.law-one-conclusion
  Env Theory Law Ante [Left = Right] ->
    (repair.law-equality Env Theory Law Ante Left Right)
  _ _ _ _ Conclusion -> [error repair-law-not-equation Conclusion])

(define repair.law-equality
  Env Theory Law Ante Left Right ->
    (let L (repair.law-term Left Env Theory Law (repair.lf-counter Ante))
      (if (= (hd L) ok)
          (let R (repair.law-term Right Env Theory Law (repair.lt-counter L))
            (if (= (hd R) ok)
                (let Body (repair.smt-and
                            (append (repair.lf-premises Ante)
                              (append [(repair.lf-value Ante)]
                                (append (repair.lt-premises L)
                                  (append (repair.lt-premises R)
                                    [(@s "(not (= " (repair.lt-value L) " "
                                          (repair.lt-value R) "))")])))))
                  [ok (@s (repair.law-env-decls Env)
                          (repair.lf-decls Ante) (repair.lt-decls L)
                          (repair.lt-decls R))
                      (@s "(rule (=> " Body " " (repair.law-bad-name) "))"
                          (repair.nl))])
                R))
          L)))

(define repair.smt-and
  [] -> "true"
  [X] -> X
  Xs -> (@s "(and " (repair.join-space Xs) ")"))

(define repair.law-blocks
  [] _ _ Decls Rules -> [ok Decls Rules]
  [[law Formula] | Cs] Theory Law Decls Rules ->
    (let R (repair.law-one Formula Theory Law)
      (if (= (hd R) ok)
          (repair.law-blocks Cs Theory (+ Law 1)
            (@s Decls (hd (tl R))) (@s Rules (hd (tl (tl R)))))
          R))
  [_ | Cs] Theory Law Decls Rules ->
    (repair.law-blocks Cs Theory Law Decls Rules))

(define repair.law-query
  Program Constraints ->
    (if (not (repair.has-law? Constraints)) [ok ""]
        (let Theory (rules.compile Program)
          (let CHC (shenlogic.chc.render Theory nonlinear)
            (if (= (hd CHC) ok)
                (let Blocks (repair.law-blocks Constraints Theory 0 "" "")
                  (if (= (hd Blocks) ok)
                      [ok (@s (hd (tl CHC)) (repair.nl) (hd (tl Blocks))
                              "(declare-rel " (repair.law-bad-name) " ())"
                              (repair.nl)
                              (hd (tl (tl Blocks)))
                              "(query " (repair.law-bad-name) ")" (repair.nl))]
                      Blocks))
                [error repair-law-chc-unavailable CHC])))))

(define repair.check-examples
  _ [] _ -> true
  Program [[expect Expr Value] | Cs] Fuel ->
    (if (= (evaluator-evaluate Program Expr Fuel) [value Value])
        (repair.check-examples Program Cs Fuel) false)
  Program [[forbid Expr Value] | Cs] Fuel ->
    (let R (evaluator-evaluate Program Expr Fuel)
      (if (and (cons? R) (= (hd R) value)
               (not (= (hd (tl R)) Value)))
          (repair.check-examples Program Cs Fuel) false))
  Program [[law _] | Cs] Fuel -> (repair.check-examples Program Cs Fuel)
  _ _ _ -> false)

(define repair.tree-size
  X -> (if (cons? X) (+ 1 (repair.tree-list-size X)) 1))

(define repair.tree-list-size
  [] -> 0
  [X | Xs] -> (+ (repair.tree-size X) (repair.tree-list-size Xs)))

(define repair.tree-cost
  X X -> 0
  X Y -> (if (and (cons? X) (cons? Y))
             (repair.list-cost X Y)
             1))

(define repair.list-cost
  [] [] -> 0
  [] Ys -> (repair.tree-list-size Ys)
  Xs [] -> (repair.tree-list-size Xs)
  [X | Xs] [Y | Ys] ->
    (+ (repair.tree-cost X Y) (repair.list-cost Xs Ys)))

(define repair.candidate-cost
  Original Candidate -> (repair.tree-cost Original Candidate))

(define repair.better?
  Cost Canon none -> true
  Cost Canon [best BestCost BestCanon _ _] ->
    (if (< Cost BestCost) true
        (if (> Cost BestCost) false
            (< (repair.string-compare Canon BestCanon) 0))))

(define repair.string-compare
  "" "" -> 0
  "" _ -> -1
  _ "" -> 1
  A B -> (let CA (string->n (pos A 0))
           (let CB (string->n (pos B 0))
             (if (< CA CB) -1
                 (if (> CA CB) 1
                     (repair.string-compare (tlstr A) (tlstr B)))))))

(define repair.insert-best
  Best [] -> [Best]
  [best Cost Canon NewDef Program] [Prior | Rest] ->
    (if (repair.better? Cost Canon Prior)
        [[best Cost Canon NewDef Program] Prior | Rest]
        [Prior | (repair.insert-best [best Cost Canon NewDef Program] Rest)]))

(define repair.search-all
  _ _ _ _ _ [] _ _ Bests -> Bests
  RawProgram OriginalDef Name TargetAlpha Constraints
    [Guards | Rest] Fuel Remaining Bests ->
    (if (<= Remaining 0) Bests
        (let Templates (value *repair-active-templates*)
            (let NewDef (repair.definition OriginalDef
                          (repair.make-clauses Templates Guards))
              (let CandidateRaw (repair.program-candidate RawProgram Name NewDef)
                (let Rendered (repair.program-tsl CandidateRaw)
                  (if (= (hd Rendered) ok)
                      (let CP (repair.parse-tsl (hd (tl (tl Rendered))))
                        (if (and (= (hd CP) ok)
                                 (= (hd (tl CP))
                                    (value *repair-target-preamble*))
                                 (= (repair.alpha-list-top (hd (tl (tl CP))))
                                    (value *repair-target-equations*))
                                 (= (repair.alpha-list-top
                                      (repair.equations-for Name
                                        (hd (tl (tl CP))))) TargetAlpha)
                                 (repair.check-examples (hd (tl Rendered))
                                   Constraints Fuel))
                            (let Cost (repair.candidate-cost OriginalDef NewDef)
                              (let Canon (serialize.canonical NewDef)
                                (repair.search-all RawProgram OriginalDef Name
                                  TargetAlpha Constraints Rest Fuel (- Remaining 1)
                                  (if (<= Cost (value *repair-max-cost*))
                                      (repair.insert-best
                                        [best Cost Canon NewDef (hd (tl Rendered))]
                                        Bests)
                                      Bests))))
                            (repair.search-all RawProgram OriginalDef Name TargetAlpha
                              Constraints Rest Fuel (- Remaining 1) Bests)))
                      (repair.search-all RawProgram OriginalDef Name TargetAlpha
                        Constraints Rest Fuel (- Remaining 1) Bests))))))))

\\ Portable source span discovery.  Only top-level parenthesized forms are
\\ candidates; parentheses inside strings and Shen \\ comments are ignored.
(define repair.definition-span
  Text Name -> (repair.scan-top (explode Text) (explode Text) Name 0 0 false false -1))

(define repair.scan-top
  [] _ _ _ _ _ _ _ -> not-found
  [C | Cs] All Name I Depth InString InComment Start ->
    (if InComment
        (if (= C (repair.nl))
            (repair.scan-top Cs All Name (+ I 1) Depth InString false Start)
            (repair.scan-top Cs All Name (+ I 1) Depth InString true Start))
        (if InString
            (if (and (= C (repair.backslash)) (cons? Cs))
                (repair.scan-top (tl Cs) All Name (+ I 2) Depth
                  true false Start)
                (repair.scan-top Cs All Name (+ I 1) Depth
                  (not (= C (n->string 34))) false Start))
            (if (and (= C (repair.backslash)) (cons? Cs)
                     (= (hd Cs) (repair.backslash)))
                (repair.scan-top (tl Cs) All Name (+ I 2) Depth false true Start)
                (if (= C (n->string 34))
                    (repair.scan-top Cs All Name (+ I 1) Depth true false Start)
                    (if (= C "(")
                        (repair.scan-top Cs All Name (+ I 1) (+ Depth 1)
                          false false (if (= Depth 0) I Start))
                        (if (and (= C ")") (> Depth 0))
                            (let NextDepth (- Depth 1)
                              (if (= NextDepth 0)
                                  (let End (+ I 1)
                                    (let Text (repair.chars-string
                                                (repair.slice All Start End))
                                      (if (repair.definition-text? Text Name)
                                          [found Start End]
                                          (repair.scan-top Cs All Name (+ I 1) 0
                                            false false -1))))
                                  (repair.scan-top Cs All Name (+ I 1) NextDepth
                                    false false Start)))
                            (repair.scan-top Cs All Name (+ I 1) Depth
                              false false Start))))))))

(define repair.definition-text?
  Text Name -> (let R (repair.read-one Text)
                 (and (= (hd R) ok)
                      (let F (hd (tl R))
                        (and (cons? F) (= (hd F) define)
                             (cons? (tl F)) (= (hd (tl F)) Name))))))

(define repair.signature-tokens
  [signature Args Result] ->
    [(intern "{") | (append (repair.signature-parts Args Result)
                             [(intern "}")])]
  _ -> [])

(define repair.signature-parts
  [] Result -> [Result]
  [A | As] Result -> [A --> | (repair.signature-parts As Result)])

(define repair.clause-text
  [clause _ Patterns none Body] ->
    (@s "  " (repair.terms-text Patterns) " -> " (serialize-term Body))
  [clause _ Patterns [some Guard] Body] ->
    (@s "  " (repair.terms-text Patterns) " -> " (serialize-term Body)
        " where " (serialize-term Guard))
  [clause _ Patterns Guard Body] ->
    (@s "  " (repair.terms-text Patterns) " -> " (serialize-term Body)
        " where " (serialize-term Guard)))

(define repair.terms-text
  [] -> ""
  [X] -> (serialize-term X)
  [X | Xs] -> (@s (serialize-term X) " " (repair.terms-text Xs)))

(define repair.clauses-text
  [] -> ""
  [C] -> (repair.clause-text C)
  [C | Cs] -> (@s (repair.clause-text C) (repair.nl)
                  (repair.clauses-text Cs)))

(define repair.definition-text
  Definition -> (repair.definition-text-style Definition true))

(define repair.definition-text-style
  [definition Name Signature Clauses _] true ->
    (@s "(define " (str Name) (repair.nl)
        "  " (repair.terms-text (repair.signature-tokens Signature)) (repair.nl)
        (repair.clauses-text Clauses) ")")
  [definition Name _ Clauses _] false ->
    (@s "(define " (str Name) (repair.nl)
        (repair.clauses-text Clauses) ")"))

(define repair.inline-signature?
  Text [found Start End] ->
    (let R (repair.read-one
              (repair.chars-string
                (repair.slice (explode Text) Start End)))
      (if (= (hd R) ok)
          (repair.inline-signature-form? (hd (tl R)))
          false))
  _ _ -> false)

(define repair.inline-signature-form?
  [define _ First | _] -> (shenlogic.ast.atom-spelling? First "{")
  _ -> false)

(define repair.replace-span
  Text [found Start End] Replacement ->
    (let Chars (explode Text)
      (@s (repair.chars-string (repair.take Chars Start)) Replacement
          (repair.chars-string (repair.drop Chars End))))
  _ _ _ -> (error repair-source-span-not-found))

(define repair.prefix-lines
  [X | Xs] [X | Ys] Acc -> (repair.prefix-lines Xs Ys [X | Acc])
  Xs Ys Acc -> [(reverse Acc) Xs Ys])

(define repair.diff-lines
  Prefix "-" -> (repair.prefixed-lines Prefix "-")
  Prefix "+" -> (repair.prefixed-lines Prefix "+"))

(define repair.prefixed-lines
  [] _ -> ""
  [L | Ls] P -> (@s P L (repair.nl) (repair.prefixed-lines Ls P)))

\\ A deterministic single-hunk unified diff.  It trims the common prefix;
\\ the hunk intentionally includes the remaining suffix for portability and
\\ simplicity rather than depending on a host diff executable.
(define repair.unified-diff
  File Original Repaired ->
    (let Split (repair.prefix-lines (repair.lines Original)
                  (repair.lines Repaired) [])
      (let Prefix (hd Split)
        (let Old (hd (tl Split))
          (let New (hd (tl (tl Split)))
            (@s "--- " File (repair.nl) "+++ " File (repair.nl)
                "@@ -" (str (+ 1 (length Prefix))) "," (str (length Old))
                " +" (str (+ 1 (length Prefix))) "," (str (length New))
                " @@" (repair.nl)
                (repair.diff-lines Old "-")
                (repair.diff-lines New "+")))))))

(define repair.result
  File EditedText SpecText Fuel MaxCandidates MaxCost ->
    (do (set *repair-allow-laws* false)
      (do (set *repair-candidate-rank* 0)
          (repair.result-mode File EditedText SpecText Fuel MaxCandidates MaxCost))))

(define repair.prepare-result
  File EditedText SpecText Fuel MaxCandidates MaxCost ->
    (repair.prepare-result-nth File EditedText SpecText Fuel MaxCandidates MaxCost 0))

(define repair.prepare-result-nth
  _ _ _ _ _ _ Rank -> [error repair-invalid-candidate-index Rank]
    where (or (not (integer? Rank)) (< Rank 0))
  File EditedText SpecText Fuel MaxCandidates MaxCost Rank ->
    (do (set *repair-allow-laws* true)
      (do (set *repair-candidate-rank* Rank)
          (repair.result-mode File EditedText SpecText Fuel MaxCandidates MaxCost))))

(define repair.result-mode
  _ _ _ Fuel _ _ -> [error repair-invalid-fuel Fuel]
    where (or (not (integer? Fuel)) (<= Fuel 0))
  _ _ _ _ MaxCandidates _ -> [error repair-invalid-max-candidates MaxCandidates]
    where (or (not (integer? MaxCandidates)) (<= MaxCandidates 0))
  _ _ _ _ _ MaxCost -> [error repair-invalid-max-cost MaxCost]
    where (or (not (integer? MaxCost)) (< MaxCost 0))
  File EditedText SpecText Fuel MaxCandidates MaxCost ->
    (let OriginalText (read-file-as-string File)
      (let RawProgram (shenlogic.source-program File)
        (let OriginalTSL (shenlogic.translate-file File "tsl")
          (let OP (repair.parse-tsl OriginalTSL)
            (let EP (repair.parse-tsl EditedText)
              (repair.result-parsed File OriginalText RawProgram OP EP
                SpecText Fuel MaxCandidates MaxCost)))))))

(define repair.result-parsed
  File OriginalText RawProgram [ok OPreamble OEquations]
    [ok EPreamble EEquations] SpecText Fuel MaxCandidates MaxCost ->
      (if (= OPreamble EPreamble)
          (do (set *repair-target-preamble* EPreamble)
            (do (set *repair-target-equations*
                  (repair.alpha-list-top EEquations))
              (let Target (repair.target OEquations EEquations)
                (if (= (hd Target) ok)
                    (repair.result-target File OriginalText RawProgram
                      (hd (tl Target)) EEquations SpecText Fuel
                      MaxCandidates MaxCost)
                    Target))))
          [error repair-edited-scaffolding])
  _ _ _ [error E] _ _ _ _ _ -> [error E]
  _ _ _ _ [error E] _ _ _ _ -> [error E]
  _ _ _ OP EP _ _ _ _ -> [error repair-invalid-tsl OP EP])

(define repair.result-target
  File OriginalText RawProgram Name EEquations SpecText Fuel MaxCandidates MaxCost ->
    (let OriginalDef (repair.find-definition Name
                        (shenlogic.ast.program-definitions RawProgram))
      (if (= OriginalDef not-found)
          [error repair-target-not-found Name]
          (let Specs (repair.constraints SpecText)
            (if (= (hd Specs) ok)
                (repair.result-specs File OriginalText RawProgram Name
                  OriginalDef EEquations (hd (tl Specs)) Fuel MaxCandidates MaxCost)
                Specs)))))

(define repair.result-specs
  _ _ _ _ _ _ Specs _ _ _ -> [error repair-law-solver-required]
    where (and (repair.has-law? Specs)
               (not (value *repair-allow-laws*)))
  File OriginalText RawProgram Name OriginalDef EEquations Specs Fuel MaxCandidates MaxCost ->
    (let TargetForms (repair.equations-for Name EEquations)
      (let TemplatesR (repair.templates TargetForms Name
                         (shenlogic.ast.definition-clauses OriginalDef) [])
        (if (= (hd TemplatesR) ok)
            (repair.result-templates File OriginalText RawProgram Name
              OriginalDef TargetForms Specs (hd (tl TemplatesR))
              Fuel MaxCandidates MaxCost)
            TemplatesR))))

(define repair.result-templates
  File OriginalText RawProgram Name OriginalDef TargetForms Specs Templates
    Fuel MaxCandidates MaxCost ->
      (let _ (set *repair-active-templates* Templates)
        (let _ (set *repair-max-cost* MaxCost)
          (let Selections (repair.guard-selections Templates MaxCandidates)
            (let Bests (repair.search-all RawProgram OriginalDef Name
                          (repair.alpha-list-top TargetForms) Specs Selections
                          Fuel MaxCandidates [])
              (let Best (repair.nth-or (value *repair-candidate-rank*) Bests none)
              (if (= Best none)
                  [error repair-no-candidate]
                  (repair.result-best File OriginalText Name Best))))))))

(define repair.result-best
  File OriginalText Name [best Cost _ NewDef CandidateProgram] ->
    (let Span (repair.definition-span OriginalText Name)
      (if (= Span not-found)
          [error repair-source-span-not-found Name]
          (let Source (repair.replace-span OriginalText Span
                         (repair.definition-text-style NewDef
                           (repair.inline-signature? OriginalText Span)))
            (let ReRead (repair.source-text-program Source)
              (if (and (= (hd ReRead) ok)
                       (= (hd (tl ReRead)) CandidateProgram))
                  [ok Name Cost Source
                   (repair.unified-diff File OriginalText Source)]
                  [error repair-source-reread-mismatch]))))))

(define repair.source-text-program
  Source -> (trap-error
              (let Parsed (shenlogic.reader.parse-program
                            (read-from-string-unprocessed Source))
                (if (= (hd Parsed) ok)
                    (let Checked (shenlogic.validate.program (hd (tl Parsed)))
                      (if (= (hd Checked) ok)
                          [ok (shenlogic.ast.normalize-program (hd (tl Checked)))]
                          [error repair-source-validation]))
                    Parsed))
              (/. E [error repair-source-reread])))
