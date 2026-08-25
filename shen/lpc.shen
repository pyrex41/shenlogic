\\ LPC exit: render a function's tsl theory in the prop grammar of
\\ Tarver's LPC proof assistant (target: the datatype prop and d-rules of
\\ his published logic.shen), so his prover and the pedagogy of Logic,
\\ Proof and Computation drive proofs over ShenLogic translations.
\\
\\ The artifact is a loadable Shen source file defining
\\ (shenlogic-axioms F) per function; his intro rule consumes it through
\\ the one-line adapter shown in the header.  v1 admits checker-proven
\\ total functions whose theories stay inside his prop grammar: no
\\ comparisons, no arithmetic terms, no definedness atoms, no strings,
\\ no value sort, no function parameters.  That is exactly the
\\ append/map/first-shaped corpus his own samples use; anything else is
\\ rejected with a diagnostic, never approximated.

(define shenlogic.lpc.render
  Program Theory ->
    (let TR (tsl.type-program Program)
      (if (tsl.ok? TR)
          (let Tot (hd (tl (termination.classify Program)))
            (lpc.defs (hd (tl TR)) Tot ""))
          (tsl.render-error TR))))

(define lpc.defs
  [] _ Acc -> [ok (@s (lpc.header)
                      "(define shenlogic-axioms" (tsl.nl)
                      Acc ")" (tsl.nl))]
  [[t-def Name TVars Args Result TCs] | Ds] Tot Acc ->
    (if (not (tsl.total-function? Name Tot))
        [error [sl-lpc001 lpc-unsupported Name not-total]]
        (let Props (lpc.equations Name TCs [] Tot TVars [])
          (if (= (hd Props) ok)
              (lpc.defs Ds Tot
                (@s Acc "  " (str Name) " -> [" (tsl.nl)
                    (lpc.prop-lines (hd (tl Props)))
                    "  ]" (tsl.nl)))
              Props))))

(define lpc.header
  -> (let BB (@s (n->string 92) (n->string 92))
       (@s BB " ShenLogic axioms in LPC prop syntax." (tsl.nl)
           BB " Adapter for the LPC prover's intro rule:" (tsl.nl)
           BB "   (define axioms S -> (shenlogic-axioms S))" (tsl.nl)
           (tsl.nl))))

(define lpc.prop-lines
  [] -> ""
  [P] -> (@s "    " P (tsl.nl))
  [P | Ps] -> (@s "    " P (tsl.nl) (lpc.prop-lines Ps)))

(define lpc.equations
  _ [] _ _ _ Acc -> [ok (reverse Acc)]
  Name [TC | TCs] Prior Tot TVars Acc ->
    (let F (tsl.quantify-tvars TVars
             (tsl.equation-formula Name TC (reverse Prior) Tot TVars))
      (let R (lpc.prop F)
        (if (= (hd R) ok)
            (lpc.equations Name TCs [TC | Prior] Tot TVars
              [(hd (tl R)) | Acc])
            R))))

(define tsl.quantify-tvars
  [] F -> F
  TVars F -> [f-all-types TVars F])

(define lpc.prop
  [f-true] -> [ok "verum"]
  [f-false] -> [ok "falsum"]
  [f-eq A B] -> (lpc.two-term "=" A B)
  [f-not F] -> (lpc.wrap1 "~" (lpc.prop F))
  [f-and Fs] -> (lpc.junction "&" Fs)
  [f-or Fs] -> (lpc.junction "v" Fs)
  [f-imp F G] -> (lpc.two-prop "=>" (lpc.prop F) (lpc.prop G))
  [f-iff F G] -> (lpc.two-prop "<=>" (lpc.prop F) (lpc.prop G))
  [f-all [] F] -> (lpc.prop F)
  [f-all [[V T] | Bs] F] -> (lpc.binder "all" V T (lpc.prop [f-all Bs F]))
  [f-some [] F] -> (lpc.prop F)
  [f-some [[V T] | Bs] F] -> (lpc.binder "exists" V T (lpc.prop [f-some Bs F]))
  [f-all-types [] F] -> (lpc.prop F)
  [f-all-types [A | As] F] ->
    (lpc.wrap-type A (lpc.prop [f-all-types As F]))
  F -> [error [sl-lpc001 lpc-unsupported formula F]])

(define lpc.wrap1
  Op [ok S] -> [ok (@s "[" Op " " S "]")]
  _ E -> E)

(define lpc.two-prop
  Op [ok S1] [ok S2] -> [ok (@s "[" S1 " " Op " " S2 "]")]
  _ [error E] _ -> [error E]
  _ _ [error E] -> [error E])

(define lpc.two-term
  Op A B ->
    (let TA (lpc.term A)
      (if (= (hd TA) ok)
          (let TB (lpc.term B)
            (if (= (hd TB) ok)
                [ok (@s "[" (hd (tl TA)) " " Op " " (hd (tl TB)) "]")]
                TB))
          TA)))

\\ His & and v are binary; n-ary conjunctions nest to the right.
(define lpc.junction
  _ [F] -> (lpc.prop F)
  Op [F | Fs] -> (lpc.two-prop Op (lpc.prop F) (lpc.junction Op Fs))
  Op [] -> [error [sl-lpc001 lpc-unsupported empty-junction Op]])

(define lpc.binder
  Q V T Body ->
    (let TT (lpc.type T)
      (if (= (hd TT) ok)
          (lpc.wrap-binder Q V (hd (tl TT)) Body)
          TT)))

(define lpc.wrap-binder
  Q V TT [ok S] -> [ok (@s "[" Q " " (str V) " : " TT " " S "]")]
  _ _ _ E -> E)

(define lpc.wrap-type
  A [ok S] -> [ok (@s "[all " (str A) " : type " S "]")]
  _ E -> E)

(define lpc.type
  number -> [ok "nat"]
  boolean -> [ok "boolean"]
  symbol -> [ok "symbol"]
  [list T] -> (lpc.wrap1 "list" (lpc.type T))
  T -> (if (variable? T)
           [ok (str T)]
           [error [sl-lpc001 lpc-unsupported type T]]))

(define lpc.term
  [e-var V] -> [ok (str V)]
  [e-value N] -> (if (integer? N)
                     [ok (str N)]
                     (if (element? N [true false])
                         [ok (str N)]
                         (if (symbol? N)
                             [ok (str N)]
                             [error [sl-lpc001 lpc-unsupported term N]])))
  [e-ctor nil []] -> [ok "[]"]
  [e-ctor cons [H T]] -> (lpc.app "cons" [H T])
  [e-call F Args] -> (lpc.app (str F) Args)
  T -> [error [sl-lpc001 lpc-unsupported term T]])

(define lpc.app
  Name [] -> [ok (@s "[" Name "]")]
  Name Args ->
    (let R (lpc.terms Args "")
      (if (= (hd R) ok)
          [ok (@s "[" Name (hd (tl R)) "]")]
          R)))

(define lpc.terms
  [] Acc -> [ok Acc]
  [T | Ts] Acc ->
    (let R (lpc.term T)
      (if (= (hd R) ok)
          (lpc.terms Ts (@s Acc " " (hd (tl R))))
          R)))
