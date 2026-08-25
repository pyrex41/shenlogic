\\ ShenLogic axioms in LPC prop syntax.
\\ Adapter for the LPC prover's intro rule:
\\   (define axioms S -> (shenlogic-axioms S))

(define shenlogic-axioms
  append2 -> [
    [all A : type [all Ys : [list A] [[append2 [] Ys] = Ys]]]
    [all A : type [all X : A [all Xs : [list A] [all Ys : [list A] [[append2 [cons X Xs] Ys] = [cons X [append2 Xs Ys]]]]]]]
  ]
  rev2 -> [
    [all A : type [[rev2 []] = []]]
    [all A : type [all X : A [all Xs : [list A] [[rev2 [cons X Xs]] = [append2 [rev2 Xs] [cons X []]]]]]]
  ]
)
