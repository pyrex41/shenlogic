\\ Canonical linear forms over the exact integers.
\\
\\ (linarith.form E) normalizes a normalized-AST integer expression into
\\ [lin C Pairs]: the constant C plus Pairs = [[Var Coeff] ...] with zero
\\ coefficients removed and variables in first-occurrence order, or none
\\ when E is not (recognizably) linear.  Validity is the ring axioms of
\\ the integers, part of the declared linear-arithmetic background theory
\\ (docs/TSL-LOGIC.md).  Everything is pure list recursion in a fixed
\\ order, so results are identical on every Shen host.  Unrecognized
\\ forms return none: consumers fail closed.

(define linarith.form
  [e-var X] -> [lin 0 [[X 1]]]
  [e-value N] -> (if (integer? N) [lin N []] none)
  [e-prim + [A B]] -> (linarith.add2 (linarith.form A) (linarith.form B))
  [e-prim - [A B]] -> (linarith.add2 (linarith.form A)
                        (linarith.scale -1 (linarith.form B)))
  [e-prim * [A B]] -> (linarith.mul2 (linarith.form A) (linarith.form B))
  _ -> none)

(define linarith.add2
  none _ -> none
  _ none -> none
  [lin C1 P1] [lin C2 P2] ->
    [lin (+ C1 C2) (linarith.nonzero (linarith.merge P1 P2))])

(define linarith.merge
  P1 [] -> P1
  P1 [[V C] | Rest] -> (linarith.merge (linarith.add-pair P1 V C) Rest))

(define linarith.add-pair
  [] V C -> [[V C]]
  [[V C0] | Ps] V C -> [[V (+ C0 C)] | Ps]
  [P | Ps] V C -> [P | (linarith.add-pair Ps V C)])

(define linarith.nonzero
  [] -> []
  [[_ 0] | Ps] -> (linarith.nonzero Ps)
  [P | Ps] -> [P | (linarith.nonzero Ps)])

\\ Multiplication stays linear only when one operand is constant.
(define linarith.mul2
  none _ -> none
  _ none -> none
  [lin C []] F -> (linarith.scale C F)
  F [lin C []] -> (linarith.scale C F)
  _ _ -> none)

(define linarith.scale
  _ none -> none
  K [lin C Ps] -> [lin (* K C) (linarith.nonzero (linarith.scale-pairs K Ps))])

(define linarith.scale-pairs
  _ [] -> []
  K [[V C] | Ps] -> [[V (* K C)] | (linarith.scale-pairs K Ps)])

\\ The step a call argument takes relative to the head variable V:
\\ [step K] when E normalizes to exactly V + K, else none.
(define linarith.delta
  E V -> (linarith.delta-form (linarith.form E) V))

(define linarith.delta-form
  [lin K [[V 1]]] V -> [step K]
  _ _ -> none)

\\ Whether the comparison (Op A B) bounds V from below or above: the
\\ difference A - B is canonicalized, and a form of exactly V + c (or
\\ -V + c) turns each comparison operator into a lower or upper bound on
\\ V.  Any other shape is none.
(define linarith.compare-bound
  Op A B V ->
    (linarith.bound-kind Op
      (linarith.add2 (linarith.form A) (linarith.scale -1 (linarith.form B)))
      V))

(define linarith.bound-kind
  Op [lin _ [[V 1]]] V -> (linarith.kind-pos Op)
  Op [lin _ [[V -1]]] V -> (linarith.kind-neg Op)
  _ _ _ -> none)

(define linarith.kind-pos
  > -> lower
  >= -> lower
  < -> upper
  <= -> upper
  _ -> none)

(define linarith.kind-neg
  > -> upper
  >= -> upper
  < -> lower
  <= -> lower
  _ -> none)
