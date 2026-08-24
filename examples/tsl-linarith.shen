\\ Linear-arithmetic canonicalization in the termination checker: steps
\\ and bounds are recognized in any linear spelling.  wobble's step is
\\ not of the form V + K, so it stays unknown (fail closed) -- correctly,
\\ since doubling diverges above the bound.

(define countdown
  { number --> number }
  X -> (countdown (- (+ X 1) 2)) where (> X 0)
  _ -> 0)

(define halveish
  { number --> number }
  X -> (halveish (- X (+ 1 1))) where (> X 0)
  _ -> 0)

(define countup
  { number --> number }
  X -> (countup (+ X 1)) where (< X 10)
  _ -> 1)

(define wobble
  { number --> number }
  X -> (wobble (* 2 X)) where (> X 0)
  _ -> 0)
