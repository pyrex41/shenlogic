\\ Mutual recursion remains a single least fixed point component.

(define even-v2?
  { number --> boolean }
  0 -> true
  N -> (odd-v2? (- N 1)))

(define odd-v2?
  { number --> boolean }
  0 -> false
  N -> (even-v2? (- N 1)))

(define parity-v2
  { number --> symbol }
  N -> (if (even-v2? N) even odd))
