(define even?
  { number --> boolean }
  0 -> true
  N -> (odd? (- N 1)))

(define odd?
  { number --> boolean }
  0 -> false
  N -> (even? (- N 1)))
