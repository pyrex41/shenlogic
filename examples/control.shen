(define abs
  { number --> number }
  X -> (if (< X 0) (- 0 X) X))

(define twice-fib
  { number --> number }
  N -> (let X (fib N) (+ X X)))

(define fib
  { number --> number }
  0 -> 0
  1 -> 1
  N -> (+ (fib (- N 1)) (fib (- N 2))))
