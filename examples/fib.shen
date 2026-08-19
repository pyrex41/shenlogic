(define fib
  { number --> number }
  0 -> 0
  1 -> 1
  N -> (+ (fib (- N 1)) (fib (- N 2))))
