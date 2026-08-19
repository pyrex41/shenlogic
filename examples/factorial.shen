\\ Factorial exactly as in the motivating Shen2Logic discussion.
(define factorial
  { number --> number }
  0 -> 1
  X -> (* X (factorial (- X 1))))
