\\ Unsupported effects and partial primitives must be rejected explicitly.
(define uses-division-v2
  { number --> number }
  X -> (/ X 2))

(define uses-float-v2
  { number --> number }
  X -> (+ X 1.5))
