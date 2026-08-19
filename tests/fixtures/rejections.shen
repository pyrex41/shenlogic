\\ Every definition in this file is intentionally outside verified v1.
(define uses-float
  { number --> number }
  X -> (+ X 1.5))

(define uses-division
  { number --> number }
  X -> (/ X 2))

(define uses-hd
  { (list A) --> A }
  X -> (hd X))
