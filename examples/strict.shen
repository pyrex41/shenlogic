(define strict-probe
  { number --> number }
  X -> (let Y (+ X 1) (+ Y Y)))
