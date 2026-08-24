(define inc { number --> number } X -> (+ X 1))
(define pick { (number --> number) --> number --> number }
  F X -> 0 where (= F inc)
  F X -> (F X))
