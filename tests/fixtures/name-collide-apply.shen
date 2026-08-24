(define sl-apply-1 { symbol --> number --> number } S X -> 99)
(define inc { number --> number } X -> (+ X 1))
(define app { (number --> number) --> number --> number } F X -> (F X))
