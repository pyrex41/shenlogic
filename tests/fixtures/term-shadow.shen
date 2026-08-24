(define spin { number --> number }
  V -> (let V (+ V 2) (spin (- V 1))) where (> V 0)
  V -> 0)
(define grow { (list number) --> number }
  [] -> 0
  [X | Xs] -> (let Xs [X | Xs] (grow Xs)))
