(define part { number --> number --> number } X X -> 1)
(define h2 { (list number) --> (list number) --> number }
  [] _ -> 0
  [X | Xs] Xs -> (h2 Xs Xs))
