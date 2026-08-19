(define first
  { (list A) --> A }
  [X | _] -> X)

(define same-pair?
  { (list A) --> boolean }
  [X X] -> true
  _ -> false)
