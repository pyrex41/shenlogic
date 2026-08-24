\\ Polymorphic list functions for the tsl typed equational output.

(define append2
  { (list A) --> (list A) --> (list A) }
  [] Ys -> Ys
  [X | Xs] Ys -> (cons X (append2 Xs Ys)))

(define first
  { (list A) --> A }
  [X | _] -> X)
