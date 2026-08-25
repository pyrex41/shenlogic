\\ Total list functions renderable in LPC prop syntax (--format lpc).

(define append2
  { (list A) --> (list A) --> (list A) }
  [] Ys -> Ys
  [X | Xs] Ys -> (cons X (append2 Xs Ys)))

(define rev2
  { (list A) --> (list A) }
  [] -> []
  [X | Xs] -> (append2 (rev2 Xs) (cons X ())))
