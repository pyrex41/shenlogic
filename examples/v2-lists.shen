\\ Proper, improper, and nested list patterns.

(define list-shape
  { A --> symbol }
  [] -> empty
  [X] -> singleton
  [X Y] -> pair
  [X | T] -> improper
  _ -> other)

(define nested-list-shape
  { A --> symbol }
  [[X Y] | T] -> nested-pair
  [[X | T] | _] -> nested-improper
  _ -> other)

(define same-nested
  { A --> boolean }
  [[X X]] -> true
  _ -> false)
