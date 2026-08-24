\\ Higher-order function parameters: map/filter in the shen2logic style.

(define double
  { number --> number }
  X -> (* 2 X))

(define positive?
  { number --> boolean }
  X -> (> X 0))

(define map
  { (A --> B) --> (list A) --> (list B) }
  F [] -> []
  F [X | Y] -> [(F X) | (map F Y)])

(define filter
  { (A --> boolean) --> (list A) --> (list A) }
  F [] -> []
  F [X | Y] -> (if (F X) [X | (filter F Y)] (filter F Y)))

(define twice
  { (A --> A) --> A --> A }
  F X -> (F (F X)))
