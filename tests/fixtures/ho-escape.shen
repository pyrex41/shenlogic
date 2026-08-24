(define leak-fn
  { (A --> B) --> (list A) --> A }
  F X -> (+ F 1))
