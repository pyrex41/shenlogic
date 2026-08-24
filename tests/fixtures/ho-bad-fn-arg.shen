(define map1
  { (A --> B) --> (list A) --> (list B) }
  F [] -> []
  F [X | Y] -> [(F X) | (map1 F Y)])

(define bad-call
  { (list number) --> (list number) }
  L -> (map1 unknown-fn L))
