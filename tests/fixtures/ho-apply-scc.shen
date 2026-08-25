\\ Apply-induced SCC merge: unary id-app applies its parameter, so
\\ id-app and sl.apply-1 share an SCC. Unused arity-1 inc is in the
\\ apply dispatch but not in that component.

(define inc
  { number --> number }
  X -> (+ X 1))

(define id-app
  { (number --> number) --> number }
  F -> (F 0))
