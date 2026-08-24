\\ Regression corpus for the tsl soundness fixes found by adversarial
\\ review: prior-clause variable capture in exclusions, strict-let
\\ definedness obligations, and type/term namespace separation.

(define exl
  { (list number) --> number --> number }
  (cons E0 R) Y -> 1 where (> E0 Y)
  L E0 -> 2)

(define loop
  { number --> number }
  X -> (loop X))

(define drops
  { number --> number }
  X -> (let Z (loop X) 5))

(define pick
  { number --> number }
  X -> (let Z (loop X) (if (< X 0) Z 7)))

(define wv
  { W0 --> number }
  _ -> 7)

(define sh
  { A --> number }
  A -> 7)
