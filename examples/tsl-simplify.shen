\\ Simplification showcase: each definition once produced a formula that
\\ was correct but not pleasant.  depth exercises constructor-disjoint
\\ exclusion pruning in the inversion axiom; pick2 exercises strict-let
\\ obligation absorption; both-branches exercises shared branch-obligation
\\ factoring; mixed exercises the empty-residue collapse.

(define depth
  { (list (list number)) --> number }
  [] -> 0
  [[] | R] -> (depth R)
  [[X | Y] | R] -> (+ 1 (depth [Y | R])))

(define spin
  { number --> number }
  X -> (spin X))

(define pick2
  { number --> number }
  X -> (let Z (spin X) (if (< X 0) Z 7)))

(define both-branches
  { number --> number }
  X -> (if (< X 0) (- 0 (spin X)) (+ 1 (spin X))))

(define mixed
  { number --> number }
  X -> (if (< X 0) (spin X) (+ (spin X) (pick2 X))))
