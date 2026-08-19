\\ Free constructors are established by constructor-headed patterns.
\\ Constructor names are injective, disjoint, and arity-sensitive.

(define constructor-tag
  { A --> symbol }
  (node X) -> node
  (pair X Y) -> pair
  (bundle X Y) -> bundle
  (unit) -> unit-constructor
  unit -> unit-symbol
  _ -> other)

\\ Overlapping constructor patterns are ordered: the specific clause wins.
(define constructor-overlap
  { A --> symbol }
  (node 0) -> zero
  (node X) -> node
  _ -> other)

\\ A constructor may contain arithmetic and nested constructors in an
\\ expression; this is not a function call to `box` or `pair`.
(define mixed-constructor
  { number --> A }
  X -> (bundle (+ X 1) (pair X (node (- X 1)))))

(define wrap-constructor
  { A --> A }
  X -> (box X))

(define unwrap-constructor
  { A --> A }
  (box X) -> X)

\\ Constructor and literal namespaces do not collide.
(define constructor-collision
  { A --> symbol }
  (same X) -> constructor
  same -> symbol
  "same" -> string
  _ -> other)

(define constructor-string-probe
  { --> A }
  -> "same")
