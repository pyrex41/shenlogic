; Associativity of append from ShenLogic tsl axioms for append2
; (examples/tsl-lists.shen: proven total, so equations are unguarded).
; The induction SCHEMA is second-order; here it is instantiated by hand
; with P(X) := forall Y,Z. app(app(X,Y),Z) = app(X,app(Y,Z)) -- the same
; instantiation Tarver's list-ind step makes -- and Z3 discharges the
; base case, the step case, and the final application automatically.
(declare-sort E 0)
(declare-datatypes ((L 0)) (((nil) (cons (hd E) (tl L)))))
(declare-fun app (L L) L)
; tsl equations for append2
(assert (forall ((Y L)) (= (app nil Y) Y)))
(assert (forall ((X E) (Xs L) (Y L)) (= (app (cons X Xs) Y) (cons X (app Xs Y)))))
; instantiated induction axiom for P
(assert (=> (and (forall ((Y L) (Z L)) (= (app (app nil Y) Z) (app nil (app Y Z))))
                 (forall ((H E) (T L))
                   (=> (forall ((Y L) (Z L)) (= (app (app T Y) Z) (app T (app Y Z))))
                       (forall ((Y L) (Z L)) (= (app (app (cons H T) Y) Z) (app (cons H T) (app Y Z)))))))
            (forall ((X L) (Y L) (Z L) ) (= (app (app X Y) Z) (app X (app Y Z))))))
; negated goal
(assert (not (forall ((X L) (Y L) (Z L)) (= (app (app X Y) Z) (app X (app Y Z))))))
(check-sat)
