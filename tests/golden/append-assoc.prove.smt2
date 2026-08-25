; ShenLogic prove query v1
; unsat = the tsl theory entails the conjecture
(declare-sort A 0)
(declare-datatypes ((SLList 1)) ((par (T) ((slnil) (slcons (slhd T) (sltl (SLList T)))))))
(declare-fun append2 ((SLList A) (SLList A)) (SLList A))
(assert (forall ((Ys (SLList A))) (= (append2 (as slnil (SLList A)) Ys) Ys)))
(assert (forall ((X A) (Xs (SLList A)) (Ys (SLList A))) (= (append2 (slcons X Xs) Ys) (slcons X (append2 Xs Ys)))))
(assert (=> (and (forall ((Y (SLList A)) (Z (SLList A))) (= (append2 (append2 (as slnil (SLList A)) Y) Z) (append2 (as slnil (SLList A)) (append2 Y Z)))) (forall ((H0 A) (T0 (SLList A))) (=> (forall ((Y (SLList A)) (Z (SLList A))) (= (append2 (append2 T0 Y) Z) (append2 T0 (append2 Y Z)))) (forall ((Y (SLList A)) (Z (SLList A))) (= (append2 (append2 (slcons H0 T0) Y) Z) (append2 (slcons H0 T0) (append2 Y Z))))))) (forall ((X (SLList A)) (Y (SLList A)) (Z (SLList A))) (= (append2 (append2 X Y) Z) (append2 X (append2 Y Z))))))
(assert (not (forall ((X (SLList A)) (Y (SLList A)) (Z (SLList A))) (= (append2 (append2 X Y) Z) (append2 X (append2 Y Z))))))
(check-sat)
