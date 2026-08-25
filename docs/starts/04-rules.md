# PO4 Rules

**Obligation.** Eval derives a graph rule; a finite least-rule derivation reconstructs eval. Spine of `P ⊢ ⇓ iff T(P) ⊨`.

**Notes.** Compiler emits 9-field open-term rules (`shen/rules.shen:534-584`). Lean `Rule` is 5-field ground plus `Premise.eval` the compiler never emits (`proof/ShenLogic.lean:260-266`). `derives_iff_lfpF` is generic over a given rule list, not `T(P)`. `certificate-instantiate` only replaces a whole term; that is enough for the toy `fact` replay, not compiled factorial.

**Code.** Ground witness in `tests/factorial-rule-witness.shen` against `tests/golden/factorial.slir`. `factorial_c0_p0` with `a0=0` derives 1. `factorial_c1_p1` chain 0→1→2→6→24→120 derives `(factorial 5)=120`. sl-checks `factorial-rule-c0-zero` / `factorial-rule-c1-five`. Walks compiled `value-eq` / `value-neq` / `call` / `i-sub` / `i-mul`. Not eval iff T(P). Not Lean `Derives`.

**Plan.** 1) Do not start a general Lean adequacy theorem (needs 1–3 first). 2) Do not treat `certificate-instantiate` as compiled-rule replay. 3) Factorial 0/5 is a witness, not a theorem.
