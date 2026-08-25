# PO4 Rules

**Obligation.** Eval derives a graph rule; a finite least-rule derivation reconstructs eval. Spine of `P ⊢ ⇓ iff T(P) ⊨`.

**Notes.** Compiler emits 9-field open-term rules. Lean `Rule` is ground values plus `Premise.eval` the compiler never emits. `derives_iff_lfpF` is generic over a given rule list, not `T(P)`.

**Code.** None yet.

**Plan.** 1) Ground witness: `factorial 0` and `factorial 5` instantiate compiled rules. 2) Do not start a general Lean adequacy theorem (needs 1–3 first).
