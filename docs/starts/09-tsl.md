# PO9 TSL correspondence

**Obligation.** Under `defined-f(ā) <=> exists v. f$(ā,v)`, every tsl equation and definedness axiom holds in the least graph model.

**Notes.** Stated, not mechanized (`TSL-LOGIC.md`). Mutual definedness leastness is a comment. Graph `Value` (closed ADT) vs TSL free algebra of program ctors is a model mismatch.

**Code.** Goldens exist for factorial/map/tsl-*. No `mutual.tsl.logic`. No Lean Formula AST.

**Plan.** 1) Pin `tests/golden/mutual.tsl.logic`. 2) Lean `ShenLogic.V2.TSL` Formula + `interp` only (no theorem). 3) Do not claim correspondence.
