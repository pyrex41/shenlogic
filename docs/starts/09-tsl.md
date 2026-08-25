# PO9 TSL correspondence

**Obligation.** Under `defined-f(ā) <=> exists v. f$(ā,v)`, every tsl equation and definedness axiom holds in the least graph model.

**Notes.** Stated, not mechanized (`TSL-LOGIC.md`). Mutual definedness leastness is a comment. Graph `Value` (closed ADT) vs TSL free algebra of program ctors is a model mismatch.

**Code.** Goldens exist for factorial/map/tsl-*/d. `tests/golden/mutual.tsl.logic` is the compiler output of existing `examples/mutual.shen`, plus `mutual-tsl` in `tests/run-all.shen`. Same even/odd family as Leastness `mutual.graph.logic` and THF `mutual.thf`. Pin includes `; leastness of defined-even? is model-theoretic (mutual recursion)` and the same for `defined-odd?`. That is emission, not correspondence. No Lean Formula AST.

**Plan.** 1) Keep this golden. 2) Lean `ShenLogic.V2.TSL` Formula + `interp` only (no theorem). 3) Do not claim correspondence.
