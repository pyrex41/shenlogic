# 14 Assoc-append gold test

**Obligation.** Replay Mark's 54-step `assoc-append.prf` against generated TSL for append. Compiler-half acceptance test.

**Notes.** No replay. T(append2) states the goal and holds Mark's two `intro append` axioms under spelling `append`/`[]`/`[list A]` vs `append2`/`()`/`(list A)` (binders X then X/Y/Z vs Ys then X/Xs/Ys). Instantiating the emitted 2nd-order list-ind axiom is not his sequent tactic. Extra emit: inj/disjoint/acyclic (his unused `nil` / `list-identity` / `list-acyclic`) and `defined-first` (not in Mark). `system-S` has no TSL counterpart.

**Code.** Pinned emit is `tests/golden/tsl-lists.tsl.logic` from `examples/tsl-lists.shen` (`append2`; no `append` source). No `append.tsl.logic`. `examples/append-assoc.smt2` is a hand-written Z3 sketch, not in Makefile/CI. Three `system-S` typing goals: `[[append y z] : [list t]]` (step 11), `[[append y w] : [list t]]` (33), `[[append w z] : [list t]]` (45).

**Plan.** 1) Keep this characterization. 2) Do not write a `.prf` replay engine. 3) Gold test moves only if a fresh `translate --format tsl` differs from the golden, or a real replay exists.
