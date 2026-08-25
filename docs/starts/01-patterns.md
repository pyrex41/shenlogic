# PO1 Patterns

**Obligation.** Matching succeeds iff the translated pattern proposition holds, including repeated vars and ctor injectivity/disjointness.

**Notes.** Shen matcher treats repeated vars as equality. Lean `pattern_equivalence` is `Iff.rfl`. Fixture `repeated-pattern.shen` was unused (live twin `examples/lists.shen`).

**Code.** `ceb2e5b` emits `[value-eq Old V]` on already-bound success in `rules.match-pattern`. Golden `tests/golden/lists.graph.logic`. Honest pin: `same-pair?` prints `value-eq M1 M1` because `make-fields` reuses `C` on nested cons. Pre-existing. Leave it.

**Plan.** 1) Do not clean `make-fields` unless asked. 2) No Lean adequacy until Lean's pattern proposition *is* the compiled Rule IR. 3) Optional later: wire or delete unused `repeated-pattern.shen`.
