# PO2 Clauses

**Obligation.** Under total guards, the selected clause is the first applicable. Guard error/nontermination is not classical false.

**Notes.** Evaluator blocks on guard error. Lean `firstApplicable` skips `guardPass = none` (classical false). They disagree unless guards are total. `guard-fallback.shen` deleted as unused twin of `examples/guards.shen`.

**Code.** This branch: `tests/golden/guards.graph.logic` + `guards-graph` sl-check.

**Plan.** 1) Keep `firstApplicable` alone this week. 2) Later Lean: `choose_guard_none` and `choose = firstApplicable` under a totality hypothesis. 3) No Shen↔Lean theorem yet.
