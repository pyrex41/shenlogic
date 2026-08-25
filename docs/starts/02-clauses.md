# PO2 Clauses

**Obligation.** Under total guards, the selected clause is the first applicable. Guard error/nontermination is not classical false.

**Notes.** Evaluator blocks on guard error (`evaluator-clauses` returns `Q`). Lean `firstApplicable` skips `guardPass = none`. They disagree unless guards are total. `lem` / `exp` at `logic.shen:232,238` stay out of the translation.

**Code.** `44a0dc9` pins `tests/golden/guards.graph.logic` and the `guards-graph` sl-check. Deleted unused `tests/fixtures/guard-fallback.shen`. Honest pin for `sign`: three rules, no fourth stuck path.

- c0: `int-test <` → negative
- c1: `int-test >=` (`rules.compare-negate` of `<` at `shen/rules.shen:493-497`) and `value-eq 0` → zero
- c2: `int-test >=` and `value-neq 0` → positive

`value-eq sign_a0 (v-int i-var)` on every path is `ensure-int`, not a totality proof. Guard-false is `int-test >=`, not `lem`. No `falsum`. This is a regression pin of current output, not `choose = firstApplicable`.

**Plan.** 1) Leave `firstApplicable` alone until it agrees with `choose` on stuck guards. 2) Do not rewrite `compare-negate` into a classical split. 3) No Shen↔Lean theorem yet.
