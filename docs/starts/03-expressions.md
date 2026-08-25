# PO3 Expressions

**Obligation.** Constants, variables, lists, strict calls, if, let, and, or agree with their relational rules.

**Notes.** Evaluator and `rules.expr` implement if/let/and/or/cons (`shen/evaluator.shen:55-162`, `shen/rules.shen:304-338`). Lean theorems `eval_deterministic` / `expr_path_*` / `bigStep_iff_eval` / `control_*` are aliases of `eval`, not PO3.

**Code.** `d363098` extends Lean `Expr`/`eval` with `letE` / `andE` / `orE` / `cons` in `proof/ShenLogic.lean`. `ite` / `andE` / `orE` use Shen's `= true` (any other *value* is else / false / rhs; `none` stays stuck). `letE` shadows on the front of `ρ`. `cons` is strict L-to-R: a `.list` tail becomes `.list (h :: xs)`; any other tail is `.ctor "cons" [h, t]`. That last clause is a model of improper cons, not a T(P) axiom and not Lean `Value.list` injectivity. `eval_deterministic` is still `some`-injectivity. No adequacy lemma. No `v2-control.slir` / `control.graph.logic` golden.

**Plan.** 1) Golden `tests/golden/v2-control.slir` next. 2) No `evaluator-expr` ↔ `rules.expr` theorem. 3) Factorial 0/5 compiled-rule witness is PO4.
