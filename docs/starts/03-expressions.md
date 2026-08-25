# PO3 Expressions

**Obligation.** Constants, variables, lists, strict calls, if, let, and, or agree with their relational rules.

**Notes.** Evaluator and `rules.expr` implement if/let/and/or/cons. Lean `Expr` is val/var/add/eq/ite/call only. Lean `ite` requires `.bool`; Shen treats non-`true` as else.

**Code.** None yet for this obligation (no Lean extend, no `v2-control.slir` golden).

**Plan.** 1) Extend Lean `Expr`/`eval` with let/and/or/cons using Shen's `= true` rule. No adequacy lemma. 2) Then golden `tests/golden/v2-control.slir`.
