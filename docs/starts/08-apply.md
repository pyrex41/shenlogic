# PO8 Apply

**Obligation.** `sl.apply-N(s,x̄,r) <=> exists f. s='f ∧ f$(x̄,r)`; apply-induced SCC coarsening preserves LFP.

**Notes.** Implemented on `v2-map`. Lean has no apply. `v2-map` SCCs do not merge.

**Code.** None yet for the merge case.

**Plan.** 1) Add `tests/fixtures/ho-apply-scc.shen`: unused arity-1 `inc`; unary `id-app` that applies its parameter so `id-app` and `sl.apply-1` share an SCC. 2) Eval + CHC query of named/junk apply. 3) No Lean theorem.
