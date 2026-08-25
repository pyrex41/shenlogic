# PO8 Apply

**Obligation.** `sl.apply-N(s,x̄,r) <=> exists f. s='f ∧ f$(x̄,r)`; apply-induced SCC coarsening preserves LFP.

**Notes.** Implemented on `v2-map` (singleton `sl.apply-1` SCC; no merge). Lean has no apply. This fixture is the merge case. That is emission, not a proof the LFP is preserved.

**Code.** This branch: `tests/fixtures/ho-apply-scc.shen` + `tests/golden/ho-apply-scc.graph.logic` + `ho-apply-scc-{graph,eval-named,eval-junk,query-named,query-junk}` sl-checks. Compiler output includes `(least-scc (sl.apply-1 id-app))`; unused `inc` stays `(least-scc (inc))`. Named apply evals `(id-app inc)` to 1; junk number is `[error apply-non-function]`. CHC query generation succeeds for named `inc` and junk `junk`. No solver run is a proof.

**Plan.** 1) No Lean apply or SCC-coarsening theorem. 2) Do not treat CHC query emission as adequacy. 3) Leave `v2-map` goldens as the non-merge case.
