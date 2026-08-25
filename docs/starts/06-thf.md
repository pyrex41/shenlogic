# PO6 THF

**Obligation.** Typed decls, ctor axioms, and simultaneous SCC leastness quantify over the complete candidate model. No finite sample is a proof.

**Notes.** Emitter is full-model. TPTP4X is factorial syntax only. Lean encoding lemmas only. `map.thf` is singleton SCCs and does not pin simultaneous leastness.

**Code.** This branch: `tests/golden/mutual.thf` + `mutual-thf` sl-check on existing `examples/mutual.shen` (same even/odd family as PO5 `mutual.graph.logic`). Compiler output includes `thf(sl_least_odd_q_even_q,...)` quantifying over both `R_odd_q` and `R_even_q`. That is emission, not a proof that the text is the LFP.

**Plan.** 1) Leave TPTP4X-on-mutual optional. 2) No Lean proof of PO6. 3) Do not invent a second mutual program.
