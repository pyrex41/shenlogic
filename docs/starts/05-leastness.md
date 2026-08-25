# PO5 Leastness

**Obligation.** SCC operators monotone; closure + containment in every closed candidate is the simultaneous LFP.

**Notes.** Lean `lfp_monotone` is the identity. `scc_lfp_adequate` is an alias of `lfp_least` with no SCC. TSL mutual leastness is a comment, not an axiom.

**Code.** This branch: `tests/golden/v2-mutual.graph.logic` + `v2-mutual-graph` sl-check. Existing `mutual.graph.logic` already pins odd?/even?.

**Plan.** 1) Leave Lean `LFPOn` for later. 2) Do not formalize `rules.sccs` this week. 3) Share fixtures with PO6 THF (`mutual.thf`).
