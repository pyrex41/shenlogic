# PO12 Contracts

**Obligation.** CHC bad-state reachable iff the supported graph-safety law has a terminating counterexample. Z3 is not a compiler proof.

**Notes.** Lowering is `repair.law-*` string-append, not `chc.shen`. Z3 plumbing tested; the iff is not. No golden `law.smt2`. Host dumps of both factorial law specs match the start-file fragment list. Do not claim the iff.

**Code.** First code on disk: yes. Query-shape + reject sl-checks on this branch.

**implemented.** Host dump of `shenlogic.repair-prepare-file` / `repair.law-query` for both factorial law specs, plus isolated `repair.law-open` / `repair.law-one` rejects. No lowering change.

**tested.** `repair-law-query-shape-true`, `repair-law-query-shape`, `repair-rejects-unsupported-law-binder`, `repair-rejects-existential-law`, `repair-rejects-law-not-equation`.

**proved.** None. Lean silent.

**next.** Keep Z3 as plumbing. No golden `law.smt2`. No Lean iff.

**Plan.** Pins landed from the host dump. Three rejects landed. No Lean iff.
