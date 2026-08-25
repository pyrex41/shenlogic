# PO12 Contracts

**Obligation.** CHC bad-state reachable iff the supported graph-safety law has a terminating counterexample. Z3 is not a compiler proof.

**Notes.** Lowering is `repair.law-*` string-append, not `chc.shen`. Z3 plumbing tested; the iff is not. No golden `law.smt2`.

**Code.** Existing law specs only. Query-shape pin not yet landed.

**Plan.** 1) Assert prepared query contains `|ShenLogic repair bad state|`, factorial premise, `(VInt …)`, `(not (= … (VInt 2)))`. 2) Three rejects: unsupported binder, existential, non-equation. 3) No Lean iff.
