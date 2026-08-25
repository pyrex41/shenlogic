# PO13 Search and ranking

**Obligation.** Bounded Prolog covers the declared guard-choice space; tree-cost + canonical tie-break picks the advertised minimum.

**Notes.** MiniZinc/SyGuS are docs only (zero `.mzn`). No isolated cartesian/truncation tests before this branch.

**Code.** This branch: `repair-enum-2x2-product`, `repair-enum-limit-drops-none`, `repair-rank-equal-cost-canonical`.

**Plan.** 1) Keep MiniZinc out. 2) No Lean optimality theorem. 3) Later: distinguish bound-exhaustion from unrealizability.
