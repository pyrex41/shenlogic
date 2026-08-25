# PO10 Projection

**Obligation.** Inverting a source-shaped edited tsl equation yields exactly the represented clause candidates.

**Notes.** Inversion is a heuristic: drops `~` and `defined-*`, power-sets leftover safe guards, restores `_` from original source. Not an exact inverse of `tsl.exclusion-formulas`.

**Code.** This branch: `repair-templates-*` sl-checks + `repair-alpha-binder-rename` on the four repair fixtures.

**Plan.** 1) Keep templates as a pin of current behavior, including that `~`/`defined-*` are dropped. 2) No Lean projection judgment. 3) Later: classify `~` as exclusion vs source guard.
