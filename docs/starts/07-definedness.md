# PO7 Definedness

**Obligation.** Deterministic eval ⇒ `G_f` functional, and `Defined_f(ā) <=> exists v. G_f(ā,v)`.

**Notes.** README `d`/`0=1` was prose only. Lean `defined_iff_graph` is `Iff.rfl`. `graph_functional` is Option injection on the abstract evaluator, not compiler `G_f`. Closest old fixtures (`loop`/`spin`/`diverge`) emit `(f X)=(f X)` and cannot yield `0=1`.

**Code.** This branch: `examples/d.shen` + `tests/golden/d.tsl.logic` + `d-tsl`. Compiler output (honest pin):

- intro and inversion: `(defined-d N) => (defined-d N)`
- minimality: any `P` with `(P N) => (P N)` contains `defined-d`
- equation: `(defined-d N) => ((d N) = (+ 1 (d N)))`

First-order intros are tautologies. Emptiness is not an emitted theorem. Unguarded `((d N)=(+ 1 (d N)))` is correctly *not* emitted: that totalizes `d` and lets LIA derive `0=1` as a theorem of `T(P)`.

**Shape (proposal, not a theorem).** An intro is unproductive when its definedness obligations include a self-call at the same arguments (no descent). Drop those intros instead of printing the tautology. Inversion of the remaining cases is then first-order:

- `d`: no intros; `(defined-d N) => false`, i.e. `(all N : number (~ (defined-d N)))`
- mixed `0 -> 1 | N -> (+ 1 (f N))`: intro `(defined-f 0)`; inversion `(defined-f X) => (X = 0)`

Keep every equation guarded. Do not add `(defined-d N)` as an axiom. Mutual definedness leastness stays a comment. This is an emitter change, not a Lean lemma.

**Plan.** 1) No Lean `0=1` or `~defined-d` proof. 2) Next code, if any: emit empty-case inversion for unproductive-only functions. 3) Do not treat `P := ⊥` on the tautological minimality, or LIA under the guarded equation, as a checked theorem.
