# PO7 Definedness

**Obligation.** Deterministic eval ⇒ `G_f` functional, and `Defined_f(ā) <=> exists v. G_f(ā,v)`.

**Notes.** README `d`/`0=1` was prose only. Lean `defined_iff_graph` is `Iff.rfl` of a definition. Closest old fixtures (`loop`/`spin`/`diverge`) are bare self-calls and cannot yield `0=1`.

**Code.** This branch: `examples/d.shen` + `tests/golden/d.tsl.logic` + `d-tsl`. Honest pin: definedness axioms are tautologies (`defined-d N => defined-d N`). The theory still does not prove `~(defined-d N)`. Unguarded `((d N)=(+ 1 (d N)))` is correctly *not* emitted.

**Plan.** 1) Do not add a Lean `0=1` proof. 2) Next research question: what axiom shape would make `~(defined-d N)` a theorem without silently totalizing. 3) Mutual definedness leastness is still a comment.
