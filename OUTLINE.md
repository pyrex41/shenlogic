# ShenLogic research outline

24 Aug 2026. Working copy: `~/projects/shenlogic` (Pyrex41/shenlogic, clean clone).
Gold sources already in-tree: `tarver_files/logic.shen`, `tarver_files/assoc-append.prf`.

This is a work plan, not a paper claim. The compiler-to-logic story is Tarver/Thompson completed as engineering. The publishable thesis is **projectable, partiality-aware repair**. The compiler still has to earn one gold test: replay Mark's assoc-append proof from generated TSL.

## Two theses (do not mix the paper)

1. **Compiler adequacy.** `P ⊢ f(ā) ⇓ v  iff  T(P) ⊨ f$(ā,v)`, plus tsl/definedness correspondence. Target theorem, not a current claim. Lean has matcher/evaluator/ordered-clause determinism and a generic least-closure lemma. Thirteen obligations in `docs/PROOF-OBLIGATIONS.md`.
2. **Repair.** A generated theory is an editable semantic view. A projectable equation edit yields a bounded source patch accepted only when the forward compiler reproduces the edit and contracts pass. Not a general inverse for arbitrary axioms.

Week-1 work is characterization, not MiniZinc/SyGuS/LLMs.

## Rooms and owners

| Room | Owners | Scope |
| --- | --- | --- |
| SL Compiler | Shen, Patterns, Clauses, Expressions, Rules | Obligations 1–4 |
| SL Models | Leastness, THF, Definedness, Apply, TSL | Obligations 5–9 |
| SL Repair | Projection, RoundTrip, Contracts, Search, Benchmark | Obligations 10–13 + benchmark |
| SL Gold | Shen, AssocAppend, TSL | Replay `assoc-append.prf` against `T(append)` |

## Workstreams

Each stream's first deliverable is the same shape: **implemented / tested / proved / next step**, with file refs. No invented theorems or recovery rates.

### Compiler (obligations 1–4)

1. **Patterns.** Matching iff translated pattern proposition, including repeated vars and constructor injectivity/disjointness. Files: `shen/evaluator.shen`, `tests/fixtures/repeated-pattern.shen`, `examples/v2-constructors.shen`, Lean matcher.
2. **Clauses.** First applicable clause under total guards; guard error/nontermination is not classical false. Files: ordered-clause evaluator, `tests/fixtures/guard-fallback.shen`, `examples/ordered.shen`.
3. **Expressions.** Constants, variables, lists, strict calls, `if`, `let`, `and`, `or` agree with relational rules. Files: `shen/evaluator.shen` vs graph/Rule IR.
4. **Rules.** Eval→graph and finite derivation→eval. Files: SLIR (`docs/IR.md`), `shen/` lowering. This is the spine of the intended adequacy theorem.

### Models (obligations 5–9)

5. **Leastness.** SCC operators monotone; simultaneous least fixed point. Files: `examples/v2-mutual.shen`, Lean least-closure.
6. **THF.** Full-model quantification, no finite-sample "proof". Files: `shen/thf.shen`, TPTP4X gate, name-collision rejection.
7. **Definedness.** `G_f` functional; `Defined_f(ā) <=> exists v. G_f(ā,v)`. Files: `shen/termination.shen`, `shen/tsl.shen`. The `d`/`0=1` poison case is the demo, not factorial.
8. **Apply.** `sl.apply-N` defunctionalization adequacy. Files: `examples/v2-map.shen`, `tests/fixtures/ho-*.shen`.
9. **TSL.** Every emitted equation and definedness axiom holds in the least graph model. Files: `docs/TSL-LOGIC.md`, `shen/tsl.shen`, `tests/golden/*.tsl.logic`.

### Repair (obligations 10–13)

10. **Projection.** Invert a source-shaped edited tsl equation to exactly the clause candidates. Files: `shen/repair.shen`, `docs/REPAIR.md`.
11. **Round-trip.** Accepted patch retranslates to the edited view; splice re-parses. Write barrier stays fail-closed.
12. **Contracts.** CHC bad-state reachable iff a terminating counterexample of the law. Z3 is a decision point, not a proof of the compiler.
13. **Search.** Bounded Prolog covers the declared guard-choice space; ranking is the advertised minimum among survivors. MiniZinc/SyGuS are later backends, not this week's work.

### Extras (the work the README underweights)

14. **Assoc-append replay.** Translate `append`/`append2`, ask whether steps 0–53 of `assoc-append.prf` are theorems of `T(append)` plus Mark's `list-ind` / `=r` / quantifier rules. If the answer is "we only emit the axioms", that is the compiler gap. Do not claim a replay until one exists.
15. **Benchmark inventory.** Count and classify current `tests/fixtures` + `tests/golden` against the RESEARCH-PLAN 30–100 bar (mutation / human edit / history; unique / ambiguous / impossible / out-of-grammar). Publish classifications, not only patches.

## This week (phase 1)

Freeze and characterize. Do not start a Lean adequacy proof until the inventory is honest.

- [x] One page per obligation: implemented / tested / proved / next step (in this file)
- [x] Assoc-append: TSL can state the axioms; cannot replay. `system-S` has no counterpart. SMT sketch unused.
- [x] Benchmark: 41 fixtures / 20 goldens / 4 recoveries / 0 published tasks / 0 class labels
- [x] Benchmark tasks.tsv: 9 existing run-all/repair-cli scenarios, origin=neither, 0 class labels
- [ ] Keep `docs/RESEARCH-PLAN.md` claims that are still true; flag any that the clone does not support
- [ ] No MiniZinc, no SyGuS, no LLM-as-repair-engine paper

## Next (phase 2–3), only after the inventory

- Formal repair judgment (editable projection, alpha, consistency, non-interference)
- Lean: patterns → nonrecursive expressions → ordered clauses → direct recursion → mutual/leastness (as `PROOF-OBLIGATIONS.md` already orders 1–7)
- Public benchmark with expected *classifications*
- Flagship demo that is not factorial (ordered + recursive + partial + ambiguous)

## Out of scope until the above exists

MiniZinc / SyGuS / SemGuS search bake-off. Trusted neural repair. Interactive version-space UI. Definedness-domain editing. Whole-program / mutual repair. Effects, lambdas, polymorphic user ADTs.

## Success for this pass

Reuben has a single outline in this file, 15 named owners, and a first audit of the clone that says what is actually on disk. The next commit-sized task per stream is named. Assoc-append is either a scheduled replay or a listed missing lemma, not a vibe.

## Audit findings (24 Aug 2026, first pass)

First pass closed. Next work is the named commit-sized tasks below, not more inventory.

### Gold (14)

Cannot replay `assoc-append.prf`. TSL emits Mark's two intro axioms (as `append2` / `()`) plus list inj/disjoint/acyclicity/2nd-order induction. No sequent or ND checker. `system-S` has no counterpart. `examples/append-assoc.smt2` is a hand-written Z3 sketch, not in Makefile/CI. Next: record the axiom diff and the three `system-S` typing goals. Do not write a checker yet.

### Compiler

**1 Patterns.** Shen matcher treats repeated vars as equality. Rule IR success path for an already-bound var does **not** emit `value-eq` (only `value-neq` on failure). Lean `pattern_equivalence` is `Iff.rfl` of its own `PatternHolds`. Fixture `repeated-pattern.shen` is unused. Next: put `[value-eq Old V]` on the success state and golden `lists.graph.logic` for `same-pair?`. No Lean adequacy.

**2 Clauses.** Evaluator and Lean `choose` block on guard error/timeout. Lean `firstApplicable` treats guard `none` as skip (classical false). They disagree unless guards are total. Fixture `guard-fallback.shen` is unused. Next: Lean `choose_guard_none` plus `choose = firstApplicable` under a totality hypothesis; wire the dead fixture and `(sign 1)`.

**3 Expressions.** Evaluator and `rules.expr` implement if/let/and/or/cons. Lean `Expr` is val/var/add/eq/ite/call only. `ite` requires `.bool`; Shen treats non-`true` as else. Next: extend Lean `Expr`/`eval` with let/and/or/cons using Shen's `= true` rule. No adequacy lemma.

**4 Rules.** Spine of the intended theorem. Compiler emits 9-field open-term rules; Lean `Rule` is ground values plus `Premise.eval` the compiler never emits. `derives_iff_lfpF` is generic over a given rule list, not `T(P)`. Next: ground witness that `factorial 0` and `factorial 5` instantiate compiled rules. No general Lean theorem.

### Models

**5 Leastness.** Compiler SCCs + `(least-scc …)` exist; `mutual.graph.logic` pins odd?/even?. Lean `lfp_monotone` is the identity; `scc_lfp_adequate` is an alias of `lfp_least` with no SCC. Next (this week): `v2-mutual.graph.logic`. Later: `LFPOn` restricted to a name set. No compiler-SCC theorem.

**6 THF.** Full-model emitter exists; TPTP4X is factorial syntax only. No simultaneous-SCC THF golden. Next: `tests/golden/mutual.thf`.

**7 Definedness.** README `d`/`0=1` poison case is **not in-tree**. Closest fixtures (`loop`/`spin`/`diverge`) are bare self-calls; unguarded they emit `(f X)=(f X)`, which does not yield `0=1`. Lean `defined_iff_graph` is `Iff.rfl` of a definition. Next: `examples/d.shen` + golden `d.tsl.logic` (guarded, no unguarded `d` equation).

**8 Apply.** `sl.apply-N` compiled and tested on `v2-map`. Lean has no apply. `v2-map` SCCs do not merge. Next: `ho-apply-scc.shen` fixture that actually shares an SCC.

**9 TSL.** Correspondence "stated, not mechanized." Mutual definedness leastness is a comment, not an axiom. Graph `Value` vs TSL free algebra mismatch. Next: Lean TSL Formula AST + `interp` only (no theorem); pin `mutual.tsl.logic`.

### Repair

**10 Projection.** Inversion is a heuristic: drops `~` and `defined-*`, takes a power set of leftover safe guards, restores `_` from the original source. Not an exact inverse of TSL exclusion emission. No template goldens. Next: pin `repair.templates` output on the four `repair-*.tsl.logic` files plus one alpha-only pair.

**11 Round-trip.** Runtime preamble / retranslate / splice-reread / write barrier exist. No test translates the spliced file. Next: one regression that `translate(splice) = edited view`.

**12 Contracts.** Law→bad-state is a second string compiler in `repair.law-*`, not `chc.shen`. Z3 plumbing tested; the iff is not. Next: pin query shape for both factorial law specs + three unsupported-fragment rejects.

**13 Search.** Prolog enumerator + tree-cost rank exist. MiniZinc/SyGuS are **docs only** (zero `.mzn`). No isolated cartesian/truncation/tie-break tests. Next: three `sl-check`s on hand-built pools (full 2×2 product; `Limit=2` drops `none`; equal-cost ordered by canonical text). No Lean, no MiniZinc.

### Benchmark (15)

Implemented: `tests/benchmark/tasks.tsv` (9 rows). One row per existing `run-all` / `repair-cli` `(source, logic, spec)` triple. `origin=neither` on all. `class` empty. `inversion=yes` only on the four template pins (factorial, ordered, declared, wildcard). The other five are reject/prepare specs already in the suite, not new programs. `make benchmark-inventory` / `tests/benchmark/inventory.awk` prints counts.

Tested: inventory target. First-pass file counts unchanged (41 fixtures / 20 goldens / 4 positive recoveries). Published tasks: **9**. Class labels: **0**. Distance to 30 is 21. Do not treat 9 as 9 recoveries, and do not treat 41 files as 41 tasks.

Proved: no. RESEARCH-PLAN 30-100 bar is unpublished. No unique/ambiguous/impossible/out-of-grammar labels.

Next: do not invent programs. Mutation / human / history labels wait for actual provenance. Class labels wait for a uniqueness, ambiguity, or impossibility witness.
