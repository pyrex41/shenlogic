# THORN integration and extension plan

THORN is Mark Tarver's automated theorem prover for first-order logic with
equality, distributed with the Shen standard library (`Lib/THORN`). It is
derived from Stickel's PTTP: props are compiled into Shen functions, and a
depth-bounded, timeout-bounded backward search is run over them. It is about
600 lines of Shen, consumes the same `prop` datatype that the `lpc` backend
already emits, and writes a readable natural-deduction-style proof to
`prf.txt`.

This document plans two things: using THORN as a Shen-native proof engine
inside ShenLogic, and extending THORN so that it can discharge the goals
ShenLogic actually produces.

## Why

- `shenlogic prove` is the only quantified-theorem path and it depends on
  Z3. THORN would give a prover that runs on every conforming Shen host
  with no external tool, matching the project's portability promise.
- Z3 answers `unsat`; THORN produces a proof object. That is the missing
  ingredient for the proof-carrying repair narrative in
  [RESEARCH-PLAN.md](RESEARCH-PLAN.md) and for a checkable certificate.
- The `lpc` renderer already produces the exact input THORN needs: a
  loadable list of props per function. The bridge is short.
- A second, independent prover gives a differential oracle over Z3
  verdicts, in the same spirit as the three-host suite and the System-S
  typing oracle.

## Fit and known gaps

| THORN property | Consequence for ShenLogic |
| --- | --- |
| Horn-clause model elimination, no induction | Induction must be instantiated outside THORN, as `prove` already does for Z3. |
| Equality by two-way rewriting, incomplete | Fine for the total, comparison-free `lpc` fragment; fail-closed on timeout. |
| Predicates compile to same-named Shen functions | `append` as a predicate would clobber the program under analysis. Needs renaming. |
| Depth 20, timeout 5 s, unbounded complexity by default | Search settings become prove flags and part of the recorded query. |
| Weak on stand-alone goals with no compiled KB | Axioms always go in through `kb->` first; the conjecture only through `<-kb`. |
| `attach` gives procedural attachment | A route to arithmetic guards later, outside any soundness claim. |
| Timeout is "liberal" per its own docs | Wall-clock enforced by the wrapper, as for Z3. |

## Phase 0: obtain and pin THORN (done)

THORN 20 from the S42 distribution is vendored under `third_party/thorn/`
with its BSD licence, recorded in `toolchain.lock`, and noted in
[CLEANROOM.md](../CLEANROOM.md). `make thorn-check` runs
`tests/thorn-smoke.shen` on the default host. Findings from getting it to
run on the 41.2 kernel under shen-go:

- **S42 library dependencies.** THORN 20 calls nine functions that live
  in the S42 standard library rather than the kernel: `mapf`, `newv`,
  `remove-duplicates`, `subset?`, `every?`, `sort`, `filter`,
  `remove-if`, `partition`. They are supplied verbatim in
  `third_party/thorn/prelude.shen`, inside `package thorn` so the
  prefixed references in the compiled prover resolve.
- **Kernel divergence on `<--` in datatype patterns.** The 41.2 Prolog
  compiler splits a generated clause at the first `<--` symbol, so the
  prop rule `[P <-- | Q] : prop` in `datatypes.shen` fails to load. The
  rule is reshaped as `[P C | Q]` with the side condition `if (= C <--)`
  placed before the premises. The condition must precede the premises;
  after them it is a datatype syntax error. The upstream grammar is
  itself permissive: it accepts `[[p a] foo [q a]]` as a prop with or
  without this rule, so the typed grammar is documentation, not a
  gate. The bridge in phase 1 runs with the type checker off.
- **Performance on shen-go.** Schubert's Steamroller proves in about
  5 million inferences and 15 seconds, against the 1 second claimed
  for Shen/Scheme. The default 5 second budget is too small on this
  host, so the smoke test sets 120 seconds. Ground `append` facts show
  the expected blow-up: 37, 738, and 74,521 inferences for lists of
  length 0, 1, and 2, and the length-3 fact times out at 5 seconds.
  This is the motivation for phase 3 item 2.
- **Proof output.** `<-kb` writes `prf.txt` into the current directory
  on this host (the `*home-directory*` value is empty), so `/prf.txt` is
  gitignored until phase 1 captures it explicitly.
- **Not yet run on shen-cl or shen-lua.** The prover compiles props to
  Prolog at run time, so those hosts are the likely next divergence.

## Phase 1: bridge, no changes to THORN

New file `shen/thorn.shen`, wired into `shenlogic prove` as
`--engine thorn` (Z3 stays the default).

1. **Namespace isolation.** Rewrite every predicate and function symbol in
   the emitted props to a prefixed form (`sl.append`) before `kb->`, and
   map back when reading the proof. Call `thorn.wipe-kb` before every
   query so arity clashes across runs cannot occur.
2. **Reuse the prove front end.** `prove.peel`, `prove.formula`,
   `prove.involved`, and `prove.check-fragment` already parse the
   conjecture, collect the involved functions, and reject non-total ones.
   Only `prove.emit` gets a second implementation that renders props via
   `lpc.prop` instead of SMT-LIB.
3. **Induction instance.** Take the list induction instance that
   `prove.induction` builds and hand its base and step cases to THORN as
   two separate `<-kb` goals, each with the inductive hypothesis added by
   `kb->`. Both must return `true` for `proved`.
4. **Fail closed.** `false`, timeout, or a host error all report
   `unproved`. Never treat `false` as a counterexample.
5. **Proof artifact.** Capture `prf.txt` into the output directory as
   `theory.thorn.prf`, with the symbol renaming undone.
6. **Tests.** Golden test in `tests/run-all.shen`: append associativity
   on `examples/tsl-lists.shen` proves under THORN, and the proof text is
   byte-stable across hosts. Negative test: a false conjecture such as
   `(append X Y) = (append Y X)` is reported unproved, not proved.

Exit: `./bin/shenlogic prove examples/tsl-lists.shen '<assoc>' --induct X
--engine thorn` prints `proved` with no Z3 installed.

## Phase 2: differential oracle

1. `shenlogic oracle --prover` runs every prove golden through both
   engines and reports agreement.
2. Any `proved` from THORN that Z3 does not confirm is a bug in one of
   them and blocks the suite; a THORN `unproved` where Z3 says `unsat` is
   logged as an incompleteness datum and feeds phase 3.
3. Start a small conjecture corpus under `tests/conjectures/`: append,
   reverse, length, map fusion, with expected verdicts per engine.

Exit: agreement table in the test output; incompleteness list written.

## Phase 3: extend THORN

Fork the vendored file into `shen/thorn-core.shen` from here. Each item is
independent and ordered by expected payoff for ShenLogic goals.

1. **Structural induction inside the prover.** A `thorn.induct` rule that,
   for a goal universally quantified over `(list T)`, generates base and
   step subgoals and adds the hypothesis to the knowledge base for the
   step. This moves phase 1 item 3 inside THORN and lets nested induction
   happen without ShenLogic orchestration. Later: induction over any
   datatype with the `lpc` constructor axioms.
2. **Directed rewriting for defining equations.** ShenLogic's equations
   are oriented: left side is a call on constructor patterns. Registering
   them as one-way rewrites, with two-way rewriting kept only for
   hypotheses, removes the main source of search blow-up in equational
   goals and is the single largest expected performance win.
3. **Definedness atoms.** Admit `defined-f` predicates as ordinary
   predicates so guarded equations of non-total functions can be loaded.
   This lifts the `lpc` total-only restriction and lets THORN prove
   `(~ (defined-d N))`-style facts the README advertises.
4. **Arithmetic through `attach`.** Map `<`, `<=`, `+`, and `-` on
   numeric terms to procedural attachment. Provable only on ground
   instances; document that this is evaluation, not deduction, and keep
   it out of the certificate.
5. **Iterative deepening with a per-goal budget.** Replace the single
   global depth and timeout with a budget schedule the wrapper controls,
   so the same query is reproducible across hosts of different speed.
6. **Proof output as data.** Return the proof as a Shen list alongside
   `prf.txt`, so ShenLogic can check it or render it into the certificate
   bundle rather than scraping a text file.

Each extension lands with a THORN-only unit test in
`tests/thorn/` and a re-run of the phase 2 agreement table.

## Phase 4: certificate and paper

1. Add `theory.thorn.prf` and the proof data to the `certify` bundle, and
   write a small independent checker for the proof data in Shen, so the
   trusted base is the checker rather than THORN's search.
2. Add obligation 15 to [PROOF-OBLIGATIONS.md](PROOF-OBLIGATIONS.md):
   THORN's compiled clause set is equivalent to the `lpc` props, and a
   checked proof entails the conjecture in every intended tsl model.
3. Report in the paper: fraction of the conjecture corpus each engine
   proves, proof sizes, and time per host.

## Risks

- **Licence and provenance.** THORN is third-party code. Keep it in its
  own directory with its own licence and treat the fork boundary as a
  documented event.
- **Host divergence.** THORN uses `eval`-style compilation of props into
  functions. shen-lua has already diverged from the other hosts once; a
  prover that compiles code at run time is a likely second case.
- **Search blow-up.** PTTP-style search is exponential. Phase 3 item 2 is
  the mitigation; until then, keep budgets small and the corpus modest.
- **Scope creep.** THORN is not meant to replace Z3 on arithmetic or on
  CHC queries. Its job is equational theorems over free datatypes, where
  it can also explain the proof.

## Order of work

Phase 0 is done. Phase 1 is a few days of effort and gives a
demonstrable Shen-only `prove`. Phase 2 is a day and is a precondition for
touching THORN's internals. Phase 3 items 1 and 2 are the ones worth doing
before any paper deadline; items 3 to 6 follow as the corpus demands.
