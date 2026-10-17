# Integration contracts

## Source and binary producers

The PHP producer emits normalized ASTs, function entries, control-flow edges,
call sites, reads/writes, def-use may edges, containment, and explicit unknowns.
Directory extraction retains a manifest and file-local source digests. It is a
structural analysis, not a complete PHP interpreter: dynamic dispatch, includes,
exceptions, aliasing and loops require additional contracts or remain obligations.
Matching a domain API name supplies a named assumption; it does not prove its body.

Ghidra fits at the same fact boundary. Run its actual headless analyzer:

```sh
mkdir -p build/ghidra
"$GHIDRA_HOME/support/analyzeHeadless" build/ghidra project \
  -import /absolute/path/to/binary \
  -scriptPath "$PWD/extractors" \
  -postScript BehaviorFacts.java "$PWD/build/native.json" -deleteProject
node bin/behavior.mjs import-ghidra build/native.json
node bin/behavior.mjs analyse build/native.json
```

`BehaviorFacts.java` exports executable SHA-256, function entries, instructions,
control flow, calls, raw P-code, high P-code/SSA def-use links, and unknown memory
or call effects. P-code references have corresponding nodes. The importer checks
the fact envelope. A binary behavior manifest must bind the exact executable and
entry and enumerate assumptions. `reconstruct-binary` keeps these conditional.
There is no general x86-to-behavior equivalence proof and no inference of full
machine state from a program counter.

## Soufflé and GraphWalker

`analysis/code.dl` computes finite may-reachability, containment, may-call,
may-write and unresolved-site closures. TSV projection rejects unsafe cells.
Missing tools and subprocess failure are explicit outcomes. Closure is a targeting
and inventory aid: absence of a may fact is never used to discharge a semantic
premise.

`explore` evaluates a certificate through Shen on an explicit finite input set,
with state, edge, fuel and depth bounds. The export records those bounds and whether
exploration was truncated. It contains concrete states, inputs and expected states.
`graphwalker` runs the real CLI/JAR and returns proposed edge IDs. `validate-path`
checks connectivity, content identities and every transition through Shen. Local
`walk` is a seeded alternative planner; neither planner issues proof certificates.

## Implementations and observations

`run` accepts a JSON object with `adapter` and `steps`, and an optional evidence DB
path. Each step has an `input`; fixture steps can also inject a `fault`.

- `sqlite-transfer`: an independently implemented transactional transfer, receipt
  and outbox fixture. `legacy: true` disables deduplication. Actual SQLite, durable
  receipts and lost-response/retry behavior are exercised by tests.
- `http`: configured endpoint and declarative observation map. Preserve raw body,
  status and operational failures. Timeouts imply unknown commit; an HTTP status
  alone does not prove noncommit. Map versions and completeness assumptions travel
  with evidence.
- `command`: executable plus argument array, JSON stdin/stdout, explicit timeout
  and output limits. No shell interpolation. This is a locally trusted adapter.
- `postgres` / `mysql`: real driver bindings, configured parameterized statements,
  explicit transaction boundaries, and observation queries. Configuration specifies
  column maps and whether ordered effects are complete. Commit transport failure
  remains unknown. Templates and mappings are trusted local configuration.

SQL configurations use `version: 1`, `kind`, `connection`, and
`commands: {name: [{sql, parameters: [inputField]}]}`. Observation configuration
contains `assumption`, `storeQuery`, `effectsQuery`, `keyColumn`, `valueColumn`,
`topicColumn`, `effectColumn`, and `complete`. Ordered effect queries must use an
explicit stable order. Optional `integerStrings` converts driver-returned numeric
strings with checked range validation. SQL driver tests use injected drivers;
a live PostgreSQL/MySQL deployment has not been validated here.

Evidence admission preserves raw records. Scenario execution acquires a lease,
records intent before invocation, and appends observations to a hash-linked journal.
Artifacts and dependencies are content addressed and checked on read. These are
integrity mechanisms, not signatures or a substitute for access control. Recovery
of an interrupted real application requires its own durable receipt/observation
contract; the host does not infer that an interrupted request failed.

## Migration decisions

Keep legacy and intended certificates separate. A migration contract binds both
exact digests. A decision binds one exact finding with an explicit approval and
rationale. Duplicate decisions are rejected. An unapproved difference is reported
as such, even when the target matches the intended behavior. Successful finite
traces establish compatibility within their observation scope, not universal
refinement. Incomplete observations and unresolved alternative worlds remain
inconclusive.

## Extending the system

Add domain axioms and sequent rules in Shen, with separate proof constructors and
checkers; update rulepack identity and negative tests. New source/binary producers
must retain source identity and unknowns. New observation maps must declare their
scope and completeness assumptions. New planners emit scenarios for independent
validation. ShenLogic's existing translator is reachable through `logic`; THORN
solver discovery/replay and automatic translation of this entire calculus into
external prover obligations are not implemented in this package.
