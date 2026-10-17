# Verification record

Validated on Linux x64, Node 24.19.0, pinned LuaJIT and shen-lua from
`toolchain.json`. External runs used Soufflé 2.5, GraphWalker 4.3.3, Ghidra 12.1.4
and JDK 21. Downloads are checksum pinned.

The final strict run passed **57 tests, zero failures, zero skips**.
The strict gate executes all tests without external-tool skips:

```sh
npm run test:external
```

Coverage includes:

- Actual Shen System-S checking of indexed behavioral types, invalid proof
  rejection, affine preservation, effect bounds, method-specific retry safety,
  resource minting restrictions and bridge code-injection rejection.
- Reference execution, overflow and fuel limits, atomic rollback, receipt
  identity/input conflicts, unknown-commit alternatives and observation matching.
- Actual PHP parsing and reconstruction, unsupported-code obligations, project
  manifests and ambiguous entries, conditional binary manifests and admission.
- SQLite evidence integrity, lease conflicts, tampered journals, durable receipts,
  lost-response retry, conformance, migration decision binding and minimization.
- Local HTTP and subprocess adapters, persistent authenticated API, reusable
  behavior composition and existing ShenLogic translation in the same worker.
- Real Soufflé execution and real GraphWalker paths rechecked by Shen.
- Real Ghidra headless analysis of a C fixture compiled during the test; exported
  P-code and SSA references are inspected.
- PostgreSQL/MySQL driver control flow through injected drivers; these are not
  live database integration tests.

The original parent ShenLogic `tests/run-all.shen` suite also reports
`SHENLOGIC|ALL PASS`. The demo produces a compatible intended trace, a legacy
violation, a two-step minimized counterexample and an unapproved migration change.
The source is formatted and checked with `git diff --check`.

CI runs bootstrap, formatting, tests and the demo. A manually enabled external
job downloads the pinned integrations and enforces the strict gate. Normal tests
report explicit skips if external tools are not configured.

## What these results do not establish

This is an executable framework with a specific initial behavioral calculus.
It is not a mechanically proved soundness theorem for that calculus, a proof of
Shen/LuaJIT, a full PHP or machine-code semantics, or a migration proof for an
application that has not been supplied. Domain API contracts, atomicity, receipt
persistence and observation completeness are explicit assumptions until connected
to stronger evidence. Finite test compatibility is not universal equivalence.

Built-in invariants cover affine sums over supported arithmetic on successful
completion. They do not establish arbitrary temporal properties, liveness,
concurrency serializability, actual message delivery or exactly-once consumption.
The simulator models ordered effect intents. State exploration is finite and
bounded. Binary extraction cannot alone establish behavioral refinement.

THORN integration, arbitrary-domain prover replay, a general application rewrite,
additional source languages, Antithesis integration and live database certification
remain work beyond this implementation. No placeholders are reported as verified.
