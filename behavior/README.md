# Shen behavioral reconstruction

An executable behavioral-type system and reverse-engineering workflow inside
ShenLogic. Shen owns the judgments and reference semantics. Source/binary
extractors produce facts; Soufflé computes may analyses; GraphWalker proposes
paths; adapters produce observations. Neither a planner nor an extractor can
mint an implementation proof.

## Run

Requires Node 24+, git, make, and a C compiler. No npm install scripts are run.

```sh
cd behavior
npm run bootstrap
npm test
npm run demo
node bin/behavior.mjs replay build/demo/counterexample.json
```

The bootstrap builds pinned LuaJIT and checks out pinned shen-lua into `.tools`.
It refuses to rewrite an unexpected existing checkout. To use an existing
installation instead, set `LUA` and `SHEN_LUA_ROOT`, then `npm ci --ignore-scripts`.
The application runs one persistent Shen worker, not a process per judgment.

For all external integration tests on Linux x64 (roughly 800 MB of downloads):

```sh
npm run bootstrap -- --external
npm run test:external
```

Downloads have pinned URLs and SHA-256 digests in `toolchain.json`. On other
platforms configure `SOUFFLE`, `GRAPHWALKER_JAR` (or `GRAPHWALKER`), `GHIDRA_HOME`,
and `JAVA_HOME` manually. Basic tests explicitly skip unconfigured external
runtimes; `test:external` requires all of them and fails if one is missing.

## What runs end to end

`npm run demo` parses `fixtures/transfers.php` with a real PHP parser,
reconstructs two behaviors through explicit domain API contracts, and creates
Shen certificates. The intended behavior must inhabit three refinements:

- retry safety **by durable deduplication**;
- preservation of the sum of `alice` and `bob` balances, by affine reasoning;
- effect inclusion in ledger writes and a transfer outbox intent.

It then runs two independent SQLite implementations through a commit/lost-response/
retry scenario. The intended implementation is compatible with the observations;
the legacy implementation violates the intended behavior by applying the transfer
twice. The counterexample is minimized, stored, and replayable. A finite exploration
produces a GraphWalker model, and paths are rechecked by Shen before execution.
A migration comparison leaves the intentional difference **unapproved** until an
explicit reviewer decision is supplied. The demo does not manufacture approval.

Outputs in `build/demo` include source AST/facts, reconstruction assumptions,
certificates, observations, conformance results, scenario projections, the migration
finding, and an integrity-checked SQLite journal. Soufflé analysis runs when its
executable is configured; its absence does not become a successful analysis.

## The semantic core

`shen/calculus.shen` defines actual indexed Shen datatypes. A derivation inhabits:

```
bt-proof Program ResourcesIn ResourcesOut Effects
bt-retry-safe Program Resources Effects
bt-effects-within Program ResourcesIn ResourcesOut AllowedEffects
bt-preserves Program ResourcesIn ResourcesOut Effects Fields
```

Each composition constructor is a sequent rule. Proof construction (`bt.infer`)
is separate from checking (`bt.check-ground`, using System S). The proof checker
does not call the constructor. Context/effect witnesses are inert indices; the Lua
bridge elaborates proof constructors without running submitted expressions. It
calls System S directly because the general source typechecker curries arbitrary
list-shaped index data. The bridge is included in the frozen rulepack digest.

The simulator, affine invariant checker, and observation matcher are also Shen.
Node handles process I/O, parsing, projections, databases, and scheduling.

See [the calculus](docs/CALCULUS.md) for the language and exact guarantees.

## Use your code

```sh
node bin/behavior.mjs extract /path/to/application > build/source.json
node bin/behavior.mjs analyse build/source.json > build/analysis.json
node bin/behavior.mjs reconstruct build/source.json contracts.json exactEntry > build/reconstruction.json
node bin/behavior.mjs certify build/reconstruction.json > build/certificate.json
```

A directory extraction visits PHP files and excludes symlinks, `.git`, `vendor`,
and `node_modules`; its manifest records the selected scope. Source files retain
individual byte digests. Ambiguous entry names require an exact node ID.
Reconstruction supports straight-line contract calls, declared closure scopes,
and conditionals over supported expressions. Unsupported statements/calls produce
obligations and **no executable program**. `candidate` is diagnostic only.

`fixtures/contracts.json` shows how to bind application APIs to behavioral terms.
Those bindings are named assumptions, not facts inferred from function names.
`admit` requires explicit approval of each assumption and still labels the result
`conditional`, never universally verified. For native binaries see
[integrations](docs/INTEGRATIONS.md).

Models can define reusable parameterized behaviors with `definitions` and
`["invoke", name, arguments]`. Expansion is bounded and rejects recursion;
iteration must be an explicit bounded `repeat`. `compose.mjs` records the source
digest; executable certificates bind the expanded program.

## Commands and persistent API

`node bin/behavior.mjs --help` lists the CLI. It includes extraction, analysis,
reconstruction, admission, certification, simulation, exploration, GraphWalker,
trace checking, execution, replay, migration comparison, and journal inspection.
`logic FILE tsl|chc|thf|slir|lpc|graph` exposes the existing ShenLogic translator
through the same persistent worker; it does not assert that this whole behavioral
interpreter has been translated or proved by ShenLogic.

```sh
BEHAVIOR_TOKEN='use-a-long-local-token' node bin/behavior.mjs serve 7070 evidence.sqlite
```

The server binds only to `127.0.0.1`, requires a bearer token, rejects Origin headers,
and accepts bounded JSON requests. Endpoints: `/certify`, `/verify`, `/run`,
`/explore`, `/check-trace`; `GET /artifact/<digest>` retrieves stored results.
It does not expose arbitrary Shen evaluation or external command execution.

## Verification and boundaries

See [verification](docs/VERIFICATION.md) for executed gates and remaining limits.
This is a working framework, not a claim of complete PHP semantics, arbitrary
binary verification, a proved Shen host, or a completed migration of an unseen
application. The first built-in semantic refinements are affine preservation,
effect inclusion, and method-specific retry safety. New domain logics can be added
as Shen datatypes and checking rules with an updated rulepack identity.

The same Apache-2.0 license as the parent repository applies to this code.
External tools retain their own licenses and are not vendored here.
