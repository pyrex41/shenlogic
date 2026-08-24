# Bifrost integration

Bifrost is the cross-host conformance gate. It invokes the same ShenLogic
script on each available Shen 41.2 host and compares deterministic records.
The suite must use the compiled Bifrost Go binary; the legacy script runner is
not a project dependency.

The test entrypoint writes records in this shape:

```text
PASS <case-id>
SHENLOGIC|ALL PASS
```

Host load chatter is normalized by the suite. Canonical `.slir`, surface,
graph, CHC, THF, and tsl files are compared byte-for-byte inside the shared
Shen tests. A host that is unavailable is reported as skipped.

`make bifrost` sets `SHEN_FASL=off`. This forces shen-lua to compile the
current nested Shen modules instead of replaying a warm user-program image,
so an edited dependency is always part of the conformance run.

The suite covers factorial, overlapping and repeated-variable patterns,
Fibonacci, mutual recursion, guard rejection, v2 Value/constructor cases,
function parameters (`map`/`filter`), the tsl typed equational output and its
soundness-regression corpus, and the portable repair API.
`bifrost.suite.json` is the source of truth for command arguments and expected
markers. The suite also checks the byte-canonical SLIR v2 marker.

## Host policy

Per-change checks require the pinned shen-go, shen-cl, and shen-lua hosts.
Nightly and release checks may add shen-rust, ShenScript, and other conforming
41.2 ports. Host revisions are recorded in `toolchain.lock`; no floating
checkout is a release input.

Yggdrasil/Ratatoskr runs only after Bifrost parity in the release/nightly
workflow. Its role is to package the translator and compare shaken artifacts,
not to define source semantics; its Go stage is isolated with
`GOFLAGS=-mod=mod`.
