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
graph, CHC, and THF files are compared byte-for-byte inside the shared Shen
tests. A host that is unavailable is reported as skipped.

The first suite covers factorial, overlapping and repeated-variable patterns,
Fibonacci, mutual recursion, guard rejection, and v2 Value/constructor cases.
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
