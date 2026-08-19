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

Host banners go to stderr. Canonical `.slir`, surface, graph, CHC, and THF
files are compared byte-for-byte. A host that is unavailable is reported as
skipped in ordinary development runs and is required for the release matrix.

The first suite covers factorial, overlapping and repeated-variable patterns,
Fibonacci, mutual recursion, and guard rejection. `bifrost.suite.json` is the
source of truth for command arguments and expected markers.

## Host policy

Per-change checks require shen-go. Nightly checks add shen-cl and any pinned
shen-rust, shen-lua, or ShenScript hosts present in the runner. Host revisions
are recorded in `toolchain.lock`; no floating checkout is a release input.

Yggdrasil/Ratatoskr runs only after Bifrost parity. Its role is to package the
translator and compare shaken artifacts, not to define source semantics.
