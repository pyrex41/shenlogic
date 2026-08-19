# ShenLogic

ShenLogic is a Shen-native translator from a deliberately small, pure Shen
fragment to executable logical specifications. It is intended to make the
relationship between Shen evaluation and typed second-order logic explicit,
testable, and eventually mechanized.

The implementation and test suite are written in Shen. The required
development host is Shen 41.2 through [shen-go](https://github.com/pyrex41/shen-go).
The generated artifacts are designed for three complementary consumers:

- `surface`: compact equations suitable for review;
- `graph`: a least evaluation-graph specification;
- `slir`, `chc`, and `thf`: a canonical intermediate representation and
  standard backend formats.

## Quick start

Set `SHEN_GO` to a Shen 41.2 executable (the default is
`../shen-go/.bin/shen-go`), then run:

```sh
make host
make test
make check
```

The command-line wrapper is invoked in script mode:

```sh
shen-go script shenlogic-cli.shen translate examples/factorial.shen --format graph

shen-go script shenlogic-cli.shen certify examples/factorial.shen --out build/certificate
shen-go script shenlogic-cli.shen query examples/factorial.shen "(factorial 5)" 120 --backend chc
```

The exact invocation is also available through `make`. Machine-readable
outputs are written to files; diagnostic text goes to stderr and the process
returns a non-zero status on rejection.

## Semantic boundary

Version 0.2 reads fixed-arity definitions and separate or inline signatures.
Its Shen evaluator covers ordered literal, variable, wildcard, constructor,
proper-list, improper-list, and repeated-variable patterns; total primitive
guards; strict first-order calls; `if`, `let`, short-circuit `and`/`or`; exact
integers; direct recursion; and mutual recursion.

The v2 front end normalizes source into a closed AST before validation. The
normalization boundary is explicit: source terms are never interpreted as
host code, and every backend consumes the same tagged Rule IR. Values use one
closed `Value` algebra (integers, booleans, symbols, strings, nil/cons, and
declared constructors), so symbols and strings cannot alias accidentally.
Constructor matching and ordered fallback lower to explicit `decompose` and
`not-tag` paths in the graph IR. CHC emits a Value-Horn model and THF emits the
full higher-order least-model obligations; unsupported terms are rejected at
the boundary.

The translator rejects floats, division and other partial primitives,
higher-order values, lambdas, effects, I/O, mutable state, dynamic loading or
evaluation, Prolog/backtracking, exceptions, and user-function calls in clause
guards. Rejection is explicit and stable; unsupported behavior is never
silently approximated.

## Logical meaning

For each function `f`, the graph backend emits a relation `f$` where
`f$(arguments,result)` means that the Shen call terminates with `result`.
Rules are ordered through an explicit decision tree, so a false guard may fall
through while an error or nonterminating guard blocks fallback. Recursive
functions are grouped into strongly connected components and receive a
simultaneous leastness condition. Consequently a negative factorial input has
no graph result when evaluation does not terminate.

The formal adequacy target is:

```text
P ⊢ f(a₁,…,aₙ) ⇓ v  iff  T(P) ⊨ f$(a₁,…,aₙ,v)
```

The `proof/` Lean project checks the current pattern/evaluator determinism
lemmas. Recursive adequacy and backend preservation remain explicit proof
obligations. A structural certificate gate is available through `certify`; it
writes a deterministic bundle for a separately configured solver/proof run and
does not itself claim an SMT/THF proof.

## Workflow

`make test` runs the Shen unit and golden tests. `make certify` produces the
proof-certificate bundle. `make backend-check` runs Z3 and TPTP4X when they are
installed. `make proof` runs the pinned
Lean checks when Lean is installed; CI installs Lean and requires the build.
`make bifrost` uses the compiled Bifrost
binary to compare deterministic records across Shen hosts. Yggdrasil/Ratatoskr
runs as a release/nightly stage-1 Go packaging gate with an isolated
`GOFLAGS=-mod=mod`; it compares the stage-1 and built kernels and executes the
generated Go artifact.
`make package` fixes numeric owners, sorting, and `SOURCE_DATE_EPOCH`, then
writes a SHA-256 manifest alongside the archive.

See [docs/SEMANTICS.md](docs/SEMANTICS.md),
[docs/IR.md](docs/IR.md), [docs/BIFROST-INTEGRATION.md](docs/BIFROST-INTEGRATION.md),
and [docs/PROOF-OBLIGATIONS.md](docs/PROOF-OBLIGATIONS.md).

## Project status

This is a clean-room implementation. It does not claim compatibility with an
unavailable Shen2Logic implementation. The supported semantics, output grammar,
and proof obligations are versioned in this repository and may change before
the first public release.

The current workflow and IR contract are version 0.2.0 (SLIR v2).

Licensed under Apache-2.0.
