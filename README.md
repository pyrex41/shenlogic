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
shen-go script shen/cli.shen translate examples/factorial.shen --format graph
```

The exact invocation is also available through `make`. Machine-readable
outputs are written to files; diagnostic text goes to stderr and the process
returns a non-zero status on rejection.

## Semantic boundary

Version 0.1 reads fixed-arity definitions and separate or inline signatures.
Its Shen evaluator covers ordered literal, variable, wildcard, constructor,
proper-list, improper-list, and repeated-variable patterns; total primitive
guards; strict first-order calls; `if`, `let`, short-circuit `and`/`or`; exact
integers; direct recursion; and mutual recursion.

The logical translator currently accepts the first-order subset without
control-flow expressions. Constructor matching and complex ordered fallback
remain explicit `match` and `not-applicable` premises in the graph IR. The CHC
and THF backends accept the integer Horn profile and reject those premises
until their free-constructor lowering is implemented.

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
obligations; they are not claimed by version 0.1.

## Workflow

`make test` runs the Shen unit and golden tests. `make proof` runs the pinned
Lean checks when Lean is installed; CI installs Lean and requires the build.
`make bifrost` uses the compiled Bifrost
binary to compare deterministic records across Shen hosts. Yggdrasil/Ratatoskr
is a later packaging gate: it checks that shaken standalone artifacts produce
the same canonical `.slir` output.

See [docs/SEMANTICS.md](docs/SEMANTICS.md),
[docs/IR.md](docs/IR.md), [docs/BIFROST-INTEGRATION.md](docs/BIFROST-INTEGRATION.md),
and [docs/PROOF-OBLIGATIONS.md](docs/PROOF-OBLIGATIONS.md).

## Project status

This is a clean-room implementation. It does not claim compatibility with an
unavailable Shen2Logic implementation. The supported semantics, output grammar,
and proof obligations are versioned in this repository and may change before
the first public release.

Licensed under Apache-2.0.
