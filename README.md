# ShenLogic

ShenLogic translates a small, pure subset of Shen into logical specifications.
It is implemented in Shen and runs on Shen 41.2 with
[shen-go](https://github.com/pyrex41/shen-go).

For each supported Shen function, ShenLogic can produce:

- `surface`: compact equations for review;
- `graph`: relational rules describing terminating evaluations;
- `slir`: the canonical ShenLogic intermediate representation;
- `chc`: SMT-LIB constrained Horn clauses;
- `thf`: typed higher-order TPTP formulas.

The graph, CHC, and THF outputs use an explicit result relation. This preserves
partiality: if a Shen call does not terminate, the generated graph does not
assign it a result.

## Requirements

- Shen 41.2 through `shen-go`;
- Go 1.25 to build the pinned `shen-go` host;
- optional: Z3, TPTP4X, Lean 4.19, Bifrost, and Yggdrasil for the extended
  validation workflow.

By default, the Makefile uses `../shen-go/.bin/shen-go`. Set `SHEN_GO` to use a
different executable.

## Get started

```sh
make host
make test
make check
```

Translate the factorial example:

```sh
./bin/shenlogic translate examples/factorial.shen --format surface
./bin/shenlogic translate examples/factorial.shen --format graph
./bin/shenlogic translate examples/factorial.shen --format slir
./bin/shenlogic translate examples/factorial.shen --format chc
./bin/shenlogic translate examples/factorial.shen --format thf
```

Evaluate a supported expression:

```sh
./bin/shenlogic eval examples/factorial.shen '(factorial 5)'
```

Generate a solver query:

```sh
./bin/shenlogic query examples/factorial.shen '(factorial 5)' 120 --backend chc
```

Create and check the deterministic certificate bundle:

```sh
./bin/shenlogic certify examples/factorial.shen --out build/certificate
```

Commands return a nonzero status when source or an option is rejected.
Diagnostics go to stderr, while generated artifacts go to stdout or the path
given with `-o`.

## Supported Shen subset

Version 0.2 supports:

- fixed-arity definitions and type declarations;
- ordered clauses and total primitive guards;
- literal, variable, wildcard, repeated-variable, list, and constructor
  patterns;
- proper and improper lists;
- strict first-order calls;
- `if`, `let`, short-circuit `and`, and short-circuit `or`;
- exact integer arithmetic and comparisons;
- direct and mutual recursion.

It rejects unsupported behavior instead of approximating it. Rejected features
include floating point, division and other partial primitives, higher-order
values, lambdas, effects, I/O, mutable state, exceptions, dynamic loading,
Prolog/backtracking, and user-function calls in guards.

See [docs/SEMANTICS.md](docs/SEMANTICS.md) for the precise contract and
[docs/IR.md](docs/IR.md) for the SLIR v2 format.

## Meaning of the generated graph

For a Shen function `f`, ShenLogic generates a relation of the form:

```text
f$(arguments, result)
```

The relation means that evaluating `f(arguments)` terminates with `result`.
Clause order and guard fallback are represented explicitly. Recursive
relations are grouped into strongly connected components and given
simultaneous leastness conditions.

The intended correctness theorem is:

```text
P ⊢ f(a₁,…,aₙ) ⇓ v  iff  T(P) ⊨ f$(a₁,…,aₙ,v)
```

That full theorem is a target, not a current claim. The Lean project proves
the deterministic core and generic derivation/least-closure results. The
certificate checker verifies artifact structure and deterministic lowering; it
does not claim that an SMT or THF solver proved the generated theory.

The exact remaining obligations are listed in
[docs/PROOF-OBLIGATIONS.md](docs/PROOF-OBLIGATIONS.md).

## Validation and packaging

Useful workflow targets are:

```sh
make test             # Shen regression and golden tests
make certify          # deterministic certificate bundle
make backend-check    # Z3 and TPTP4X checks when installed
make proof            # Lean checks when installed
make bifrost          # cross-host Shen conformance
make yggdrasil-stage1 # standalone Go packaging gate
make package          # reproducible source archive and SHA-256 manifest
```

Tool and host revisions are pinned in [toolchain.lock](toolchain.lock).
Bifrost details are in
[docs/BIFROST-INTEGRATION.md](docs/BIFROST-INTEGRATION.md).

## Project status

ShenLogic 0.2 is a clean-room implementation. It does not claim compatibility
with an unavailable Shen2Logic implementation. The supported semantics and
output formats are versioned and may change before the first public release.

Licensed under Apache-2.0.
