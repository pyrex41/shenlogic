# ShenLogic

ShenLogic translates a small, pure subset of Shen into logical specifications.
It is implemented entirely in Shen and is portable across conforming Shen 41.2
implementations. The regression suite currently passes on
[shen-go](https://github.com/pyrex41/shen-go),
[shen-cl](https://github.com/pyrex41/shen-cl), and
[shen-lua](https://github.com/pyrex41/shen-lua).

For each supported Shen function, ShenLogic can produce:

- `surface`: compact equations for review;
- `graph`: relational rules describing terminating evaluations;
- `slir`: the canonical ShenLogic intermediate representation;
- `chc`: SMT-LIB constrained Horn clauses;
- `thf`: typed higher-order TPTP formulas;
- `tsl`: typed second-order equations with definedness guards and
  constructor axioms (see [docs/TSL-LOGIC.md](docs/TSL-LOGIC.md)).

The graph, CHC, and THF outputs use an explicit result relation. This preserves
partiality: if a Shen call does not terminate, the generated graph does not
assign it a result. The `tsl` output preserves partiality equationally: calls
to functions a conservative termination check cannot prove total are guarded
by `defined-` antecedents, so a divergent definition never makes the theory
inconsistent.

## Requirements

- a Shen 41.2 implementation;
- Go 1.25 only when building the default `shen-go` development host;
- optional: Z3 4.15, TPTP4X, Lean 4.19, Bifrost, Yggdrasil, and ShellCheck for
  the extended validation workflow.

Ground-example repair uses only ShenLogic and its integrated Prolog. Z3 is
required when a repair contract contains quantified laws. TPTP4X is a syntax
gate for generated THF and is not needed at runtime. Exact tested revisions
are recorded in [toolchain.lock](toolchain.lock).

The bundled command-line wrapper and the basic Make targets use `shen-go` by
default. The Shen source itself has no dependency on Go. Bifrost runs the same
suite through each installed Shen host.

## Get started

```sh
make host
make test
make check
make repair-check
make bifrost
```

`make bifrost` tests shen-go, shen-cl, and shen-lua when they are installed.
Set `BIFROST_IMPLS` to select another Bifrost host list.

Translate the factorial example:

```sh
./bin/shenlogic translate examples/factorial.shen --format surface
./bin/shenlogic translate examples/factorial.shen --format graph
./bin/shenlogic translate examples/factorial.shen --format slir
./bin/shenlogic translate examples/factorial.shen --format chc
./bin/shenlogic translate examples/factorial.shen --format thf
./bin/shenlogic translate examples/factorial.shen --format tsl
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

Repair Shen source from an edited `tsl` equation view. Generate the view from
the exact source revision being repaired, edit only its `; equations` section,
then preview a patch:

```sh
./bin/shenlogic translate examples/factorial.shen \
  --format tsl -o build/factorial.tsl.logic

# This checked-in fixture is that view with factorial 0 changed from 1 to 2.
./bin/shenlogic repair examples/factorial.shen \
  --logic tests/fixtures/repair-factorial.tsl.logic \
  --spec tests/fixtures/repair-factorial.spec

# Apply only after all examples and quantified laws pass.
./bin/shenlogic repair examples/factorial.shen \
  --logic tests/fixtures/repair-factorial.tsl.logic \
  --spec tests/fixtures/repair-factorial-law-true.spec --write
```

Without `--write`, repair emits a deterministic unified diff. It can change
the target definition's patterns, guards, clauses, and bodies while keeping
its name, signature, and arity fixed. Only the `; equations` section is an
editable view; changes to generated scaffolding are rejected. Quantified laws
require Z3. A rejected or inconclusive candidate leaves the source untouched;
a successful `--write` replaces only the repaired definition. The definition
is canonically formatted, so review the diff or keep the source under version
control. See [docs/REPAIR.md](docs/REPAIR.md) for the repair contract, safety
boundary, and current synthesis fragment.

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
- function parameters: arrow-typed arguments that are applied fully
  saturated or passed on, with defined function names as arguments
  (modeled by name via generated `sl.apply-N` relations);
- `if`, `let`, short-circuit `and`, and short-circuit `or`;
- exact integer arithmetic and comparisons;
- direct and mutual recursion.

It rejects unsupported behavior instead of approximating it. Rejected features
include floating point, division and other partial primitives, lambdas,
partial application, function-valued results, effects, I/O, mutable state,
exceptions, dynamic loading, Prolog/backtracking, and user-function calls
in guards.

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
make repair-check     # repair CLI, solver rejection, and write barrier
make shellcheck       # shell wrappers when ShellCheck is installed
make certify          # deterministic certificate bundle
make backend-check    # Z3 and TPTP4X checks when installed
make proof            # Lean checks when installed
make bifrost          # shen-go, shen-cl, and shen-lua conformance
make yggdrasil-stage1 # standalone Go packaging gate
make package          # reproducible source archive and SHA-256 manifest
make test-all         # regression, host, proof, backend, and repair gates
```

Targets that depend on optional tools report `SKIP` when a tool is absent.
The release-readiness run uses the available pinned tools and all three Shen
hosts; a passing executable test suite is evidence for the implemented
fragment, not a substitute for the open proof obligations.

Tool and host revisions are pinned in [toolchain.lock](toolchain.lock).
Bifrost details are in
[docs/BIFROST-INTEGRATION.md](docs/BIFROST-INTEGRATION.md).

## Project status

ShenLogic 0.2 is a clean-room implementation. It does not claim compatibility
with an unavailable Shen2Logic implementation. The supported semantics and
output formats are versioned and may change before the first public release.
Round-trip repair is an experimental, bounded synthesis feature: it is not a
general inverse for arbitrary axioms, and it fails closed outside its stated
fragment.

Licensed under Apache-2.0.
