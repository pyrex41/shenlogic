# ShenLogic

ShenLogic compiles a pure subset of [Shen](https://shenlanguage.org) into
formal logic. For each function it emits a machine-checkable theory —
typed equations, definedness predicates, and datatype axioms — that states
exactly what the function computes, so Shen programs can be verified
against specifications with off-the-shelf provers, and so verified
properties can travel with the program wherever a trusted port takes it.
The translation also runs in reverse, in a bounded way: edit the generated
equations and ShenLogic can search for a source patch that makes the edits
true again.

ShenLogic is implemented entirely in Shen and is portable across
conforming Shen 41.2 implementations. The regression suite currently
passes on [shen-go](https://github.com/pyrex41/shen-go),
[shen-cl](https://github.com/pyrex41/shen-cl), and
[shen-lua](https://github.com/pyrex41/shen-lua).

## From code to logic

Shen functions are ordered, guarded pattern-matching rules:

```shen
(define factorial
  { number --> number }
  0 -> 1
  X -> (* X (factorial (- X 1))))
```

`./bin/shenlogic translate examples/factorial.shen --format tsl` turns
that definition into a typed second-order theory:

```text
; totality: factorial unknown (no descent measure found)

; definedness: factorial
(defined-factorial 0)
(all X : number ((and (~ (X = 0)) (defined-factorial (- X 1))) => (defined-factorial X)))
(all X : number ((defined-factorial X) => (or (X = 0) (and (~ (X = 0)) (defined-factorial (- X 1))))))
(all P : (number => o) ((and (P 0) (all X : number ((and (~ (X = 0)) (P (- X 1))) => (P X)))) => (all X : number ((defined-factorial X) => (P X)))))

; equations
((factorial 0) = 1)
(all X : number ((and (~ (X = 0)) (defined-factorial (- X 1))) => ((factorial X) = (* X (factorial (- X 1))))))
```

Three things happen here that a naive clauses-to-equations reading gets
wrong:

- **Clause order is compiled away.** The second clause only fires after
  the first fails, so its equation carries the antecedent `(~ (X = 0))`.
  When an earlier clause has constructor patterns, the condition becomes
  an existentially quantified non-match, and conditions that constructor
  disjointness already decides are pruned.
- **Partiality is explicit.** `factorial` diverges on negative inputs, and
  the termination classifier cannot prove it total, so its recursive
  equation is guarded by `defined-factorial`, which is axiomatized as the
  least predicate closed under the clause structure. This is not
  pedantry: the unguarded equation for a divergent function such as
  `(define d N -> (+ 1 (d N)))` would let classical arithmetic derive
  `0 = 1` and poison every theorem in the program. Guarded, the same
  theory instead proves `(~ (defined-d N))` — the right answer.
- **Disequalities are provable.** Programs that use lists or free
  constructors get injectivity, disjointness, and structural induction
  axioms, so facts like `(~ ((cons X Y) = ()))` are theorems rather than
  wishes. A theory of bare conditional equations plus congruence cannot
  prove them.

When the conservative termination check does prove a function total —
structural descent, lexicographic descent, or an integer measure with a
guard-derived bound — the guards disappear and the equations take the
textbook form:

```text
; totality: append2 total (structural descent at argument 0)
(all A : type (all Ys : (list A) ((append2 () Ys) = Ys)))
(all A : type (all X : A (all Xs : (list A) (all Ys : (list A) ((append2 (cons X Xs) Ys) = (cons X (append2 Xs Ys)))))))
```

Polymorphism and function parameters render natively; `map` comes out as

```text
(all A : type (all B : type (all F : (A --> B) ((map F ()) = ()))))
```

with each application site contributing a `defined-apply-1` obligation.
The logic these theories live in — sorts, deduction rules, intended
models — is pinned down in [docs/TSL-LOGIC.md](docs/TSL-LOGIC.md).

## What this enables

- **Check concrete facts with a solver.** `shenlogic query` emits an
  SMT-LIB Horn query for a ground claim; Z3 answers `sat` for facts the
  program actually computes and `unsat` for facts it does not — including
  through higher-order calls like `(map double [1 2]) = [2 4]`.
- **Prove properties against specifications.** The emitted equations,
  induction schemas, and definedness axioms are a proof-ready
  axiomatization. They describe what the code does, not what its author
  meant: give `length` a recursive clause that forgets the `+ 1` and the
  theory faithfully lets you prove `(all Xs ((length Xs) = 0))` by list
  induction — which is exactly why checking it against an independent
  specification catches the bug.
- **Round-trip repair.** Because the equation view is faithful, a bounded
  edit to it can be pushed back into source: `shenlogic repair` searches
  for a patched definition that regenerates the edited equations and
  passes a contract of examples and Z3-checked laws (details below).
- **A second, executable opinion.** The built-in evaluator is the
  semantic oracle for every translation decision, and the whole suite
  runs byte-identically on three independent Shen hosts, so the logic is
  tested against running code, not intuition.

## How it works

Everything downstream of the reader treats source as inert data:

1. **Read and normalize.** Definitions are parsed into a tagged AST; no
   source form is evaluated during lowering.
2. **Validate.** Unsupported behavior is rejected with a diagnostic
   instead of being approximated (see the fragment below).
3. **Compile to the Rule IR.** Ordered clauses, guards, and fallback
   become explicit, mutually exclusive decision paths over a relation
   `f$(arguments, result)` meaning "evaluation terminates with result".
   Recursive relations are grouped into strongly connected components
   with simultaneous least-fixed-point conditions.
4. **Render.** Backends print the same theory in different logics, and a
   typing pass plus termination classifier produce the guarded equational
   view:

   - `surface`: compact untyped equations for review;
   - `graph`: readable relational rules describing terminating
     evaluations;
   - `slir`: the canonical ShenLogic intermediate representation;
   - `chc`: SMT-LIB constrained Horn clauses for Z3;
   - `thf`: typed higher-order TPTP formulas;
   - `tsl`: typed second-order equations with definedness guards and
     constructor axioms (see [docs/TSL-LOGIC.md](docs/TSL-LOGIC.md)).

The graph, CHC, and THF outputs preserve partiality through the result
relation: a call that does not terminate is simply assigned no result.
The `tsl` output preserves it equationally through `defined-` guards, so
a divergent definition never makes the theory inconsistent. Function
values are modeled by name (defunctionalization via generated
`sl.apply-N` relations), which keeps the theory first-order everywhere a
first-order solver needs it to be.

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

## Round-trip repair

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

## The correctness claim, stated honestly

For a Shen function `f`, the generated relation `f$(arguments, result)`
means that evaluating `f(arguments)` terminates with `result`. Clause
order and guard fallback are represented explicitly, and recursive
relations carry simultaneous leastness conditions. The intended
correctness theorem is:

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
