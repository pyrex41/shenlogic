# ShenLogic 0.2 semantic contract

## Normalization and values

Source is read as data and normalized into a tagged AST before validation. This
is the trust boundary: no source form is evaluated while it is being lowered.
All values inhabit one closed `Value` ADT: exact integers, booleans, symbols,
strings, nil/cons lists, and declared free constructors. Equality and quoting
are defined on those tags, never delegated to host-language representation.

## Evaluation

Definitions have fixed arity and ordered clauses. A pattern mismatch advances
to the next clause. A successful total guard returning false advances; a true
guard evaluates the body. A guard error or nontermination blocks fallback. Body
calls are strict and first-order. The executable Shen evaluator reports a
value, an error, or a fuel timeout; a timeout is an observation, not a proof of
divergence.

Patterns include literals, variables, `_`, constructors, proper and improper
lists, and repeated variables. Repetition is equality, not rebinding.

## Graph semantics

For `f : A₁ -> ... -> Aₙ -> B`, `f$` is a relation over
`A₁ × ... × Aₙ × B`. `f$(a₁,...,aₙ,b)` means that evaluation terminates with
`b`. Each decision-tree path becomes a closure rule. Recursive calls become
positive graph premises.

Rules are closed under simultaneous strongly connected components. The graph
is additionally contained in every candidate tuple of relations closed under
the same rules; this is the least closed relation and excludes junk results.

## Supported fragment and model

The v2 evaluator has exact integers, booleans, symbols, strings, and free
constructors. The Rule IR retains control-flow paths and lowers
free-constructor matching to explicit `decompose`/`not-tag` premises. CHC
lowers the closed Value ADT to SMT-LIB datatypes. THF emits typed higher-order
axioms for the intended full model, including simultaneous SCC leastness;
neither backend silently treats an unknown solver result as a proof.

All modes exclude floating point, division, partial primitives, effects,
mutable state, I/O, exceptions, dynamic loading, Prolog/backtracking,
lambdas and partial application, and user calls in clause guards.

## Function parameters

Signatures may declare arrow types in argument positions. A clause-head
variable at such a position is a function parameter: it may be applied,
fully saturated, and passed on at other arrow positions; a defined
function name may be passed where an arrow of its arity is expected.
Arrow result types, nested arrows, lambdas, and partial application stay
rejected (`sl-v006`, `sl-v041`, `sl-v043`..`sl-v048`).

The logical model is defunctionalization by name: a function value is its
name as a symbol. For each applied arity `N` the theory gains a relation
`sl.apply-N` over `value^(N+1)` with one rule per defined arity-N
function `f`:

```text
sl.apply-N('f, x1, ..., xN, r)  <=  f$(x1, ..., xN, r)
```

Applications `(F X)` lower to `sl.apply-1` premises. Rules are generated
for every arity-N function, so query-injected names behave exactly as
the evaluator does; junk applications (a symbol naming no function, or
the wrong arity) simply have no derivation, again matching the
evaluator. `sl.apply-N` participates in the SCC ordering as an ordinary
node; its dependency on all arity-N functions can merge SCCs, which is a
sound over-approximation for the simultaneous leastness conditions. The
extended adequacy statement reads
`P ⊢ (map f l) ⇓ v iff T(P) ⊨ map$('f, l, v)`.

Names beginning with `sl.apply-` are reserved (`sl-v048`). A symbol used
both as data and as a function name denotes one value; the theory and
evaluator agree on this, and only the typed tsl reading distinguishes
the two roles.

## tsl semantics

The `tsl` format renders the same programs as a typed second-order
equational theory (see [TSL-LOGIC.md](TSL-LOGIC.md)). Its intended models
are sorted: `number` is the integers, `boolean` two-valued, `(list A)`
the finite proper lists, and `value` the free algebra of the program's
constructors. Declared signatures are required and checked; programs
without a consistent typed reading are rejected rather than
approximated. Equations are guarded by `defined-` antecedents exactly
where the conservative termination classifier could not prove totality,
so partial functions are never silently totalized. The intended
definedness reading is `defined-f(ā) iff exists v. f$(ā,v)` against the
graph semantics above; that correspondence is a stated obligation, not a
mechanized theorem.

The intended adequacy theorem is:

```text
P ⊢ f(a₁,…,aₙ) ⇓ v  iff  T(P) ⊨ f$(a₁,…,aₙ,v)
```

Lean mechanization and backend-specific assumptions are tracked separately in
[PROOF-OBLIGATIONS.md](PROOF-OBLIGATIONS.md).
