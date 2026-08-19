# ShenLogic 0.1 semantic contract

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

The v1 evaluator has exact integers, booleans, symbols, strings, and free
constructors. The logical Rule IR currently excludes `if`, `let`, `and`, `or`,
and `do` until control-flow paths are lowered independently. It retains free
constructor matching as explicit premises. The CHC and THF emitters are
stricter still: their current profile is integer Horn logic, and they reject
constructor matches or complex applicability tests.

All modes exclude floating point, division, partial primitives, effects,
mutable state, I/O, exceptions, dynamic loading, Prolog/backtracking,
higher-order values, and user calls in clause guards.

The intended adequacy theorem is:

```text
P ⊢ f(a₁,…,aₙ) ⇓ v  iff  T(P) ⊨ f$(a₁,…,aₙ,v)
```

Lean mechanization and backend-specific assumptions are tracked separately in
[PROOF-OBLIGATIONS.md](PROOF-OBLIGATIONS.md).
