# TSL: the typed second-order logic behind the `tsl` output

The `tsl` format emits a theory in a sorted second-order logic. This file
fixes the language, the deduction rules, and the intended models, so that
`|-` has a definite meaning. A translation without a stated deductive
system cannot claim that provability tracks evaluation; this document is
that statement for ShenLogic.

## Language

Types:

- rigid sorts `number` (exact integers), `boolean`, `symbol`, `string`,
  and `value`;
- `(list T)` for each type `T`;
- rank-1 function types `(T1 --> ... --> R)` in argument positions of
  signatures and quantifiers;
- type variables `A, B, ...`, bound only by `(all A : type ...)`;
- predicate types `(T1 => ... => o)`, bound only by second-order
  quantifiers.

Terms: variables; integer, string, symbol, and boolean literals; `()`;
`(cons t u)`; user constructor applications; function applications
`(f t1 ... tn)`; arithmetic terms `(+ - *)`; conditional terms
`(if c t u)`; and boolean-sorted term formers `(< > <= >= = neq and or)`.
The comparison, equality, and connective spellings are overloaded: in a
condition position they are formulas, in a value position they are terms
of sort `boolean`. Whenever a program uses one as a term, the output
includes bridge axioms tying the term to its formula reading (e.g.
`(all X : number (all Y : number ((< X Y) => ((< X Y) = true))))` and its
negative twin), so equations like `((positive? X) = (> X 0))` have
derivational force.

Formulas: `true`, `false`, `(t = u)`, integer comparisons
`(< > <= >=)`, `defined-f` and `defined-apply-N` atoms,
predicate-variable applications, `(~ F)`, `(and F ...)`, `(or F ...)`,
`(F => G)`, `(F <=> G)`, `(all X : T F)`, `(some X : T F)`,
`(all A : type F)`, and `(all P : (T => o) F)`.

Every function symbol `f` carries the declared Shen signature; every term
is well-typed under it. `tsl` refuses programs it cannot type
(`sl-t001`..`sl-t005`), so the emitted theory is always well-sorted.

## Deduction rules

The system is classical natural deduction over this sorted language:

- introduction and elimination for `and`, `or`, `~`, `=>`, with the
  classical absurdity rule;
- `all`-introduction/elimination and `some`-introduction/elimination for
  term variables, instantiating only with well-typed terms of the bound
  variable's type;
- `all`-introduction/elimination for type variables: from
  `(all A : type F)` infer `F[A := T]` for any closed type `T` built from
  the sorts and `list` (not from `-->`: the fragment is rank-1, so type
  variables never instantiate to function types);
- second-order `all`-elimination for predicate variables, restricted to
  *formula comprehension*: `(all P : (T => o) F)` may be instantiated
  with any formula-with-a-hole of the matching type. This schema reading
  avoids full comprehension while making the induction and minimality
  axioms usable;
- `=` is reflexive, symmetric, transitive, and a congruence for every
  function symbol, constructor, and predicate.

Background theory:

- linear integer arithmetic for `number` terms and comparisons;
- distinct symbol literals denote distinct elements of `symbol`; distinct
  string literals denote distinct elements of `string`;
- `boolean` axioms (`(~ (true = false))` and case analysis) and the
  conditional axioms are *emitted* by `tsl` when the program uses them,
  not assumed.

## The emitted theory

For a program `P`, `T(P)` contains:

1. **Constructor axioms.** Injectivity, pairwise disjointness, and
   structural induction for `cons`/`()` at every `(list A)`, and for the
   program's free constructors at `value`. These are what make
   disequalities such as `(~ ((cons X Y) = ()))` provable; a theory of
   bare conditional equations plus congruence cannot prove them (the gap
   in Thompson's 1995 system for Miranda, which supplied equations and
   congruence only).
2. **Definedness predicates.** For each function `f` the termination
   classifier could not prove total: intro clauses (one per source
   clause), an inversion axiom, and, for self-recursive `f`, a
   second-order minimality schema. `defined-f` is intended as the exact
   termination domain of `f`. For mutually recursive unknown functions
   the minimality of the definedness family is a property of the
   intended model, stated in the output as a comment rather than an
   axiom.
3. **Equations.** One per source clause: priority exclusions (negations
   of earlier clauses' applicability, pruned when constructor
   disjointness already decides them), then the guard, then the body's
   definedness obligations, implying the clause equation.

## Simplification

Emitted formulas are reduced before printing by a small, ordered,
size-decreasing set of classical equivalences (see the rule catalog in
`shen/tsl.shen`): unit and flattening laws, double negation, duplicate
elimination, and contextual deletion — a definedness obligation is
dropped when the clause's exclusions, guard, and earlier obligations
already syntactically contain it (a disjunct, dually, is reduced under
the negations of its earlier siblings). Deletion is fail-closed: an
entailment the reducer cannot establish syntactically leaves the
formula unchanged. Shared branch obligations of a conditional factor
out by excluded middle at emission, and inversion-case exclusions are
specialized against the case clause's own patterns so
constructor-disjoint priors are pruned (justified by the co-emitted
disjointness axioms). The reducer never alters axiom blocks, quantifier
binders, exclusion or guard conjuncts, or any term; determinism comes
from a fixed left-to-right strategy over lists, so output remains
byte-identical across Shen hosts.

## Partiality discipline

A classical equation between terms asserts denotation; an unguarded
equation about a partial function silently totalizes it (`nth 0` has no
value in Shen, yet `((nth X L) = ...)` would still denote). `tsl`
therefore guards every call to a function not proven total with a
`defined-` antecedent at the call site. Unguarded equations appear only
when the conservative termination classifier (structural descent,
two-position lexicographic descent, or integer descent with a
guard-derived lower bound; see `shen/termination.shen`) has proven every
callee total. The classifier never accepts clause-order exclusions such
as `(~ (X = 0))` as an integer bound, so `factorial` stays guarded: it
really does diverge on negative inputs.

## Intended models and soundness reading

A model interprets `number` as the integers, `boolean` as a two-element
sort, `symbol`/`string` as infinite sorts of literals, `(list T)` as the
finite proper lists over `T`, and `value` as the free algebra of the
program's constructors. Function symbols denote arbitrary total
functions of their sort; the equations constrain them only on the
definedness domain, so a partial Shen function is modeled by any total
extension of its graph — every theorem proved from `T(P)` about defined
applications is therefore a theorem about the Shen function.

The intended correspondence, relative to the graph semantics
(`docs/SEMANTICS.md`), is:

- `defined-f(a1,...,an)` iff `exists v. f$(a1,...,an,v)`;
- under that reading, each emitted equation and definedness axiom is
  satisfied by the least model of the graph rules.

This correspondence is stated, not yet mechanized; the Lean obligations
that would discharge it are tracked in `docs/PROOF-OBLIGATIONS.md`.

## Function parameters

A variable of function type may be applied — `((F X) = ...)` renders
application directly, and `(all F : (A --> B) ...)` quantifies over the
function space of the model. A defined function name written where an
arrow type is expected denotes that function; its signature instantiates
at the use.

Each applied arity `N` introduces `defined-apply-N`, read as a
type-indexed schema — one predicate per instantiation of
`forall A1..AN, B. (A1 --> ... --> B) => A1 => ... => AN => o` — rather
than a single monomorphic predicate constant; occurrences at different
arrow sorts are instances of that scheme. The intended reading of each
instance is `exists r. sl.apply-N(F, x̄, r)` against the
defunctionalized graph theory (`docs/SEMANTICS.md`). The emitted axioms
constrain `defined-apply-N` on named functions: a total function is
defined-apply everywhere on its argument sorts, and an unknown function
`f` satisfies `(defined-f x̄) <=> (defined-apply-N f x̄)`. Every
application site in a body contributes a `defined-apply-N` obligation to
its clause's antecedent, since the applied argument is arbitrary.

Equality between function-sorted terms is rejected by the typing pass
(`sl-t005 function-equality`): the graph theory's function values are
names (intensional), while the typed model's function space is
extensional, and equating them would let the two readings diverge.

## Current limits

- User constructors are monomorphic at `value`; polymorphic user ADTs
  are not yet expressible.
- Programs mixing sorts in one position (a literal and a constructor
  pattern on the same argument) have no typed reading and are rejected.
- `let` is inlined by substitution; pathological duplication is
  accepted. Definedness obligations of a `let` binding are collected
  unconditionally: `let` is strict even when the bound variable is
  unused.
- Any function that applies a function parameter is classified unknown;
  totality relative to the parameter's totality is future work.
