# Canonical intermediate representation

The translator records three representations. The source AST preserves Shen
forms and clause order. A decision-tree artifact records matching, guards, and
fallback for review and certification. The Rule compiler independently lowers
the same normalized AST into terminal graph paths and groups recursive calls
by strongly connected component. The certificate checker recomputes both
artifacts, so neither can silently drift from normalized source.

## `.slir` v2

The serialized form is a tagged S-expression beginning with:

```text
(shenlogic-ir 2 (theory VALUE-SIGNATURE RELATIONS RULES SCCS NAME-MAP))
```

Every list is ordered. Function, clause, rule, variable, and SCC identifiers
are derived from source order and traversal counters, never from host hash
iteration. A serializer round trip must preserve the byte-canonical form.

The normalized AST is the trust boundary between source and logic. No backend
sees raw source syntax after this point. Values are closed and tagged:
`v-int`, `v-true`, `v-false`, `v-symbol`, `v-string`, and `v-ctor` nodes;
nil/cons are distinguished constructor tags. This prevents host-language
equality or string quoting from changing the model.

The frozen v2 theory shape is
`[theory ValueSignature Relations Rules SCCs NameMap]`. Relations retain the
shape `(relation NAME ARG-SORTS RESULT-SORT)`. Each rule has nine fields:
`(rule ID FUNCTION CLAUSE PATH ARGS BOUND PREMISES RESULT)`. SCC entries have
the shape `(scc NAMES)` and `NameMap` records stable source/backend names.
Diagnostics retain stable form and clause indexes.

## Backend discipline

`surface` is a review rendering and is not used as the semantic proof object.
`graph` is the readable least-graph specification. Constructor patterns lower
to explicit `decompose`/`not-tag` paths, and ordered fallback is represented
by those paths rather than opaque host matching. `chc` emits SMT-LIB
fixedpoint rules over the closed Value algebra, and a solver's `unknown`
is never treated as a proof. `thf` emits a full-model TPTP typed
higher-order specification, including simultaneous relation quantifiers and
leastness obligations required by mutual recursion. `tsl` emits the typed
second-order equational theory of [TSL-LOGIC.md](TSL-LOGIC.md): constructor
axioms, definedness predicates for functions not proven total, and guarded
clause equations. It consumes the normalized program (declared signatures
are required) alongside the theory, and is not yet part of the certificate
bundle. `lpc` re-renders checker-proven-total, comparison-free tsl
theories in the prop grammar of Tarver's LPC proof assistant; like tsl it
consumes the normalized program and is not a certificate artifact.
`prove` is not a translation format: it assembles a solver query from tsl
equations (via the same `tsl.equation-formula` construction the tsl
renderer uses), an instantiated induction axiom, and a negated
conjecture.

Backends reject unresolved polymorphism, unknown calls, unsupported
arithmetic, post-cleaning name collisions, and constructs outside the v2
capability matrix. No backend silently changes the operational meaning of
the decision tree.

Programs with function parameters additively extend the theory within the
frozen v2 grammar: normalized bodies may contain `[e-apply Var Args]`
nodes, and the compiled theory then contains `sl.apply-N` relations and
`sl.apply-N_f` rules (one per defined arity-N function). Definition names
beginning with `sl.apply-` are reserved. No `shenlogic-ir` version bump is
involved, and programs without applications compile byte-identically.
