# Canonical intermediate representation

The translator has two internal stages. The source AST preserves Shen forms
and clause order. The decision tree makes matching, guard evaluation, strict
calls, and fallback explicit. The logical Rule IR then lowers each terminal
path into graph rules and groups recursive calls by strongly connected
component.

## `.slir` v1

The serialized form is a tagged S-expression beginning with:

```text
(shenlogic-ir 1 (theory DECLARATIONS RULES SCCS))
```

Every list is ordered. Function, clause, rule, variable, and SCC identifiers
are derived from source order and traversal counters, never from host hash
iteration. A serializer round trip must preserve the byte-canonical form.

Declarations have the shape `(relation NAME ARG-SORTS RESULT-SORT)`. Rules
have the shape `(rule ID FUNCTION ARGS BOUND PREMISES RESULT)`. SCC entries
have the shape `(scc NAMES)`. Diagnostics retain stable form and clause
indexes.

## Backend discipline

`surface` is a review rendering and is not used as the semantic proof object.
`graph` is the readable least-graph specification. It retains explicit
`match` and `not-applicable` premises for constructor patterns and ordered
fallback. `chc` emits SMT-LIB fixedpoint rules for the integer Horn profile;
`unknown` is never treated as a proof. `thf` emits TPTP typed higher-order
formulas and preserves the simultaneous relation quantifiers required by
mutual recursion for the same supported profile.

Backends reject unresolved polymorphism, unknown calls, unsupported arithmetic,
and constructs outside the v1 capability matrix. No backend silently changes
the operational meaning of the decision tree.
