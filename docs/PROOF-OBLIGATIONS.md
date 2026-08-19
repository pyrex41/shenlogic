# Correctness proof obligations

The Lean project currently proves determinism for its pattern matcher,
expression evaluator, and ordered-clause evaluator. The following are the
remaining adequacy obligations. Let `P` be a program in the supported fragment
and `G_f` the generated graph relation.

1. **Pattern equivalence.** Matching succeeds exactly when the translated
   pattern proposition holds, including repeated variables and free-constructor
   injectivity/disjointness.
2. **Clause priority.** Under total guards, the selected clause is precisely
   the first applicable clause. Guard error or nontermination does not become
   classical false.
3. **Expression soundness/completeness.** Constants, variables, lists, strict
   calls, `if`, `let`, `and`, and `or` agree with their relational rules.
4. **Rule adequacy.** Induction over Shen evaluation derives a graph rule;
   induction over finite least-rule derivations reconstructs Shen evaluation.
5. **Leastness.** SCC rule operators are monotone, and closure plus containment
   in every closed candidate gives the simultaneous least fixed point.
6. **Functionality and definedness.** Deterministic source evaluation implies
   `G_f(args,v₁) ∧ G_f(args,v₂) => v₁ = v₂` and
   `Defined_f(args) <=> exists v. G_f(args,v)`.

Proof development proceeds in that order: patterns, nonrecursive expressions,
ordered clauses, direct recursion, then mutual recursion and leastness. Errors
and effects remain outside v1 until they have explicit logical result objects.
