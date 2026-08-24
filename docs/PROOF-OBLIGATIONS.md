# Correctness proof obligations (ShenLogic 0.2)

The normalized AST and closed `Value` ADT are a proof trust boundary. A
certificate gate checks the generated Rule IR and backend artifact shape before
packaging; this structural gate is not a claim that an SMT/THF solver has
proved the formulas. The CLI command `certify FILE --out DIR` records the
deterministic inputs (`normalized.ast`, `decision.slir`, `theory.slir`,
`theory.graph`, `theory.chc`, `theory.thf`, `certificate`, and `manifest`).

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
6. **Full-model THF.** Typed declarations, constructor axioms, and simultaneous
   SCC leastness quantify over the complete candidate model; no finite sample
   is accepted as a proof.
7. **Functionality and definedness.** Deterministic source evaluation implies
   `G_f(args,v₁) ∧ G_f(args,v₂) => v₁ = v₂` and
   `Defined_f(args) <=> exists v. G_f(args,v)`.
8. **Defunctionalization adequacy.** In the least model,
   `sl.apply-N(s, x̄, r) <=> exists f. s = 'f ∧ f$(x̄, r)` over the
   program's arity-N functions; the SCC over-approximation introduced by
   `sl.apply-N` edges preserves the least fixed point.
9. **tsl correspondence.** Under `defined-f(ā) <=> exists v. f$(ā,v)`
   (and `defined-apply-N(F,x̄) <=> exists r. sl.apply-N(F,x̄,r)`), every
   tsl equation and definedness axiom holds in the least graph model.

Round-trip repair adds executable validation but does not discharge those
semantic obligations. Its remaining proof obligations are:

10. **Projection adequacy.** Inverting a source-shaped edited `tsl` equation
    yields exactly the represented clause candidates, including priority
    exclusions, guards, patterns, and bound-variable renaming.
11. **Forward round-trip.** Candidate acceptance implies that retranslating
    the repaired program reproduces the unchanged preamble and edited equation
    set; the source splice re-parses to that same normalized candidate.
12. **Contract lowering.** Each generated CHC bad-state rule is reachable iff
    the corresponding supported graph-safety law has a terminating
    counterexample. This obligation does not assert termination of law terms.
13. **Search and ranking.** The bounded Prolog enumeration covers the declared
    guard-choice space, and structural edit cost plus canonical tie-breaking
    selects the advertised minimum among enumerated survivors.

Proof development proceeds in that order: patterns, nonrecursive expressions,
ordered clauses, direct recursion, then mutual recursion and leastness. Errors
and effects remain outside v2 until they have explicit logical result objects.
