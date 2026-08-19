# ShenLogic Lean proofs

This is an independent Lean 4 formalisation supporting the ShenLogic v2 proof
work. It deliberately contains no generated implementation code.

The current model defines exact integer/boolean/data values, first-order
patterns, deterministic pattern matching, expressions, ordered clauses, an
abstract Rule IR derivation relation, and least closed relations. Proved results
include matcher/evaluator/ordered-clause determinism and a generic finite
derivation/least-closure equivalence. Backend lemmas presently establish typed
AST shape and encoding predicates.

The project does not yet prove normalized Shen source-to-Rule translation
adequacy, recursive SCC adequacy for the concrete compiler, solver correctness,
or semantic preservation of the emitted CHC/THF text. Those remain the explicit
obligations in `docs/PROOF-OBLIGATIONS.md`. Build with Lean 4.19.0 and
`lake build`.
