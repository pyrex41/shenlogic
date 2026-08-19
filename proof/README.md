# ShenLogic Lean proofs

This is an independent Lean 4 formalisation of the verified ShenLogic v1
fragment.  It deliberately contains no generated code or Python dependency.

The current model defines exact integer/boolean/data values, first-order
patterns, deterministic pattern matching, expressions, and ordered clauses.
The proved results are pattern-match determinism and evaluator/ordered-clause
determinism.  Recursive least-fixed-point adequacy and backend correctness are
planned but not yet claimed.  Build with Lean 4.19.0 and `lake build`.
