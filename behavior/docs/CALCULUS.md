# Behavioral calculus v1

## Programs

All serialized programs are inert JSON arrays. Strings are data, never source.
The reference machine uses signed 32-bit integers, booleans, and strings as scalar
store/input values. Arithmetic is checked; failure is explicit. No host clock,
network, randomness, or filesystem read exists in the semantic interpreter.

| Form | Semantics / typing obligation |
|---|---|
| `["skip"]` | Identity |
| `["require", expression]` | Continue only on boolean true |
| `["put", key, expression]` | Store update; declares `write key` |
| `["emit", topic, expression]` | Append an **effect intent**; declares `emit topic` |
| `["consume", resource]` | Remove one available affine resource |
| `["produce", resource]` | Consume `mint:resource` and create resource; cannot duplicate |
| `["seq", first, second]` | Exact intermediate resource context; effect union |
| `["case", condition, yes, no]` | Both branches leave the same resource context |
| `["repeat", count, body]` | Count 0..1000; body preserves resource context |
| `["atomic", body]` | Roll back store/resources/intents/receipts on error or exhaustion |
| `["once", key, body]` | Atomically bind request identity to body and complete input, and commit receipt with effects |

Expressions: `lit`, `get`, `input`, `not`, and binary `+ - * = < <= and or`.
There is no coercion of strings to numbers or numbers to booleans. Reads of absent
bindings fail. Conditions can fail dynamically; ordinary behavioral typing here
is resource/effect typing, not totality or absence-of-runtime-error verification.

State is `[store, resources, effectIntents, receipts]`, where store and inputs are
unique-key association lists. Resource contexts are unique-name lists with an
explicit order; there is no implicit exchange or contraction rule. Initial
resources are assumptions supplied by the caller. They do not authenticate users.

## Proofs

Certificates contain version, rulepack digest, program, input/output contexts,
effects, explicit derivation, and required policy. The rulepack hashes the Shen
calculus, machine, and Lua proof elaborator. A changed policy must itself pass
verification. Unsupported policy keys are rejected.

Primitive proofs check formation and their exact resource/effect transformation.
Sequence proofs supply intermediate context and both effect sets, then require
both subproofs. Branch proofs require both subproofs against the same output
context. Repeat proofs require an invariant resource context. Atomic and once
proofs preserve their body derivations. There is no submitted axiom constructor.

Policy refinements:

- `allowedEffects`: the effect set must be included in this list.
- `retrySafe`: the term must be a `once` scope with an admissible body.
- `proofMethod: "durable-deduplication"`: requires that exact derivation form.
- `preserves: [field, ...]`: the sum of these store fields must be preserved on
  **successful completion**, using symbolic affine execution over both branches.

Affine reasoning handles addition/subtraction and multiplication by an integer
literal. Nonlinear expressions reject. Coefficients are bounded too; overflow
rejects rather than silently changing arithmetic. Requirements are ignored as
constraints by this checker, making it conservative. `once` checks both executing
and already-completed possibilities. These rules do not prove arbitrary quantified
laws, temporal liveness, or loop termination beyond the bounded repeat construct.

The inference/checking separation is executable and covered by forged-proof
regressions. There is not yet a mechanized soundness theorem for this new calculus.
ShenLogic's existing proof obligations remain separate and unchanged.

## Execution, uncertainty, and conformance

Every semantic operation consumes fuel. Exhaustion is `inconclusive`; errors carry
the state reached so far. Atomic/once scopes restore their incoming state on both
error and exhaustion. Non-atomic sequences can expose partial changes.

The abstract `once` primitive assumes state, outbox intentions, and receipt share
one atomic durability boundary. Identical request key, body, and input replay
without effects; a changed payload is a conflict. This says nothing by itself
about exactly-once external delivery. An adapter must establish the boundary and
any consumer-side deduplication separately.

`unknown-commit` creates both pre-commit and post-commit worlds for atomic/once
commands. It is inconclusive for non-atomic commands. Fuel exhaustion never removes
possible worlds. Trace checking advances all alternatives, filters by observations,
and deduplicates equal worlds. Hitting a world bound yields inconclusive.

Observation store fields are checked as a subset; effect records are a subsequence
when incomplete and an exact sequence when complete. A later complete effect
snapshot can resolve an earlier lost response. `compatible` means a reachable
execution explains the supplied finite observations under the observation map;
it is not universal conformance. No matching world yields `violation`.

Observation completeness is an explicit adapter assumption. No numeric confidence
or edge-coverage percentage promotes observations into proof. Return payloads other
than modeled store/effects are not currently compared.

## Extending the logic

Add a datatype for the desired judgment and explicit derivation constructors.
Add a terminating/explicitly bounded checker for any decidable semantic side
conditions. Connect that type through the data-only bridge and policy dispatcher,
then include negative derivations and semantics tests. Updating rules changes the
rulepack digest and invalidates old certificates.

For general proofs, use ShenLogic's generated theories, THORN, or another prover
as a proof producer. There is intentionally no route that admits an arbitrary
prover's `true` as a new behavioral axiom. THORN certificate normalization and
independent replay are not implemented in this package yet.
