# Round-trip source repair

`shenlogic repair` turns a bounded edit to generated `tsl` equations back
into a Shen source patch. It is a repair search, not a general inverse of
logic translation: the inverse may contain many programs or no program at
all.

The existing forward compiler remains the arbiter. A candidate is accepted
only when ShenLogic can parse and validate it, forward-translate it, reproduce
the edited equations exactly up to bound-variable renaming, and satisfy the
repair contract.

## Command

```sh
./bin/shenlogic repair FILE \
  --logic EDITED.tsl.logic \
  --spec CONTRACT.spec \
  [--fuel 10000] [--max-candidates 10000] [--max-cost 4] \
  [--optimizer prolog] [--write]
```

The default output is a deterministic unified diff. `--write` replaces only
the target definition after every check succeeds. With quantified laws, the
wrapper prepares the source and Horn query in a temporary directory, asks Z3
to prove the bad-state relation unreachable, and writes the file only after
Z3 returns `unsat`. A `sat` candidate is rejected and the next ranked
candidate is tried. If all candidates are `sat`, or if Z3 returns `unknown`,
fails, or is missing, repair fails closed.

The source file is otherwise preserved byte-for-byte. The repaired definition
is serialized in ShenLogic's canonical multiline form.

Ground-only contracts need no external solver. Contracts containing `law`
forms require Z3; the currently implemented `prolog` optimizer is Shen's
integrated portable Prolog. TPTP4X and MiniZinc are not repair-time
dependencies.

## Review-first workflow

Generate the editable view from the exact source revision to be repaired:

```sh
./bin/shenlogic translate examples/factorial.shen \
  --format tsl -o build/factorial.tsl.logic
```

Edit only the forms below `; equations`, create a versioned contract, and run
without `--write` first. The repository fixtures provide an executable example:

```sh
./bin/shenlogic repair examples/factorial.shen \
  --logic tests/fixtures/repair-factorial.tsl.logic \
  --spec tests/fixtures/repair-factorial.spec
```

After reviewing the diff, repeat with `--write`. On rejection, solver failure,
`unknown`, or search exhaustion, the source is not modified. A successful
write replaces only the selected definition, but canonicalizes that
definition's formatting; keep the source under version control.

## Editable view

The edited input must be a `tsl` artifact produced from the current source.
Only forms after its exact `; equations` marker are projectable. The preamble,
constructor axioms, definedness axioms, and induction/minimality material must
remain unchanged.

Exactly one defined function may have changed equations. Within that
definition, repair may change:

- clause patterns and order;
- guards;
- clause bodies;
- the number of clauses.

The function name, declared signature, and arity remain fixed. Equation edits
must stay in the source-shaped fragment emitted by the `tsl` backend. Arbitrary
new axioms are constraints on synthesis, not syntax from which a source
program can always be recovered.

## Repair contracts

A contract is one versioned Shen form:

```shen
(shenlogic-repair 1
  (expect (factorial 0) 2)
  (forbid (factorial 2) 2)
  (law (all X : number
         ((X = 0) => ((factorial X) = 2)))))
```

`expect` requires a ground expression to terminate with the stated ground
value. `forbid` requires a ground expression to terminate with a different
value; errors and fuel exhaustion do not count as success. `--fuel` bounds
each concrete evaluation.

The first quantified-law fragment supports:

- universal variables of type `number`;
- implications whose conclusion is an equality;
- integer constants, `+`, `-`, and `*` terms;
- `<`, `>`, `<=`, `>=`, equality, conjunction, disjunction, and negation;
- saturated calls to functions in the candidate program.

Other binder domains and existential laws are rejected. This restriction is
intentional: quantifying a boxed CHC `Value` without a sort recognizer would
admit junk values and create spurious counterexamples.

Laws currently have a graph-safety reading. A violation exists when all calls
needed by the antecedent and both sides have graph derivations and the result
values differ. Consequently, a successful law check does not prove that those
calls terminate. Termination must be established separately when a total
correctness claim is required.

An `unsat` result also relies on the soundness of ShenLogic's CHC lowering for
the supported fragment. That lowering and the TSL/graph correspondence still
have open mechanization obligations; see
[PROOF-OBLIGATIONS.md](PROOF-OBLIGATIONS.md). The forward compiler and solver
checks are deliberately kept in the acceptance path, but they are not
presented as a completed proof of compiler correctness.

## Search and validation

The repairer performs these stages:

1. Parse the original and edited equation sections and identify one changed
   function.
2. Invert source-shaped left-hand sides, right-hand sides, patterns, and safe
   antecedent guards into clause templates.
3. Use Shen's portable `defprolog` to enumerate the finite guard choices.
4. Rebuild each typed definition and run the ordinary validation and `tsl`
   translation pipeline.
5. Reject candidates that do not regenerate the edited equations or fail a
   ground contract.
6. Rank survivors by structural source-tree edit cost, then by canonical text
   for deterministic tie-breaking.
7. Re-read the patched source and require it to normalize to the chosen
   candidate.
8. If laws are present, lower their negations to a CHC bad-state query and
   require Z3 to return `unsat`.

`--max-candidates` bounds enumerated guard selections and `--max-cost` bounds
the accepted source-tree edit. Reaching a bound without a survivor reports
`repair-no-candidate`; the tool never silently relaxes a bound.

## API boundary

The portable Shen API is:

```shen
(shenlogic.repair-file File LogicFile SpecFile Fuel MaxCandidates MaxCost)
```

It returns `[ok Name Cost Source Diff]` for ground-only contracts. Because pure
Shen does not launch external processes, this API rejects contracts containing
laws with `repair-law-solver-required`.

The wrapper uses the preparation API:

```shen
(shenlogic.repair-prepare-file
  File LogicFile SpecFile Fuel MaxCandidates MaxCost)
```

It returns `[ok Name Cost Source Diff Query]`; the command-line wrapper owns
the Z3 call and commit barrier.

## MiniZinc boundary

MiniZinc can be useful once the candidate grammar grows enough that structural
choices and minimal-edit ranking dominate runtime. It is not a replacement for
forward translation, evaluation, or Z3 law checking. The `--optimizer` option
is the integration seam; this release implements the portable `prolog`
enumerator and rejects unavailable optimizers. A future MiniZinc adapter can
choose bounded syntax/guard decisions, after which every proposed program must
still pass the same forward-validation pipeline.

This division keeps repair portable by default and prevents an optimization
model from becoming an unsound second semantics for Shen.

## Validation

The project exercises repair at three levels:

```sh
make test          # Shen API, inversion, validation, ranking, and serialization
make repair-check  # CLI preview/write behavior and Z3 fail-closed checks
make test-all      # full host, proof, backend, certificate, and repair workflow
```

`tests/fixtures/repair-*` contains the edited views and contracts used by the
regressions. The CLI check confirms both that a valid patch can be written and
that a false quantified law cannot alter the source.
