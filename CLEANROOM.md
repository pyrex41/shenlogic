# Clean-room record

ShenLogic is an independent implementation based on the public Shen language,
the motivating factorial equations, and the stated goal of a typed
second-order translation. No private Shen2Logic source, binary, generated test
corpus, or unpublished design document was available to this project.

The implementation makes its own explicit choices:

- Shen is both the implementation language and the executable semantic oracle.
- Source forms are read as inert data and normalized into an ordered decision
  tree before logical rules are generated.
- Recursive definitions are represented by evaluation graphs and simultaneous
  leastness conditions.
- Unsupported effects, errors, and partial operations are rejected until
  their operational outcomes have a declared logical model. Function
  parameters gained such a model (defunctionalization by name, see
  docs/SEMANTICS.md) and are now supported; lambdas and partial
  application remain rejected on the same principle.
- Canonical tagged S-expressions provide the versioned intermediate format.

The only compatibility promise currently made is the surface factorial example
described in the project history. All other output and semantics are a proposed
contract, validated by Shen-host conformance tests and Lean proof obligations.
