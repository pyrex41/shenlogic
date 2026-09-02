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

## Third-party code: THORN

`third_party/thorn/` carries Mark Tarver's THORN 20 theorem prover and the
handful of Shen S42 standard-library functions it needs, taken from the
public S42 distribution under its BSD licence (see the LICENSE there and
`toolchain.lock`). It is published third-party source, not clean-room
work. Two local edits are marked in place: a prelude supplying S42
library functions absent from the 41.2 kernel, and one datatype rule in
`datatypes.shen` reshaped so the 41.2 Prolog compiler accepts it. Any
further divergence is a documented fork, per docs/THORN-PLAN.md.
