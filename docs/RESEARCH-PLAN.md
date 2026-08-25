# ShenLogic research plan

## Status and thesis

ShenLogic is a paper-worthy research project. The current implementation is
ready to support a workshop paper, short paper, or tool demonstration. A strong
full paper requires a narrower novelty claim, explicit formal results, a larger
benchmark, and comparisons with alternative synthesis strategies.

The recommended central thesis is:

> A generated logical theory can be treated as an editable semantic view.
> Given a projectable edit to that view, a repair system can synthesize a
> bounded, low-cost source change and accept it only when the ordinary forward
> compiler reproduces the edit and the candidate satisfies executable and
> solver-checked contracts.

The strongest prospective technical framing is:

> Partiality-aware, forward-validated repair of recursive functional programs
> from edits to generated logical equations.

This wording is a novelty hypothesis, not yet a priority claim. A systematic
literature review is required before using terms such as “first.”

## The problem

Program-to-logic compilers are normally one-way. Once a user finds and corrects
an error in generated equations, that information is stranded in the logical
artifact: the source program remains wrong.

There are two importantly different inverse problems:

```text
Projectable equation edit                    Arbitrary new axiom
          │                                          │
          ▼                                          ▼
bounded, provenance-aware repair         general program synthesis
often feasible and local                 possibly many-valued or impossible
```

ShenLogic currently addresses the left-hand problem. It does not claim that
arbitrary axioms uniquely determine executable programs.

Its repair architecture is:

```text
source ──forward compiler──▶ logical view
  ▲                              │
  │                              │ edited equations
  │                              ▼
  └── ranked typed candidates ◀── synthesis
               │
               ▼
      forward retranslation
       + examples + Z3
               │
               ▼
         reviewable patch
```

The ordinary compiler remains the acceptance oracle. The synthesis engine is
allowed to propose candidates, but it does not define a second semantics for
the source language.

## Current contribution

The implemented system combines the following properties:

1. The edited object is a generated logical theory rather than a failing test
   or a concrete execution result.
2. Unchanged generated scaffolding acts as a provenance and compatibility
   boundary.
3. The existing parser, validator, type checker, and forward translator are
   reused to judge every candidate.
4. Partiality is represented explicitly through graph relations and
   definedness predicates.
5. Recursive, typed functional definitions can be reconstructed as ordinary
   Shen source.
6. Ground examples, negative examples, quantified graph-safety laws, and
   minimal structural change coexist in one acceptance pipeline.
7. Candidate ordering is deterministic, and the default result is a reviewable
   unified diff.
8. A failed search, rejected law, solver error, missing solver, or inconclusive
   solver result cannot write the source file.
9. The portable implementation uses Shen's integrated Prolog and is exercised
   across shen-go, shen-cl, and shen-lua.

These properties make a credible systems contribution. For a full research
paper, they must be distilled into one primary technical claim rather than
presented as an undifferentiated collection of features.

## Relationship to prior work

The project lies at the intersection of several established areas.

### Bidirectional evaluation and output-directed programming

Bidirectional evaluation propagates edits to concrete program outputs back to
functional source. Sketch-n-Sketch applies this idea to generated HTML and
defines evaluation-update rules plus custom lenses. ShenLogic differs in the
level at which the edit occurs: its view is a compiler-generated logical
theory, not an evaluated output value.

Reference: Mikaël Mayer, Viktor Kunčak, and Ravi Chugh,
[“Bidirectional Evaluation with Direct Manipulation”](https://arxiv.org/abs/1809.04209),
OOPSLA 2018.

### Syntax- and semantics-guided synthesis

SyGuS formulates synthesis using a grammar of candidate programs plus semantic
constraints in a background theory. SemGuS generalizes this by accepting
user-defined operational semantics and compiling synthesis questions to
constrained Horn clauses, including recursive settings and some
unrealizability results.

References:

- [Syntax-Guided Synthesis](https://sygus.org/).
- Jinwoo Kim, Qinheping Hu, Loris D'Antoni, and Thomas Reps,
  [“Semantics-Guided Synthesis”](https://popl21.sigplan.org/details/POPL-2021-research-papers/30/Semantics-Guided-Synthesis),
  POPL 2021.

### Quantitative and automated program repair

Automated repair already distinguishes generate-and-validate and
synthesis-based architectures. Quantitative repair also shows that a smallest
syntactic change need not be the closest semantic change. ShenLogic's current
tree-edit cost is therefore a baseline objective, not the final answer to
repair quality.

Reference: Loris D'Antoni, Roopsha Samanta, and Rishabh Singh,
[“Qlose: Program Repair with Quantitative Objectives”](https://www.microsoft.com/en-us/research/publication/qlose-program-repair-with-quantiative-objectives/),
CAV 2016.

### Relational synthesis and inversion

Relational synthesis can generate programs that jointly satisfy relational
specifications and explicitly includes program inversion as an application.
The Relish evaluation used non-recursive DSLs, leaving recursion, richer
binding, and more complex quantified specifications as limitations relevant to
ShenLogic's direction.

Reference: Yuepeng Wang, Xinyu Wang, and Isil Dillig,
[“Relational Program Synthesis”](https://www.cs.utexas.edu/~isil/relational-synthesis.pdf),
OOPSLA 2018.

### Recursive functional synthesis

Termination, useful search structure, recursion schemes, and the synthesis of
recursive functional programs remain active research areas. ShenLogic's
explicit graph and definedness semantics give it a natural point of contact
with this work.

Reference: Hangyeol Cho and Woosuk Lee,
[“Inductive Synthesis of Structurally Recursive Functional Programs from
Non-Recursive Expressions”](https://doi.org/10.1017/s0956796825100063),
Journal of Functional Programming 2025.

### Trustworthy automated programming

Recent program-repair discussions identify trustworthy evidence, accepted
benchmarks, evaluation criteria, and developer adoption as major open
challenges. ShenLogic's forward-validation and fail-closed design are directly
relevant, but require empirical evaluation rather than architectural argument
alone.

Reference: Claire Le Goues, Michael Pradel, Abhik Roychoudhury, and Shin Hwei
Tan, [“Automated Programming and Program Repair”](https://drops.dagstuhl.de/storage/04dagstuhl-reports/volume14/issue10/24431/html/DagRep.14.10.39/DagRep.14.10.39.html),
Dagstuhl Seminar 24431 report, 2025.

## Recommended paper narrative

The recommended first full-paper narrative is:

### Partiality-aware logical-view repair

Research question:

> When the source language contains divergence and partial functions, what
> round-trip laws should relate source code, generated equations, definedness
> predicates, and repaired source?

This focus differentiates ShenLogic from systems that update concrete total
outputs or repair code only against tests. It also exposes a genuine semantic
problem: two programs may agree on returned values while differing on where
they terminate.

The paper should make the following distinctions explicit:

- denotation versus termination;
- undefined behavior versus divergence;
- equations about defined calls versus accidental totalization;
- a local projectable edit versus an arbitrary global axiom;
- syntactic minimality versus behavioral preservation;
- executable evidence versus an end-to-end compiler proof.

Potential titles include:

- “Editing the Logic, Repairing the Program”
- “From Equations Back to Programs”
- “ShenLogic: Forward-Validated Repair from Editable Logical Views”
- “Partiality-Aware Round-Trip Repair for Recursive Functional Programs”
- “Not Quite Running Prolog Backwards”

The last title is suitable for a talk. One of the more descriptive titles is
preferable for a paper.

## Alternative paper narratives

### Ambiguity-aware repair

Treat the many-valued inverse as the user interaction model rather than a
failure of the implementation. Preserve a version space of surviving repairs,
cluster semantically equivalent candidates, and synthesize inputs that
distinguish the remaining classes. The user answers one targeted question at a
time until a preferred repair is determined.

### Proof-carrying repair

Turn each successful source patch into an independently checkable evidence
bundle recording:

- the projectable logic edit;
- the source span and AST changes;
- the forward-retranslation equality;
- the ground evaluations performed;
- the solver query and result;
- the ranking calculation;
- the preservation of unaffected definitions.

This direction becomes a formal-methods paper if the repair relation and
certificate checker are mechanized and the trusted computing base is made
precise.

### Trusted neural repair

Use an LLM as a proposal generator while keeping ShenLogic as the acceptance
boundary. Compare LLM-only repair, bounded symbolic search, and a hybrid in
which neural proposals seed or prioritize a formally checked search.

The contribution must be the measured hybrid architecture, not the fact that
an LLM participated in implementing the tool.

### Portable relational repair

Study whether one relational repair implementation behaves consistently
across independent Shen hosts. This could include differential testing of
candidate enumeration, canonical ranking, serialization, solver-query
generation, and failure modes. It is likely better as a tool, experience, or
functional-programming paper than as the primary PL contribution.

## Open research problems

### 1. Round-trip laws for a partial, many-valued inverse

Classical lenses suggest useful laws, but repair is partial and may return many
programs. Candidate laws include:

- **Consistency:** forwarding an accepted repair reproduces the edited view.
- **Stability:** an unchanged view does not induce an arbitrary source change.
- **Complement preservation:** non-editable scaffolding and unrelated source
  definitions remain unchanged.
- **Bounded minimality:** the returned candidate is lowest cost among the
  enumerated survivors.
- **Failure honesty:** absence of a candidate is distinguished from search
  exhaustion and proven unrealizability.

The appropriate mathematical object may be a partial relational lens or a
version-space-valued update relation rather than an ordinary deterministic
lens.

### 2. Repairing definedness and termination domains

The current system freezes generated definedness scaffolding. A larger system
should support intentional edits to termination domains while preventing
accidental totalization.

Questions include:

- Can source code and a termination argument be synthesized together?
- How should a user request that a function become total on a larger domain?
- Can the system preserve divergence outside the edited domain?
- What semantic distance compares two partial programs?
- Can counterexamples explain whether a failed law comes from a wrong result
  or a missing terminating derivation?

### 3. Multiple repairs and active disambiguation

Instead of emitting one candidate, expose all relevant semantic classes within
the search bound. Generate distinguishing examples automatically, ask the user
for the desired result, and use that answer to refine the version space.

Important subproblems are equivalence checking, compact version-space
representation, counterexample generation, and candidate explanations.

### 4. Whole-program and mutually recursive repair

Extend the unit of repair from one definition to several functions in a
strongly connected component. This raises questions about simultaneous
least-fixed-point semantics, coordinated edits, recursion-scheme synthesis,
termination, and multi-function cost models.

### 5. Specification debugging and unrealizability

An arbitrary theory edit may have no implementation. A useful system should
distinguish:

- no candidate within the current bound;
- no candidate within the current grammar;
- an internally inconsistent contract;
- a realizable theory whose implementation needs unsupported language
  features;
- a genuinely unrealizable synthesis problem.

Desired explanations include unsatisfiable cores, minimal edits to retract,
closest realizable theories, and independently checkable no-repair
certificates.

### 6. Semantic repair distance

Tree-edit distance is deterministic and understandable, but may prefer a small
patch that changes behavior dramatically. Investigate objectives based on:

- preservation of the original graph relation;
- trace or domain inclusion;
- unchanged outputs outside the edited region;
- preservation of termination behavior;
- source readability and idiomatic structure;
- weighted combinations of semantic and syntactic distance.

### 7. Richer language fragments

Research extensions include:

- polymorphic algebraic data types;
- higher-order repair rather than only higher-order forward translation;
- synthesis of local bindings and helper functions;
- effects and effect handlers;
- exceptions and explicit error values;
- nondeterminism and relational results;
- richer numeric theories;
- function-valued results and partial application.

Each extension should come with an explicit logical interpretation rather than
being admitted through unchecked syntax generation.

### 8. Incremental provenance

The current preamble equality check gives a coarse provenance boundary. A
fine-grained system could record which source clause, guard, or expression
produced every generated formula and use that information for localization,
incremental recompilation, search pruning, and explanations.

### 9. Solver-independent evidence

Z3 is currently an external decision point for quantified laws. Investigate
proof-producing CHC workflows, replayable certificates, multiple-solver
cross-checking, and smaller independently verified checkers.

### 10. Human and AI interaction

Study how users understand and trust repairs when shown:

- a source diff alone;
- a diff plus the edited logical equations;
- distinguishing counterexamples;
- a compact proof/evidence report;
- one candidate versus a small ranked set.

The goal is not merely higher acceptance. It is calibrated trust: users should
accept correct repairs and reject under-specified or misleading ones.

## Flagship demonstration

Factorial is useful as a smoke test but too small to carry the research story.
The flagship demonstration should combine ordered clauses, recursion,
partiality, and ambiguity.

Candidate domains include:

- an ordered access-control policy;
- a bracketed pricing or tax policy;
- a partial lookup or parser;
- a recursive tree transformation;
- a mutually recursive classifier;
- a small symbolic evaluator.

A strong live sequence is:

1. Show a readable source definition and its generated TSL equations.
2. Edit one result equation and one applicability condition.
3. Ask ShenLogic for repairs and show multiple candidates.
4. Add a distinguishing example or law.
5. Preview the newly selected minimal patch.
6. Apply it and regenerate the same theory.
7. Replace the law with a false universal claim and demonstrate that the
   source remains byte-identical.
8. Point out the function's definedness domain and explain why it cannot be
   silently changed by an equation edit.

## Formal development plan

Define a repair problem using:

- source program `P`;
- forward translation `F`;
- original view `L = F(P)`;
- edited view `L'`;
- repair contract `C`;
- candidate grammar `G`;
- search bound `B`;
- cost function `d(P, P')`.

The repair relation should state that `P'` is acceptable when:

1. `P'` is in the typed candidate grammar induced by `P`, `L'`, and `G`.
2. The non-editable projection of `F(P')` equals that of `L`.
3. The editable projection of `F(P')` equals that of `L'`, modulo the stated
   alpha-equivalence.
4. Ground constraints in `C` evaluate as required within their fuel bound.
5. Every supported law in `C` has no reachable bad state, relative to the CHC
   lowering.
6. Replacing the selected source span yields a file that re-parses to the same
   normalized candidate.

Target metatheory:

- **Repair soundness:** every returned program satisfies the acceptance
  relation.
- **Bounded completeness:** every candidate in the declared finite search
  space is considered or pruned by a proved-equivalent rule.
- **Optimality:** the selected program minimizes the declared cost among
  accepted candidates in that search space.
- **Non-interference:** unaffected source regions and generated scaffolding are
  preserved.
- **Write safety:** no failing or inconclusive result authorizes a source
  mutation.
- **Law-lowering soundness:** CHC bad-state reachability corresponds to a
  terminating counterexample in the supported law fragment.

The final theorem must state its assumptions. In particular, solver success
does not by itself establish the correctness of the source-to-CHC compiler.

## Benchmark plan

The current fixtures establish feasibility but are insufficient for a full
paper. Build a public benchmark with at least 30–100 tasks spanning:

- literal, variable, wildcard, repeated-variable, list, and constructor
  patterns;
- clause insertion, deletion, and reordering;
- guard changes;
- expression and recursive-call changes;
- direct and mutual recursion;
- total and partial functions;
- ground-only and quantified contracts;
- unique, ambiguous, impossible, and out-of-grammar edits.

Use at least three sources of tasks:

1. **Mutation-derived tasks.** Mutate real source programs, translate both
   versions, and ask the system to recover the hidden source change.
2. **Human-authored theory edits.** Edit logic without first constructing the
   repaired source, avoiding a completely circular benchmark.
3. **History-derived tasks.** When possible, use real before/after functional
   program commits and derive the corresponding logical changes.

Mutation-derived exact recovery is useful but should not be the sole evidence:
the intended repaired program is already known to be representable by the
forward compiler.

## Research questions and metrics

| Research question | Measurements |
| --- | --- |
| Can logical edits be projected? | Repair rate by edit and language-feature class |
| Are returned patches acceptable? | Forward equality, contracts, semantic or manual assessment |
| How ambiguous is inversion? | Candidate count and semantic equivalence classes |
| Does ranking find intended repairs? | Exact recovery, top-k recovery, semantic agreement |
| What prevents false repairs? | Acceptance-pipeline ablations |
| Does the method scale? | Runtime, candidates explored, memory, solver time |
| How important is provenance? | Search and false-candidate changes without provenance pruning |
| Do laws reduce overfitting? | Survivors under examples alone versus examples plus laws |
| Which search backend works best? | Prolog, naive enumeration, MiniZinc, SyGuS/SemGuS, and hybrids |
| Do explanations help users? | Correct acceptance/rejection, time, confidence calibration |

Report failures by category rather than only aggregate success rate. Important
categories include malformed view, edited scaffolding, unsupported inversion,
type rejection, contract rejection, bound exhaustion, solver counterexample,
solver unknown, and source-reread mismatch.

## Baselines and ablations

Potential baselines:

- naive typed AST enumeration;
- the existing bounded Prolog enumerator;
- a MiniZinc model for structural decisions and optimization;
- a SyGuS encoding for expression-level repairs;
- a SemGuS encoding for recursive operational semantics;
- an LLM prompted with source, logic edit, and contract;
- an LLM whose proposals must pass ShenLogic validation.

Important ablations:

- no unchanged-preamble/provenance check;
- no forward retranslation check;
- examples without quantified laws;
- laws without ground examples;
- syntactic cost versus semantic distance;
- first survivor versus deterministic ranking;
- whole-program regeneration versus local source splice and reread;
- one host versus differential execution across three Shen hosts.

Sketch-n-Sketch is an important conceptual comparison but not necessarily a
direct experimental baseline because it accepts edits to execution outputs
rather than logical theories.

## MiniZinc's role

MiniZinc is useful if structural choices, global constraints, and minimal-edit
optimization become the search bottleneck. It should remain a proposal engine,
not an alternative semantic authority.

Useful experiments include:

- encoding clause presence, order, pattern constructors, guard selection, and
  cost as finite decision variables;
- comparing solution order and runtime with Prolog enumeration;
- adding lexicographic objectives for edit size, semantic preservation, and
  canonical tie-breaking;
- using solver output only to construct candidates that are then checked by
  the ordinary ShenLogic pipeline.

Adding MiniZinc alone is not a sufficient paper contribution. It is valuable
when it enables a principled search comparison or a substantially richer
candidate grammar.

## Claude/Fable and other AI assistance

AI assistance is part of the development process, not automatically part of
the scientific novelty.

For an academic artifact:

- preserve prompt/session provenance where practical;
- record which design and implementation decisions were human-reviewed;
- retain adversarial tests and failed approaches;
- disclose AI assistance according to the target venue's current policy;
- avoid presenting model-generated volume as evidence of correctness;
- make reproducible tests, specifications, proofs, and artifacts the evidence.

For a general-audience talk, “built through intensive human–AI collaboration”
is an interesting secondary hook. The primary hook should remain the editable
logic and trusted repair architecture.

A separate empirical paper could study Claude or another model as a candidate
generator inside the checked pipeline. That requires a controlled comparison,
fixed prompts and models, repeat trials, and a benchmark; anecdotal success
while building ShenLogic is not sufficient.

## Presentation plan

### One sentence

> ShenLogic lets a programmer edit generated equations and synthesizes the
> lowest-cost typed source repair within a bounded grammar, accepting it only
> when the forward compiler reproduces the edit and the repair passes examples
> and solver-checked laws.

### Thirty-second version

Logic-producing compilers usually create a dead end: if a human corrects the
generated theory, the source does not change. ShenLogic makes one part of that
theory an editable view. It reconstructs possible source definitions, ranks
them by change cost, and sends every candidate through the existing compiler,
evaluator, and Z3 checks. The result is a source diff, not an unreviewable model
patch. The inverse may be ambiguous or empty, and the system reports those
cases rather than pretending every axiom is a program.

### Suggested talk structure

1. **The dead-end artifact:** a correct logic edit that cannot flow back.
2. **Two inverse problems:** projectable update versus arbitrary synthesis.
3. **Live repair:** equation edit, candidate patch, forward reproduction.
4. **Ambiguity:** multiple programs can realize the same equations.
5. **Partiality:** result equality is not termination-domain equality.
6. **Trust boundary:** compiler, evaluator, law query, and write barrier.
7. **Evidence:** regressions, three hosts, backends, and negative tests.
8. **Limits:** current grammar, graph-safety laws, and open proof obligations.
9. **Research agenda:** definedness repair, active disambiguation, and
   proof-carrying patches.

### Claims to avoid

Do not describe the current system as:

- a fully bidirectional compiler;
- a general inverse for arbitrary axioms;
- an end-to-end verified repair engine;
- proof that Z3 establishes total program correctness;
- evidence that pure Prolog programs are automatically reversible;
- globally minimal synthesis outside the declared candidate grammar and
  bounds.

Precise limitations strengthen rather than weaken the central claim.

## Publication ladder

### Immediate

The existing artifact can support a workshop paper, short paper, or tool
demonstration centered on the architecture, executable example, and research
agenda.

Potential communities include bidirectional transformations, synthesis,
partial evaluation and program manipulation, functional programming, and
logic programming.

### Full paper

A full paper should follow after the formal repair judgment, soundness result,
public benchmark, baseline comparison, and scaling evaluation are complete.

Venue fit depends on the chosen contribution:

- OOPSLA or PLDI for bidirectional semantics and language design;
- CAV, TACAS, IJCAR, or CADE for CHCs, synthesis, unrealizability, and
  certification;
- ASE, FSE, or ICSE for automated-repair evaluation and developer workflow;
- IFL, TFP, PEPM, SLE, BX, or SYNT for earlier systems and ideas.

Deadlines and AI-use policies must be checked against the current call for the
specific submission year.

## Phased execution plan

### Phase 1: Freeze and characterize the artifact

- Tag the current bounded repair implementation.
- Record its exact supported grammar and failure taxonomy.
- Add machine-readable benchmark results.
- Archive the toolchain and artifact with a persistent release identifier.
- Write a short architecture or workshop paper without overstating novelty.

### Phase 2: Formalize the repair relation

- Define the editable projection and alpha-equivalence precisely.
- State consistency, non-interference, bounded completeness, and optimality.
- Prove the core properties on paper or in Lean.
- Specify all assumptions made by law lowering and the forward compiler.

### Phase 3: Build the benchmark

- Add mutation-, human-, and history-derived tasks.
- Include total, partial, recursive, ambiguous, and impossible cases.
- Publish expected classifications, not only expected patches.
- Add deterministic resource limits and result capture.

### Phase 4: Compare search strategies

- Establish naive enumeration and current Prolog baselines.
- Add MiniZinc or SyGuS where the candidate grammar maps naturally.
- Measure search cost independently of forward-validation cost.
- Add semantic-distance objectives and candidate equivalence classes.

### Phase 5: Add interactive ambiguity handling

- Return a ranked candidate set or compact version space.
- Generate distinguishing examples or counterexamples.
- Record user choices as new contract clauses.
- Evaluate convergence and user comprehension.

### Phase 6: Extend partiality and certification

- Permit controlled definedness edits.
- Synthesize or check termination evidence.
- Produce replayable repair certificates.
- Minimize and document the trusted computing base.

## Success criteria

The project is ready for a strong full-paper submission when it can answer all
of the following with evidence:

1. What precise class of logical edits is projectable?
2. What theorem relates an accepted patch to the edited theory?
3. What does the system guarantee about partiality and termination?
4. How complete is search relative to its declared grammar and bounds?
5. How does its ranking compare with syntactic and semantic alternatives?
6. How often is the inverse ambiguous, empty, or outside the grammar?
7. How does performance compare with at least one established synthesis
   formulation?
8. Which acceptance checks prevent otherwise plausible but incorrect repairs?
9. Can independent users understand why a patch was produced or rejected?
10. Can the full artifact and results be reproduced from a clean environment?

## Recommended next move

The first paper should be narrow: editable logical views for partial recursive
functional programs. MiniZinc, SyGuS, and LLMs should be treated as candidate
search backends and experimental comparisons rather than the headline.

The central intellectual object is the round-trip contract: a partial,
many-valued relationship between source and logic that is honest about
ambiguity, divergence, bounded search, and the possibility that no source
program realizes an edit.
