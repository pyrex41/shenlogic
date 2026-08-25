# 15 Benchmark inventory

**Obligation.** Classify current fixtures against the RESEARCH-PLAN 30-100 bar (mutation / human / history; unique / ambiguous / impossible / out-of-grammar). Publish classifications, not only patches.

**Notes.** First-pass file counts stand: 41 fixtures / 20 goldens / 4 positive recoveries. 41 files are not 41 tasks. No class labels. No mutation / human / history provenance.

**Code.** This branch: `tests/benchmark/tasks.tsv` (9 rows, existing run-all / repair-cli triples only, `origin=neither`). `inversion=yes` on the four template pins. Five reject/prepare specs already in the suite. `make benchmark-inventory` prints 9 / 0 labeled / 4 inversion / 4 recoveries / distance 21.

**Plan.** 1) Do not invent programs to pad to 30. 2) No class labels without a uniqueness, ambiguity, or impossibility witness. 3) Mutation / human / history labels wait for actual provenance.
