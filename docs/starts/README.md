# Obligation starts

One file per proof obligation. Status as of 24 Aug 2026 first pass.
Do not invent theorems. Next code is the named commit in each file.

| PO | File | First code on disk? |
| --- | --- | --- |
| 1 | 01-patterns.md | yes (`ceb2e5b`) |
| 2 | 02-clauses.md | golden uncommitted → this branch |
| 3 | 03-expressions.md | no Lean Expr extend yet |
| 4 | 04-rules.md | factorial 0/5 compiled-rule witness |
| 5 | 05-leastness.md | v2-mutual graph golden on this branch |
| 6 | 06-thf.md | mutual.thf golden on this branch |
| 7 | 07-definedness.md | `d.shen` on this branch; axioms tautological |
| 8 | 08-apply.md | ho-apply-scc fixture + graph golden on this branch |
| 9 | 09-tsl.md | mutual.tsl.logic on this branch; no Formula AST |
| 10 | 10-projection.md | template sl-checks on this branch |
| 11 | 11-roundtrip.md | splice-retranslate sl-check on this branch |
| 12 | 12-contracts.md | `repair-law-query-shape-true`, `repair-law-query-shape`, three reject sl-checks |
| 13 | 13-search.md | enum/rank sl-checks on this branch |
| 14 | 14-assoc-append.md | characterize only; no replay |
| 15 | 15-benchmark.md | tasks.tsv 9 rows, origin=neither |
