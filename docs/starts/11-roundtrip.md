# PO11 Round-trip

**Obligation.** Accepted patch retranslates to unchanged preamble + edited equations; splice re-parses to the same candidate.

**Notes.** Runtime gates exist. Retranslation was in-memory; composition `translate(splice)=edited view` was untested.

**Code.** This branch: `sl-written-retranslate?` + `repair-splice-retranslates-factorial`. Temp path gitignored.

**Plan.** 1) Mirror after `--write` in `tests/repair-cli.sh`. 2) No Lean repair relation. 3) Docs disagree (alpha vs byte-exact); leave as a later note.
