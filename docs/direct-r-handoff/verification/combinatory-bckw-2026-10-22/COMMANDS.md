# BCKW and Knuth-bound focused proof audit

Command:

```sh
bash docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/AUDIT.sh
```

Exit 0, all 19 stages, 2026-10-22 06:36:36–06:37:27 UTC. Exact expanded
commands, per-stage exit/timing ledger, source hashes, report counts and the
recursive kernel inventory are preserved beside this file. Full build output:
`_build/combinatory-bckw-audit.Hukon3`.

- Fresh absolute 23-module build: `/tmp/pts-rk-combinatory-bckw.bnSrlP`.
- Independently archived/rebuilt pristine source:
  `/tmp/pts-rk-combinatory-bckw-pristine.p0tvSU`, revision
  `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- 224 own closed reports; 225 aggregate including unchanged Ranks output.
- Recursive kernel inventory byte-identical to pristine: only unchanged
  `functional_extensionality_dep`; no unsafe fixpoints, assumed positivity,
  type-in-type or new assumptions.
- Original kernel diff, source stability, safety scan and whitespace pass.
- Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Stdlib 9.1.0,
  Equations 1.3.2+9.2. Exact package output is in the full log directory.
- HEAD `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`. No staging, commit or push.

This is the focused development audit, not a full repository CI run. No
failure or timeout occurred in this frozen-source run. The new audit was
prepared with a failing report-count sentinel while sources were changing;
it was set to the frozen count 224 before the script was first executed.

## Dependent basis regression

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  bash docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/dependent/CHECK.sh
```

Exit 0, 06:36:04 UTC; full logs
`/tmp/pts-rk-bckw-dependent-check.3s6E48`. Positive/negative source fixtures,
expanded commands, exact diagnostic logs and exits 0/42/42/42 are preserved
in `dependent/`. The negative exits are required scope errors, not suppressed
compiler failures. See that directory's README for the exact claim boundary
and initial scratch diagnostic failures. These tests do not prove a general
BCKW nondefinability result, native PTS/QIIRT equivalence, or source completeness.
