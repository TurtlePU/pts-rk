# Self-interpreter allocation, pruning and uniformity improvements

21 October 2026; parent `f5fdac0c1deeeb43d6138f8de3178224b79d42a4`.
The user requested addressing obligations from the current and earlier
research notes, explicitly excluding CPS formalization. The scope and
remaining research questions are in
[OBLIGATIONS.md](../../../../theories/self_interpreter/OBLIGATIONS.md).
After verification, the user requested commit and push. The enclosing scoped
publication commit includes this continuation, the note/PDF and evidence.

## Changed construction

- `SizedSyntaxEnumeration`: direct exact-node generation, completeness and
  agreement with the old depth/filter specification, exact cardinalities.
- Both checked equality allocators: carrier/operand/prefix checks before
  candidate expansion, with iff agreement with reference acceptance.
- `SourcePruning`: original-judgment-preserving reflexive conversion removal,
  idempotence, size/repair monotonicity and padding invariance. The final
  closed quoter invokes this before computing its budget.
- `QuotationCost`: exact plan length for the actual recursive quoter;
  the final entry point uses the pruned derivation's count.
- `PlanNonuniformity`: fixed-rank sources with actual plan length `3*h`,
  and fixed-judgment conversion detours with length `7*h`. Neither is an
  impossibility theorem for arbitrary alternative interpreters.
- Audit/Dune registration, paper/PDF, README and obligation ledger.

The original kernel, normalization development, arithmetic and frozen ZFC
sources are unchanged. Unrelated existing worktree edits remain untouched.

## Commands and development attempts

Commands run from `/Users/akuklev/air/pts-rk`, unless stated otherwise:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --display=short --no-buffer -j 2 TARGET
```

Raw logs are retained in ignored
`_build/self-interpreter-improvements-2026-10-21`. Attempts:

| Log series | Result |
| --- | --- |
| `sized-01`–`03` | Compiler errors while developing syntax completeness |
| `sized-04` | Exit 0, completeness/agreement proved |
| `sized-05`–`07` | Compiler errors in list-length lemmas and initially incorrect finite expected count; corrected to 68 |
| `integration-01` | Exit 0, direct enumerator integrated through `FullDependentInterpreter.vo` |
| `prune-01`, `prune-02` | Unreduced dependent equality transport; `02` is a diagnostic whose final shell `tail` exited 0 despite the compiler error |
| `prune-03` | Exit 0, all pruning theorems |
| `filter-01` | Exit 0, endpoint prefiltering |
| `context-filter-01` | Ambiguous temporary versus cached module path |
| `context-filter-02`–`04` | Compiler errors in membership/dependent constructor equality proofs |
| `context-filter-05` | Exit 0, complete contextual prefiltering |
| `cost-01` | Incorrect logical name on a manually compiled temporary module |
| `cost-02`, `cost-03` | Compiler errors in the initial monolithic plan-length proof |
| `cost-04` | Explicitly terminated compiler after excessive proof expansion; Dune exit 1, worker signal TERM |
| `integration-02` | Full interpreter passes; preliminary cost proof fails, aggregate exit 1 |
| `cost-05`, `cost-06` | Compiler errors in the modular count proof |
| `cost-07` | Exit 0, actual recursive plan-length theorem |
| `nonuniform-01`–`04` | Compiler errors in explicit rank/inversion proofs |
| `nonuniform-05` | Exit 0, fixed-rank family |
| `cost-08` | Exit 0, final fixed-rank and fixed-judgment actual-plan theorems |

Manual scoped checks used `rocq compile`, the existing `_build/default`
logical paths, and an output `.vo` in the raw evidence directory. These
prototype artifacts are not used in the final fresh audit. Some manual runs
warn about masking a short module name; the final Dune logical names are
`PTSrk.SelfInterpreter.*`. The existing nested-directory remapping warnings
are retained. No guard or universe check was disabled.

## Extracted execution

`Execution.v` extracts the ACTUAL final quotation path, not a model of it.
It checks normality of the raw term, represented type and faithful program.
Mode 0 quotes a sort, mode 1 a lambda and mode 2 an application. Mode 3
enumerates actual syntax lists at sizes 5 and 7.

From the raw evidence directory, using the environment above:

```sh
timeout 180 opam exec -- rocq compile \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories PTSrk \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  -o Execution.vo /Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/self-interpreter-improvements-2026-10-21/Execution.v
timeout 120 opam exec -- ocamlc -w -a -c execution.mli
timeout 120 opam exec -- ocamlc -w -a -c execution.ml
timeout 120 opam exec -- ocamlc -w -a -I . execution.cmo \
  /Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/self-interpreter-improvements-2026-10-21/main.ml -o execute
/usr/bin/time -l timeout 30 ./execute MODE
```

Extraction and OCaml compilation exit 0 (`extract-01`, `ocaml-01`). Standard
opaque-proof extraction warnings are preserved; no source axiom or unsafe
cast is introduced. Standard OCaml proof erasure is not direct Rocq record
evaluation. Generated OCaml and compiler objects remain in ignored evidence.

| Mode / log | Exit | Result / elapsed | Peak RSS |
| --- | --- | --- | --- |
| 0 / `run-sort` | 0 | `true true true`, 0.45 s | 5,996,544 bytes |
| 3 / `run-enumeration` | 0 | `size5=68 size7=1209`, 0.02 s | 4,341,760 bytes |
| 1 / `run-lambda` | 124 | timeout, 30.02 s, no completed normality result | 7,454,720 bytes |
| 2 / `run-application` | 124 | timeout, 30.02 s, no completed normality result | 7,487,488 bytes |

These are observations at a stated cap, not nontermination proofs or
end-to-end speedup claims. Subsequent additions to `PlanNonuniformity` are
proof-only detour examples and are not on the extracted execution path.

## Fresh verification

The executable `AUDIT.sh` records exact command lines, timestamps, exit
codes and logs for a fresh absolute Dune directory:
`/tmp/pts-rk-self-improvements-audit.vjkEgS`. It builds the aggregate audit,
recursively checks both core and self-interpreter libraries, compares the
core assumption inventory to retained pristine-upstream output, checks the
unchanged original sources, and checks source-manifest stability.

The completed older Dune cache
`/tmp/pts-rk-self-open-telescope-audit-retry.cdzdRH` was validated and cleaned
using `opam exec -- dune clean --build-dir=...`, reclaiming approximately
625 MiB. Its successful audit logs remain in the separate retained evidence;
its Dune trace was copied to `previous-audit-trace.csexp` before cleanup.
Only regenerable build products were removed.

The unchanged full local CI driver is run with:

```sh
export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-improvements-2026-10-21/ci
export DIRECT_R_JOBS=1
export DIRECT_R_STAGE_SECONDS=1200
bash tools/check-local-ci.sh
```

Fresh aggregate build: exit 0, 08:31:28–08:39:22 UTC. It emits 2,288 closed
reports: 2,287 self-interpreter reports and the unchanged upstream
`Ranks.strong_normalization` report. This equals the source Print inventory
plus that single upstream declaration. Core recursive checking exits 0;
aggregate recursive checking exits 0, 08:39:29–08:48:32 UTC. All own audited
endpoint assumptions are closed. The aggregate loaded inventory has only
the unchanged upstream `functional_extensionality_dep`, with no type-in-type,
unsafe fixpoint or assumed positivity. The core inventory is byte-identical
to retained pristine-upstream output; complete CI also rebuilds pristine upstream.

The initial audit driver exits 1 AFTER all compilation/kernel/pristine stages
pass: its original-source comparison mistakenly uses a Git wildcard matching
descendant developments and also includes historical README/PDF additions.
`original-sources.log` preserves that diagnostic diff. The corrected runner
uses `:(glob)` for immediate original `.v` files and explicitly compares
normalization/ZFC `.v` and Dune files. `FINAL-CHECKS.sh` independently performs
the corrected comparisons and source stability/count/status checks; it exits
0. All 112 source/Dune manifest entries are unchanged across fresh verification.
This was a validation-script scope error, not a failed proof or waived check.

Full local CI/actionlint exits 0: all 226 stages PASS, result `complete`.
The shared CI includes unrelated unpublished BZC stages; no publication of
those changes or hosted CI run is implied. No final proof build/kernel stage
fails or times out. The separate 30-second execution timeouts remain as reported.

Pinned versions: OCaml 4.14.2, Dune 3.23.1, Rocq 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2; full installed-package versions are in `versions.log`.
At verification time no Git/index mutation had occurred. The final whitespace
check passes and the index was empty on the original parent. These are historical
pre-publication checks; FINAL-CHECKS.sh deliberately records that parent.

Selected verified proof-source SHA256:

```text
e394bd308d74c747093bbe686f213c2a68b8e5eb8e49f32836176ec91a804b12  FullDependentInterpreter.v
d4f30f57678ccf176f823ebe85093e917818223d6796960ab24cada2d1f17ae6  SizedSyntaxEnumeration.v
def0a855556bb325e1b6fd12c5e5d1eca7e066a85bbd6c6f3b38997d48bf37c2  SourcePruning.v
9bb087077c36465c5b4322cdccf3818e71367010c67f79fcbd58671d91230f2f  QuotationCost.v
75d4c9d5e14bb2a5b7011ef31224af3a28e63a98922eaf732e38dba4673d8752  PlanNonuniformity.v
```

## Paper

`bash tools/build-self-interpreter-note.sh` exits 0 (`note-01`), fresh
directory `/tmp/pts-rk-self-note.RUYqeO`. The PDF remains 11 pages. PDFKit
text extraction and rendering exit 0; changed pages 5, 6, 8 and 11 were
visually checked. The final TeX log has no overfull/underfull boxes, LaTeX
warnings or missing glyphs. The excerpt stays focused on the final
construction; historical obligation reconciliation is in the separate ledger.

```text
b46abaa0fd8b24643b5d2ebe43b345eb839efc5693d5b5eaf3cf359a9900a49c  PTS-rk_self_interpreter.tex
663cf25ee1527bc64d46f58043ce65173e79af4a2755d983ce68f525a7992810  PTS-rk_self_interpreter.pdf
```
