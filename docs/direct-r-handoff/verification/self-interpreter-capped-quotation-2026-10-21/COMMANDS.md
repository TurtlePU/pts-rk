# Full-source quotation into capped PHOAS environments

21 October 2026. Parent HEAD: `1d1f2462b1d5dff9f94f8f1f3247f40d34769a90`.
This continues the uncommitted fragment-uniformity milestone. No new commit,
push or CPS formalization was requested. All prior unrelated edits are retained.

## Scope

- `CappedQuotationState`: local binder-rank invariant, actual capped state
  insertion, inherited realization and view/shape transport, executable slot
  selection, acceptance from original endpoint evidence, request-rank bound.
- `CappedLayerAlignment` and `CappedCodeAlignment`: originally typed normal
  contextual coercion, literal erasure, complete judgment repair.
- `CappedFullQuotation`, `CappedApplicationQuotation`, `CappedRecursiveQuotation`:
  numeric plans and all six source rules; application still uses two repairs.
- `CappedProgramInterpreter`: normal typed programs/evaluator, literal recovery,
  syntax injection and type-sort bound `max(k+7,r+6)` for every capped plan.
- `CappedDependentInterpreter`: full closed/open coverage, type recovery,
  pruning/padding invariance, faithful syntax across budgets/derivations,
  and `quote_at`/`every_bounded_original` at a caller-fixed quotation budget.
- Aggregate/Dune registration, research note/PDF, development README/ledger,
  and scoped handoff updates. Large module aliases in the new fragment modules
  are mechanically expanded to qualified references to avoid compiler copies.

Fragment membership requires independent original source data with pruned
quotation budget <=k, not a target program or quotation premise. The fragment
parameter is fixed before the source. These fragments cover all original closed
judgments. Open coverage uses annotated closure; its stated rank bound uses that
closure's budget. A common actual sort-index bound is not cumulativity, one
common interpreter TERM, or a bridge from semantic redex rank to source budget.
Those stronger uniformity obligations remain open. The original uncapped
quoter, its cost proofs and extraction experiments are unchanged.

## Commands and attempts

Raw evidence: `_build/self-interpreter-capped-quotation-2026-10-21`.
All incremental commands use the pinned environment:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedQuotationState.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedLayerAlignment.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedCodeAlignment.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedFullQuotation.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedApplicationQuotation.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedRecursiveQuotation.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedProgramInterpreter.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedDependentInterpreter.vo
opam exec -- dune build --display=short --no-buffer @theories/self_interpreter/audit
```

- `state-01`: intentionally interrupted (130) after module aliases caused
  excessive compiler memory use. Qualifying references avoids duplicating the
  imported modules. `state-02`: exit 1, reversed premises of `formed_replace`;
  corrected in `state-03`, exit 0, 14 own closed reports.
- `layer-01`: exit 0, 9 closed; `alignment-01`: exit 0, 7 closed;
  `full-01`: exit 0, 19 closed; `application-01`: exit 0, 9 closed.
- `recursive-01`: exit 1, incomplete mechanical module-name replacement.
  `recursive-02`: exit 1, extra invariant argument inadvertently added to the
  preexisting rank-bound lemma. Both corrected; `recursive-03`: exit 0, 4 closed.
- `program-01`: exit 0, 14 closed. `dependent-01`: exit 0, 21 closed;
  adding fragment monotonicity and all-closed coverage brings its inventory to 23.
- `audit-incremental`: intentionally interrupted (130) to expand the three
  earlier fragment modules' large exported aliases as well. The compiled
  `CappedInterpreter.vo` shrinks from 34 MiB to 17 KiB, with the same mathematical
  definitions/contracts. `audit-incremental-02` exits 0 for the final source versions.

Disk space was 188 MiB at the start. Prior fresh-build/kernel/final-check success
records were read before cleaning exactly `/tmp/pts-rk-fragment-audit.umlOaP`
with `opam exec -- dune clean --build-dir=/tmp/pts-rk-fragment-audit.umlOaP`.
This recovers only regenerable build files; prior raw verification logs remain.
A preceding attempt to copy `.../log` fails because that file does not exist;
no saved trace from that attempt is claimed. The clean exits 0.

## Fresh verification

```sh
bash docs/direct-r-handoff/verification/self-interpreter-capped-quotation-2026-10-21/AUDIT.sh
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-capped-quotation-2026-10-21/ci bash tools/check-local-ci.sh
bash tools/build-self-interpreter-note.sh
```

`AUDIT.sh` records exact commands, timestamps, versions, exits and manifests.
Fresh absolute Dune directory: `/tmp/pts-rk-capped-audit.lpDpbN`.
Source inventory: 2549 own Print Assumptions commands, 1034 aggregate Check/Print
pairs, 123 proof/Dune manifest entries. Fresh aggregate compilation exits 0
at 10:19:47 UTC (started 10:09:50), with 2550 closed reports: 2549 own plus
one unchanged upstream normalization report. Both recursive kernel checks
exit 0; aggregate checking runs 10:19:54--10:28:56 UTC. Pristine core inventories
are byte-identical. The original core/normalization/ZFC source comparisons,
123-entry source stability checks and whitespace check all pass. Own endpoints
are closed; the loaded kernel inventory has only unchanged upstream functional
extensionality, with no type-in-type, unsafe fixpoints or assumed positivity.

The first full-CI attempt (`ci`, `full-ci.log`) exits 1 at
`01-normalization-complexity`: the concurrently running incremental build held
the default Dune lock. This is a scheduling failure, not a proof rejection;
its complete logs are retained. After fresh compilation releases its lock,
the same unchanged command is retried with `DIRECT_R_LOG_DIR` ending in
`ci-retry` and output `full-ci-retry.log`. The retry exits 0: all 226 stages
PASS and the recorded result is complete, including the pristine upstream build.
The shared worktree still includes unrelated unpublished BZC/CI changes;
this is a local check of that worktree, not a claim of hosted/public CI.

`note-01` exits 0 in `/tmp/pts-rk-self-note.t5KcZY`, 13 pages; PDFKit extraction
and rendering exit 0. One overfull prose line (42.08 pt) is identified and
reworded. Pages 1, 12 and 13 are visually inspected. `note-02` exits 0 in
`/tmp/pts-rk-self-note.KAJfjK`, 13 pages, without overfull/underfull boxes,
LaTeX warnings or missing glyphs. Final PDFKit extraction/rendering exits 0;
the corrected page 11 is visually checked, with final pages 12/13 rendered.

`FINAL-CHECKS.sh` exits 0, verifying recorded successes, exact inventories,
all current source hashes, pristine agreement, complete CI, warning-free final
TeX output, empty index and unchanged HEAD. The implementation, updated note/PDF
and scoped evidence are uncommitted; no commit or push is performed this turn.

Final document SHA256 values:

```text
2de4cc8097e95182e9d9b52d98d4289f3ae007345925011948f334d7755f0f85  PTS-rk_self_interpreter.tex
9e7e5e5bd5148083421287e29268fb1ad5f840f3d75e9acf6da88e24a6d34855  PTS-rk_self_interpreter.pdf
```

Pinned versions: OCaml 4.14.2, Dune 3.23.1, Rocq 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2. Full installed versions are retained in `versions.log`.
