# Exact renaming realization and single-substitution environments

23 October 2026. Four new modules, 764 lines, 41 new registered assumption
reports (426 total). Original annotated PTS syntax and typing are unchanged.
Fresh completion compilation **passes**, exit 0, with **426/426 closed
reports**. The full new dependency-closure recursive check **passes**, exit 0,
using the explicitly enabled standard VM conversion backend; its complete
inventory equals pristine and both source checks pass. The interrupted runs
and earlier ordinary-check timeout remain separate historical outcomes.
No full repository CI, staging, commit, push or cleanup is part of this run.

## Contracts and remaining obligations

- `RenamingLookupRealization`: executable application helpers and pointwise
  witnesses for the existing fixed-environment lookup graph. The lifted
  family covers `weak rho`, retaining the same environment and base. The
  concrete shift family and its local bound are constructed from independent
  index/successor witnesses, not assumed.
- `RenamingRealization`: executable witnesses for exact `Syntax.rename`
  endpoints on every original `Term nat n`, with a supplied pointwise family
  in the generic theorem. The standard shift theorem constructs that family
  and retains no such premise. Decoder and successful raw-shift bridges have
  exact canonical endpoints. `shifted_scope_witness` applies the actual
  internal preservation term to the graph witness and independently proved
  environment bound; it does not substitute a native output-scope theorem.
- `InternalSubstitutionEnvironment`: independent term-valued graph
  `SingleEnv : C -> C -> C -> C -> U13`, with exact motive rank 12.
  Zero returns the supplied image; a successor returns the corresponding
  old variable using independent Index/Succ premises. Neither clause assumes
  output scope. An actual original-PTS term derives `TermFBound` from scope
  of the supplied image; its quantified type has rank 14.
- `SubstitutionEnvironmentRealization`: actual PTS application helpers,
  executable point witnesses for `0 -> u, successor j -> var j`, and the
  independently instantiated local bound for every original `u`, including
  untyped terms. The witnesses match the literal `fin_match` environment
  used by original single substitution.

This is forward realization and every-output scope preservation, not
reflection of arbitrary Church inhabitants, dependent typing preservation,
or consistency. No global functionality, matching-constructor inversion or
equation `target = base + depth` is needed for these contracts. Standard
witness generation explicitly threads coherent canonical states.

Next construct fixed-base, binder-indexed **term-valued lookup**, using the
already realized shift to weaken old images, and prove its all-output scope
invariant. Then construct annotated replacement, instantiate single
substitution, and prove exact standard realization and output-scope
preservation. Dependent typing/conversion invariants, operation/resource
sufficiency, standard raw-input admission, all-budget soundness and the
internal consistency implication remain open. The current environment is
not yet an internally lifted replacement operation.

## Pinned environment

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Package inventory:
`_build/self-consistency-renaming-progress.R8eFUQ/versions.log`.
HEAD is `6a8dc984fb59a9b3743503cd405ffe59a31d1978`; the index was empty
when inspected. Existing dirty work is preserved.

## Isolated development checks

Compilation uses coherent objects from the preceding fresh build, with one
logical path per dependency. The command shape is:

```sh
opam exec -- timeout 300 rocq compile -time \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories PTSrk \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-substitution-environment.1e757d PTSrk.SelfConsistency \
  /tmp/pts-rk-substitution-environment.1e757d/InternalSubstitutionEnvironment.v
```

This exact InternalSubstitutionEnvironment command completed with exit 0,
confirmed by the owning process result (session 42562); log
`/tmp/pts-rk-substitution-environment.1e757d/attempt-01.log`. The final
bound proof uses checker fuel 8192; formation uses 2048. No shared checker,
PTS rule, theorem contract or guard check changed.

Other isolated attempts use the same three dependency paths plus the
module's own directory; realization modules also require the new dependency
objects. Retained evidence and limitations:

- `/tmp/pts-rk-renaming-lookup-realization.ZZ06Pz/attempt-01.log` and
  `attempt-02.log`: parser errors in explicit dependent application types.
  Attempt 03: unsupported `dependent` tactic syntax. Attempt 04: unfinished
  finite-index branch. Attempt 05: an uninferable term placeholder. Attempt
  06 has no error and produced a compiled object. Its separate process exit
  record was lost across the resume; this is not used as fresh-build proof.
- `/tmp/pts-rk-renaming-realization.HSNPtO/attempt-01.log`: ends during the
  binder application proof, with neither a completed object nor an exit
  marker. This interrupted/incomplete attempt is **not** a passing build.
- `/tmp/pts-rk-substitution-environment-realization.dhMan7/attempt-01.log`:
  no error and a compiled object, but no retained process exit record.
  `reports-01.log` contains seven closed reports for selected lookup and
  standard-environment endpoints. The complete fresh audit below supersedes
  these partial records when it finishes.

Loadpath-remapping and large-natural-literal warnings are retained. No
admissions, new axioms, unsafe casts or disabled guard/universe checks are
introduced. Application helpers use original `tApp` and original
substitution, not a new typing judgment.

## Completed recovery of the previous recursive check

The preceding seven-module audit compiled and printed 385/385 closed reports,
but its ordinary recursive check timed out after 2400 seconds, exit 124,
without a complete inventory. That historical failure is preserved in
`self-consistency-substitution-2026-10-23/COMMANDS.md` and its original logs.

A distinct check of those same frozen objects now **passes**, exit 0:
02:06:14–02:16:57 UTC, 643 seconds within a preselected 1800-second limit.
Logs: `_build/self-consistency-renaming-vm.gH0ToE`, including `start.txt`,
`end.txt`, `kernel-exit.txt`, `kernel.log`, and before/after source manifests.
The command is:

```sh
opam exec -- timeout 1800 rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories PTSrk \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories/self_consistency PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.CodeSubstitution \
  PTSrk.SelfConsistency.ScopeRealization \
  PTSrk.SelfConsistency.InternalRenaming
```

`-bytecode-compiler yes` enables Rocq's standard VM conversion backend.
Every proof in the complete requested dependency closure is checked: no
`-admit`, `-norec`, skipped proof, or disabled safety check is used. This
changes the conversion backend/trust path relative to the timed-out ordinary
check; it is not evidence that the earlier run passed. Repository CI is
unchanged.

The pristine `PTSrk.Ranks` closure was also checked with this backend and a
300-second limit, using `/tmp/pts-rk-substitution-pristine.qcNAzd`. Complete
`CONTEXT SUMMARY` inventories compare equal, exit 0:
`current-inventory.txt` and `pristine-inventory.txt`. The only axiom is the
unchanged upstream `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
type-in-type, unsafe fixpoints and assumed positivity are all absent.
Source-stability comparison also passes. Public closed reports and the
complete imported context inventory are different checks; the latter still
records that inherited axiom.

## Fresh four-module build and reports — passed

Fresh absolute build directory: `/tmp/pts-rk-renaming-fresh.T1RZXE`.
Logs: `_build/self-consistency-renaming-progress.R8eFUQ`.
The earlier command used a 1800-second limit and the three explicit targets
`theories/self_consistency/InternalRenaming.vo`,
`theories/self_consistency/InternalSubstitutionEnvironment.vo`, and
`theories/self_consistency/CodeSubstitution.vo`, with the same Dune directory,
display, buffering and job flags below. Its `fresh-base.log` run was
interrupted by a resume and has no exit file. Existing objects do not
establish that command's success. The completion run below passed,
**03:09:08–03:22:09 UTC**, 781 seconds, exit **0**:

```sh
opam exec -- timeout 1200 dune build \
  --build-dir /tmp/pts-rk-renaming-fresh.T1RZXE \
  --display=short --no-buffer -j 2 @theories/self_consistency/audit
```

Completion output: `complete-build.log`; actual status/times:
`complete-start.txt`, `complete-end.txt`, and `complete-exit.txt`; the process
result also confirmed exit 0 (session 15853). All four new modules compiled
without source edits. The frozen manifest is **`sources-frozen.log`**;
`sources-before.log` predates the final Audit registration and must not be
mistaken for that final snapshot. Audit registration
contains 13 lookup-realization, 11 renaming-realization, 7 internal-environment
and 10 environment-realization endpoints: **41 new, 426 total**. The completed
log contains exactly **426** `Closed under the global context` reports.
The frozen manifest was successfully checked before and after recursive
checking: all 76 entries pass in both `kernel-sources-before.log` and
`kernel-sources-after.log`.
Previous module/common-source hash checks and the original-kernel comparison
pass (`previous-unchanged.log`, `original-unchanged.log`).

## New-closure recursive check — passed

Following successful fresh compilation, the following check passed,
**03:22:22–03:36:57 UTC**, 875 seconds, exit **0** (process session 4910).
It covers both new roots and their entire dependency closure with the same
explicit VM-enabled backend:

```sh
opam exec -- timeout 1800 rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories PTSrk \
  -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories/self_consistency PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.RenamingRealization \
  PTSrk.SelfConsistency.SubstitutionEnvironmentRealization
```

Output is retained in `kernel.log`; actual timestamps/status are recorded in
`kernel-start.txt`, `kernel-end.txt` and `kernel-exit.txt`. The completed
`current-inventory.txt` compares exactly with
`_build/self-consistency-renaming-vm.gH0ToE/pristine-inventory.txt`, exit 0.
The only axiom is the unchanged upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
there are no type-in-type, unsafe-fixpoint or assumed-positivity entries.
All 76 frozen source hashes pass both before and after checking. Every new
module and its recursive dependencies is covered, not unrelated old optional
modules or full CI. Those unchanged sources retain their preceding separate
full checks. This result does not retroactively turn the earlier
VM-disabled timeout or interrupted shells into successful runs.

## Reproducible audit driver and note/PDF

The new `AUDIT.sh` supplies a one-shot fresh build, reports, recursive check,
pristine comparison, safety scan and source-stability check. Its syntax check
passes, but the script has **not been run as one unit**: the actual evidence
above comes from the individually recorded stages. Its up-front clean-build
allowance is 1800 seconds, versus 1200 for this resumed completion build;
both use 1800 for the recursive check. It changes no repository CI setting.

```sh
bash -n docs/direct-r-handoff/verification/self-consistency-renaming-2026-10-23/AUDIT.sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift \
  theories/self_consistency/DIRECT_ROADMAP.pdf \
  _build/self-consistency-renaming-progress.R8eFUQ/pdf
```

Note build 01 passes with validation exit 0 in
`/tmp/pts-rk-consistency-note.bPlKY5`; log `note-build-01.log` in the progress
directory. PDF inspection passes: 15 nonempty pages, four links, required
text and mathematics, and all-page rendering (`pdf-inspection.log`). Changed
pages 12 and 13 were visually reviewed. Page images and extracted text remain
in the progress directory's `pdf` subdirectory.

Note build 02 also passes, in `/tmp/pts-rk-consistency-note.SzSwbM`, after
updating the final work-package summary to mark standard shift complete.
The repeated inspector passes with the same 15 pages/four links; page 15 is
also visually reviewed. Logs: `note-build-02.log`, `pdf-inspection-02.log`.
`final-sha256.log` records all four new sources, Audit/dune and the final
TeX/PDF pair. The frozen PR#1 ZFC-model comparison also passes, exit0:

```sh
git diff --exit-code ffa7131 -- theories/ZFC_model
git diff --cached --exit-code
```

`frozen-zfc.log` is empty. Neither that reference model nor any preceding
proof module was edited; the index remains empty. New files may appear as
intent-to-add in the interface, which is not staged content. No commit/push.
