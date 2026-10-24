# Explicit guarded quantified fragments — verification ledger

HEAD: 6a8dc984fb59a9b3743503cd405ffe59a31d1978. Work is uncommitted; no
staging, commits, pushes, unrelated cleanup or original kernel edits.

## Proofs

Pinned OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam,
OPAMSWITCH=pts-rk-ci, opam=/Users/akuklev/.local/share/pts-rk-ci/bin/opam.
Rocq9.2, OCaml4.14.2, Dune3.23.1, Stdlib9.1.0, Equations1.3.2+9.2.
All exact executable arguments are in each worker's command files/ledger and
the audit's commands.txt. No compilation artifacts were placed in theories.

New public reports: GuardedFiniteCarriers28; GuardedHornFragments19;
GuardedHilbertModels27; GuardedBetaGraphs36; GuardedHilbertTables36;
GuardedHilbertCoverage20; MM0GuardedQuantification29. Total195. All isolated
compilations and complete recursive kernel checks pass. Worker directories
retain every failed attempt and final source hash.

Command: `bash docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/AUDIT.sh`.

- Attempt01 (then49 modules): 18:17:33–18:22:20 UTC. Fresh compilation
  encountered `dune_trace_write(): No space left on device`. The task-owned
  Dune95545 ignored TERM and was stopped with KILL; wrapper exit137. No other
  process/data was changed. Live logs _build/combinatory-guarded-fragments-audit.fX2mac,
  build/tmp/pts-rk-guarded-fragments.HkLVv5, pristine/tmp/pts-rk-guarded-pristine.9tU6QO.
  Source writes also failed; after free space recovered from~120 to~260MiB,
  writes resumed. The Air question tool returned Transport closed.
- Attempt02 (50 modules): 18:28:34–18:31:19 UTC. Fresh compilation passes
  18:28:44–18:30:57 (133s), 693 own closed reports, 694 aggregate. Full
  recursive kernel checking passes18:30:57–18:31:19 (22s). Every dependency
  is included; no skip/admit or weakened checking. Entire inventory equals
  freshly built pristine723cf2ec61c737ae82ba33d2e7db44f650122b0e exactly:
  inherited functional_extensionality_dep only, no unsafe entries.
  Live _build/combinatory-guarded-fragments-audit.ACxpVa,
  build/tmp/pts-rk-guarded-fragments.Hzzxi9,
  pristine/tmp/pts-rk-guarded-pristine.HmTbHx.
  All original-kernel/previous-source/MM0/Agda/hash/safety stages pass. The
  final whitespace stage exits2 on generated logs, not proof sources.

Readable generated logs/command listings/inventory displays are subsequently
whitespace-normalized; corresponding .raw.gz files preserve their exact
original bytes. No failed proof or audit output was replaced by a success.
The live audit directory retains the untouched original logs as well.
The final gate command is `bash docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/FINAL-CHECKS.sh`.
It verifies the existing FRESH outputs and unchanged sources, rather than
claiming a cached rebuild regenerated Print Assumptions. Its record is in
final-checks. All nine gates pass at18:37:10 UTC, exit0; live logs
_build/combinatory-guarded-final.ftRIP5. Do not label audit attempt02 an
all-pass driver run.

## Note

Build command: `bash theories/CombinatoryLogic-rk/build-note.sh`.
The script records actual latexmk/LuaLaTeX arguments, versions, timestamps,
exit status, validation and source hashes.

- Build01 /tmp/pts-rk-combinatory-note.h241td: LaTeX/validation exit0, but
  PDF inspection exited133 with `Unprocessed display mathematics: $$`.
  A trailing backslash after the displayed conjunction triggered Markdown's
  hard line break. The initial inspector output was in the tool transcript;
  the original compiled PDF remains in that build directory.
- Build02 /tmp/pts-rk-combinatory-note.ZiZuWu: repaired display; build,
  validation and inspection pass, 29pages/47Rocq badges.
- Final /tmp/pts-rk-combinatory-note.lDshJ1: includes exact executable union
  coverage. Build/validation pass18:27:19–18:27:34 UTC. Command:
  `swift docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/inspect.swift theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf /tmp/pts-rk-guarded-note-final.oiiONe`.
  Inspector exit0: 30pages, appendix3pages, 48Rocq/27Agda badges, 116links.
  Every page renders; pages22–24 visually reviewed. Source/PDF/build-script/
  inspector hashes are in note-final.sha256. Generated PNGs remain temporary.

## Scope

The executable model covers all six native Hilbert rule forms under explicit
syntax/path guards. Coverage is exact for the independent catalogue, including
actual finite-carrier queries and common budgets for finite proof families.
The separate full55 literal-MM0 guard compiler is conditional on its structural
representation law and candidate model. No original-PTS-to-catalogue
completeness, native/MM0 adequacy, uniform internal reflection, internal
consistency proof or whole-host-memory bound is claimed. Native canonicity
provides external Void exclusion. All52 Agda and the MM0 source remain
unchanged; no new Agda/MM0 checker or complete repository CI run was performed.
