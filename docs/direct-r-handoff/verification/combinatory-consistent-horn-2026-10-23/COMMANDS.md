# Consistent grounded Horn theories — 23 October 2026

## Scope and mathematical status

Eight new modules extend the existing 24-module combinatory development:
NativeCanonicity, GroundHornConsistency, FiniteHorn, HilbertGrounding,
HilbertFiniteModels, FiniteHornChurch, FiniteUniversalHorn and
FiniteModelBoundary. They add 117 public assumption reports. Original PTS
syntax, typing, normalization and conversion rules are unchanged.

The concrete Hilbert catalogue now has genuine Void-denying models, whose
existence follows from proved native canonicity, not an assumed consistency
premise. Finite ground fragments have executable exact least models;
signed completion reflects supported propositional formulas but adds negative
facts to the original fragment. Actual original-PTS Church tables compute
their externally determined answers. Complete semantic grounding decides
predicate-model existence for a supplied finite constructor interpretation,
checking every semantic valuation. It does not construct such an
interpretation for every quantified PTS fragment. Internal uniform reflection,
quantified PTS schema adequacy and the separate MM0 graph bridge remain open.

The finite K obstruction concerns total untyped application with universal
equational K, not typed/graded, guarded/partial or directed-reduction models.

## Final fresh audit — PASS

From the repository root:

```sh
bash docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23/AUDIT.sh
```

The script records the exact expanded commands, exits and UTC timestamps.
All **19 stages pass**, 06:50:50–06:51:47 UTC, exit 0. Evidence is in
[audit-final/status.tsv](audit-final/status.tsv),
[audit-final/commands.txt](audit-final/commands.txt) and the corresponding
raw logs. Original runtime directories:

- Logs: `_build/combinatory-consistent-horn-audit.QbsFPC`.
- Fresh absolute Dune build: `/tmp/pts-rk-consistent-horn.2l5WGN`.
- Fresh pristine tree: `/tmp/pts-rk-consistent-horn-pristine.UNV9A0`.

Pinned environment: OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam,
OPAMSWITCH=pts-rk-ci, using
/Users/akuklev/.local/share/pts-rk-ci/bin/opam. Verified versions:
Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Full installed-package inventory is retained.

The fresh integrated build passes **06:51:00–06:51:26 UTC**, exit 0:
all 32 combinatory modules, **358 own closed reports** plus one imported
Ranks report (359 aggregate). All 117 new reports are closed. Complete
recursive `rocq check -silent -o`, without admission/skip flags, passes
**06:51:26–06:51:47 UTC**, exit 0, on all 32 roots and their dependency
closure. The complete context inventory equals fresh pristine byte-for-byte:
only inherited `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`,
no unsafe guard/positivity/universe entries. Closed theorem reports do not
erase that inherited library inventory.

All 12 original kernel files match pristine revision
723cf2ec61c737ae82ba33d2e7db44f650122b0e. All 52 previous Agda sources match
their prior audited manifest. The 32 Rocq sources, Dune registration and
shared DirectREval equality dependency have identical before/after hashes.
The safety scan and scoped whitespace check pass. Existing namespace/shadow
warnings and the upstream Vector.t advisory are retained, not suppressed;
the entire build is not described as warning-free.

HEAD remained 6a8dc984fb59a9b3743503cd405ffe59a31d1978. Pre-existing dirty
work, including simultaneous unrelated handoff additions, was preserved.
No index manipulation, commit or push was performed by this work. No new
Agda, MM0 or full-repository CI run is claimed.

## Earlier fresh attempts — failures retained

1. `audit-01/`, logs originally `.hwVbp2`, fresh build
   `/tmp/pts-rk-consistent-horn.zEqVhw`, 06:48:14–06:48:24 UTC. Pristine
   build/check pass; fresh build exits 1 because isolated NativeCanonicity
   compilation left three generated `.vo`, `.glob`, `.aux` artifacts in the
   source directory, causing duplicate Dune targets. Those exact generated
   files were moved recoverably to
   `/tmp/pts-rk-horn-models.9oMCVS/isolated-objects/`; no user source was removed.
2. `audit-02/`, logs originally `.nW7Jd0`, fresh build
   `/tmp/pts-rk-consistent-horn.qzQEXT`, 06:49:09–06:50:07 UTC. Fresh build
   and full recursive check both pass, with 359 aggregate reports. Raw-log
   comparison exits 1 because the current log includes a shared-library
   remapping warning before the context report. The audit now requires
   exactly one `CONTEXT SUMMARY` in each raw log and compares the **entire**
   inventory from that heading through EOF. No inventory field is omitted;
   raw diagnostics remain archived. A wholly fresh third run above passes.

Driver logs `fresh-audit-driver.log`, `fresh-audit-driver-02.log` and
`fresh-audit-driver-03.log` retain the outcomes; the first two are not passes.

## Isolated proof-development commands

NativeCanonicity was checked after each correction with this command, with
LOG replaced by `/tmp/pts-rk-horn-models.9oMCVS/canonicity-01.log` through
`canonicity-06.log`:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq compile \
  -Q _build/default/theories PTSrk \
  -Q _build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q theories/CombinatoryLogic-rk PTSrk.Combinatory \
  theories/CombinatoryLogic-rk/NativeCanonicity.v > LOG 2>&1
```

Exits were 1, 1, 1, 1, 1, 0. The errors were, respectively, the constructor
name `univ` rather than `𝓤`, an uninferred natural-number label parameter,
a reused local binder, and two unstable dependent-elimination variable names.
Explicit constructor patterns resolve the final issue; attempt 06 prints
two closed reports. All six raw logs are under `canonicity/`.

The other isolated commands, failures, exits and hashes are retained in:

- [denials/COMMANDS.md](denials/COMMANDS.md): generic constraints, concrete
  Hilbert grounding and exact finite Hilbert models.
- [finite/COMMANDS.md](finite/COMMANDS.md): finite saturation and signed
  propositional completion.
- [church/COMMANDS.md](church/COMMANDS.md): literal original-PTS truth tables.
- [universal/COMMANDS.md](universal/COMMANDS.md): complete finite semantic
  valuation enumeration and candidate checking.
- [boundary/COMMANDS.md](boundary/COMMANDS.md): finite untyped equational K
  collapse, with its exact scope.

The fresh integrated and recursive checks above are the final verification
of their combined current sources, superseding isolated build contexts.

## Note and PDF

Final note build `/tmp/pts-rk-combinatory-note.gKhpiC`,
**06:48:39–06:48:53 UTC**, build/validation and strengthened inspector exit 0:
**27 pages**, three-page MM0 appendix, 30 Rocq and 27 Agda badges,
44 Agda source links, 98 links total. All pages rendered; changed pages
1, 18–21 and 23–24 visually reviewed. Source/PDF hashes are in
[note-final-sha256.txt](note-final-sha256.txt).

The first build compiled but visual review found a dangling backslash in
the signed-diagram display; it is not a visual pass. The corrected second
build passed, then was superseded by the finite-candidate exposition.
Exact commands, all three runs and retained renders are recorded in
[NOTE-REVIEW.md](NOTE-REVIEW.md). No proof source changed after the final
fresh audit freeze; final hash rechecks are retained.
The final post-documentation checks are recorded in
[FINAL-CHECKS.md](FINAL-CHECKS.md).

## Next obligation and rerun

Specify a genuinely quantified typed/resource PTS fragment, construct a
finite constructor interpretation accepted by FiniteUniversalHorn, and prove
its schema agreement and coverage under all valuations. The supplied
candidate checker is not a candidate-existence theorem. Internalizing the
soundness argument and uniform saturation is a separate obligation from
externally generating correct Church tables.

After the next proof change, rerun the exact `bash .../AUDIT.sh` command
above (900-second fresh-build/check allowances, no weakening), then rebuild
the note with `bash theories/CombinatoryLogic-rk/build-note.sh` if changed.
