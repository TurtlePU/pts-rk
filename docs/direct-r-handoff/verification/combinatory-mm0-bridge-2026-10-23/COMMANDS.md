# Fresh literal-MM0/native bridge audit — 2026-10-23

The focused driver is AUDIT.sh. It checks all 58 combinatory modules, including
the eight new native/literal-MM0 bridge modules, without altering original
PTS rules or relying on cached assumption output. Full repository CI, Agda
and an MM0 checker are not run by this driver. The separate textual MM0
crosscheck remains part of the audit.

Command, from the repository root:

```sh
bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/AUDIT.sh
```

Pinned environment: OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam,
OPAMSWITCH=pts-rk-ci; Rocq 9.2.0 / OCaml 4.14.2, Dune 3.23.1,
Stdlib 9.1.0 and Equations 1.3.2+9.2. The raw commands, versions, package
inventory, per-stage exit codes and UTC timestamps are retained in each run.

## Scope and evidence rules

The source manifest contains all 58 proof sources, their Dune registration,
shared DirectREval.v and the original MM0 text: 61 paths. All 50 preceding
combinatory proof sources and shared equality/MM0 bytes are checked against
the prior fresh audit. Dune is exempted only from that raw old hash and must
instead normalize EXACTLY to its old bytes after removing the eight explicit
new module/alias registrations. The normalized old SHA-256 is
865c216310c87178a3a37c1e0ced5f84b3d8e97647b0bf46eef01ec7e90085d5.
All 12 original kernel files are compared to pristine revision
723cf2ec61c737ae82ba33d2e7db44f650122b0e. The existing 52-source Agda
manifest is checked unchanged.

Each run uses a new absolute Dune build directory and independently archives,
builds and recursively checks pristine Ranks. Complete current and pristine
kernel context inventories must agree byte-for-byte; no dependency skips or
admission flags are used. All public assumption reports must be closed. The
final roster has 192 new endpoints, 885 own reports and 886 aggregate reports
(the extra report comes from original Ranks).

Live logs remain untouched. The EXIT trap archives every log/text/status file
as exact .raw.gz bytes and as a readable copy with trailing whitespace/excess
final blank lines removed. Archival is also performed before the whitespace
gate. No proof source is formatted by this step. The whitespace gate checks
new unstaged proof files with --no-index as well as the scoped Git diff.
No files, temporary builds or unrelated processes are deleted.

## Attempt 01: final-source freeze race

Started 19:20:24 UTC.

- Live logs: _build/combinatory-mm0-bridge-audit.KjFF55
- Fresh build: /tmp/pts-rk-mm0-bridge.ZAbEr8
- Fresh pristine: /tmp/pts-rk-mm0-bridge-pristine.cCziNn
- Archive: audit.Fe6pdS

The root freeze notification raced the final Hilbert endpoint addition.
At 19:20:25 the source manifest recorded MM0HilbertAdequacy.v as
6564d2bff5f54dad28b999e7a86273a6a05bebd1c7bedee0ad929d17a4185960.
The subsequently frozen final file has 21 endpoints, including
consistent_finite_union_exact, and hash
3c4de44655aa133157d61c765b47e2ffbbe65d3f583108c41dd65d2a38ff99ff.
This is a REAL proof-source change, not registration drift. It is not
normalized away. The first run and its strict source-stability failure are
retained; a new absolute-build run is required for the final stable snapshot.
All agents explicitly acknowledged the final freeze afterward.

Compilation passed 19:20:34–19:23:10 UTC (156 seconds), then full recursive
kernel checking passed 19:23:10–19:23:34 (24 seconds). The complete context
inventory equalled the fresh pristine inventory. All old proof/kernel/Agda/
MM0 checks and the exact registration normalization passed. Source stability
then exited 1 at 19:23:34, with only the Hilbert source manifest line changed.
The driver therefore exited 1; this was not an all-pass final-source audit.

The run additionally exposed a shell gate defect: check_reports used bare
assertions inside run's set+e region, so a count mismatch could fall through
to a later successful command. The actual first build printed 885 aggregate
reports, while current final sources demanded 886. Its recorded
closed-reports exit 0 MUST NOT be treated as valid count verification.
This agrees with Dune having captured the earlier 20-endpoint Hilbert source.
The original script is retained in audit.Fe6pdS/AUDIT.sh, SHA-256
5fb577146d379d24d22d9387ef55241657d2414c4bc03335488e60a72a53d269.

Before attempt 02, every nonterminal assertion in report/context/whitespace
checks, plus archival operations, was changed to explicit failure returns.
The final count gate requires exactly 58 modules, 885 own reports and 886
aggregate closed reports. A negative test against attempt 01's count log
returns 1 as required. An initial negative-only whitespace probe also returned
1, but was INSUFFICIENT: as attempt 03 subsequently exposed, clean no-index
new-file diffs return 1 too. It therefore did not establish that the intended
whitespace fixture was reached. Those original test outputs are retained in
count-gate-negative-selftest.log and whitespace-gate-negative-selftest.log;
the latter's raw bytes are additionally preserved as gzip. The final recovery
below fixes this with both positive and negative/error fixtures against the
actual helper, without weakening any whitespace or source-integrity check.

## Attempt 02: frozen final sources

Started 19:25:19 UTC, after every proof owner explicitly confirmed freeze.
All 61 final paths were snapshotted at 19:25:20.

- Live logs: _build/combinatory-mm0-bridge-audit.9uROGM
- Fresh build: /tmp/pts-rk-mm0-bridge.gHihHC
- Fresh pristine: /tmp/pts-rk-mm0-bridge-pristine.mLKLgH
- Archive: audit.VF16WL

Fresh compilation passes 19:25:29–19:28:02 UTC (153 seconds), with exactly
885 own / 192 new / 886 aggregate closed reports. Complete recursive kernel
checking passes 19:28:02–19:28:26 (24 seconds). Its entire context inventory
matches fresh pristine exactly. Every old source/kernel/MM0/Agda check,
exact Dune normalization, and all 61 before/after source hashes pass.

The driver then exits 1 at the safety scan, 19:28:26: the pure structural
admission predicate was named `Definition Admitted N d e := ...`, and the
simple forbidden-word scanner also matched its nine references. There was
no admitted proof command or added axiom; all actual proof reports were
closed and the complete kernel inventory agreed. Preserve this real gate
failure: attempt 02 is not an all-pass driver run, and did not reach its
whitespace stage.

Root authorized exactly one source edit: rename that structural predicate
and all its references to FitsSyntax, without changing theorem names,
proof tactics, guards or definitions. The scanner remains UNCHANGED.
The final MM0GuardedSyntaxAlgebra.v SHA-256 is
28343fe48b2fe765c4de6adabc0db028fc34dbe6098dbebb60c2a990aa3705c9.
The simple strong scan then passes all 58 proof sources. A new fresh audit
is run to verify the renamed final source and its complete dependency closure.

## Attempt 03: renamed structural predicate, unchanged safety gate

Started 19:29:48 UTC; all 61 final paths snapshotted at 19:29:49.

- Live logs: _build/combinatory-mm0-bridge-audit.BLPblO
- Fresh build: /tmp/pts-rk-mm0-bridge.IH9mrh
- Fresh pristine: /tmp/pts-rk-mm0-bridge-pristine.2MonTA
- Archive: audit.HRs4x3

Fresh compilation PASSES 19:29:58–19:32:42 UTC (164 seconds): 885 own,
192 new, 886 aggregate closed reports. Complete recursive kernel verification
PASSES 19:32:42–19:33:06 (24 seconds). Its whole inventory is byte-identical
to the newly built pristine inventory: only inherited
functional_extensionality_dep, no type-in-type, unsafe fixpoints or assumed
positivity. All 61 before/after hashes agree. Original kernel, all 50 preceding
proof sources, exact eight-entry Dune registration, unchanged MM0/52 Agda
sources, textual literal-axiom crosscheck and the unchanged strong safety
scanner pass. No proof source changes after this run.

The final whitespace wrapper exits 1 at 19:33:08 with EMPTY diagnostic
output. `git diff --no-index --check` implicitly enables --exit-code: on this
Git, a clean new-file difference returns 1, and actual whitespace errors
return 3. Thus the wrapper rejected the first clean new source. The complete
raw run and original driver snapshot (SHA-256
377777d9c8a0c2d7f5f1e33b5629e50ec5308f757241bab9c61279a00cb2a96e)
are retained in audit.HRs4x3. The original driver is NOT described as all-pass.

## Final recovery: all ten gates pass

The corrected check accepts a no-index status of 0 or 1 ONLY when diagnostic
output is empty, and rejects every diagnostic, larger exit code, or missing
target. The tracked Git whitespace check is unchanged. Root authorized no
further proof edits or recompilation: the successful fresh final proof run
above remains the verification basis.

```sh
bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/FINAL-CHECKS.sh
```

All ten gates PASS, 19:35:43–19:35:44 UTC, exit 0:

- Live logs: _build/combinatory-mm0-bridge-final.LNIhbh
- Archive: final.MjHIDx
- Current 61-file manifest and fresh before/after manifests agree.
- Exactly 885 own / 192 new / 886 aggregate reports are verified.
- Complete fresh/pristine kernel context inventories agree exactly.
- The original strong safety scan passes.
- A clean new-file fixture is accepted; real trailing whitespace, a missing
  target and the earlier wrong report count are each rejected.
- The final note/PDF/build-script/inspector manifest agrees unchanged.
- Repaired tracked AND unstaged-source/archive whitespace checks pass.

Each recovery command/status and the actual driver hashes are archived.
Raw diagnostics are gzip-preserved before readable whitespace normalization.
No final gate is represented as a new compilation, and no original failed
driver status is overwritten. HEAD remains
6a8dc984fb59a9b3743503cd405ffe59a31d1978; no staging, commit, push,
cleanup or unrelated process termination was performed.
