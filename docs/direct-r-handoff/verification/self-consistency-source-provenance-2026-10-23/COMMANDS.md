# Independent checker-source provenance

This folder records verification of the new source-indexed checker relation
and any original-PTS integration completed in this continuation. It does not
assert internal finite-fragment soundness or internal consistency.

The driver's explicit module list
contains CheckerSourceGraph, InternalExecutionGraph and CheckerGraphRealization;
the source files must be frozen before starting verification. The audit module is
SourceProvenanceAudit and the Dune alias is source-provenance-audit.

```sh
bash docs/direct-r-handoff/verification/self-consistency-source-provenance-2026-10-23/AUDIT.sh
```

The driver uses the pinned pts-rk-ci environment, a fresh absolute Dune
directory and a separately extracted pristine upstream tree. It records exact
commands, exit codes, UTC start/end times, versions, before/after source
manifests, every new public proof declaration and its assumption report, and
the full recursive VM-enabled kernel inventory. No module admission or
dependency skipping is used. The entire inventory must match pristine.

The previous checkpoint has 506 theory-source entries. All 503 nonregistration
entries remain frozen. The two self-consistency registration files are checked
by exact normalization of the additive import/module/alias entries back to
their previous hashes. The concurrently modified combinatory Dune file receives
the same exact check for its explicitly reviewed guarded-model registrations
(four at fresh-build start, six at its post-gate, seven at final recovery).
All prior bodies and dependencies remain unchanged. The stable source manifest
contains precisely those 506 paths plus the four new proof files (510 total).
Full working-tree manifests are archived separately as informational snapshots;
new unrelated concurrent combinatory proofs are outside the claimed closure.
The original kernel, PR #1 ZFC tree, proof-safety scan and changed/untracked
whitespace are checked separately. Fresh compilation and kernel checks each
have a 3600-second process timeout; this does not authorize silent blocking
waits or overlooking stalled work. The unrelated older full audit and whole
repository CI are not part of this scoped check.

Both driver scripts passed bash syntax checking on preparation. Current disk
availability was 349 MiB; no cleanup was performed. No proof compilation or
fresh verification is claimed from this preparation step.

Fresh attempt01 began 18:05:15 UTC and stopped at the frozen-source gate at
18:05:22, exit1, before any build. Exactly the combinatory Dune hash differed.
The failed run is preserved under audit-01.
The archived audit-01/AUDIT.sh reconstructs the pre-adjustment driver from the
recorded edits; its logs and command records are the original run artifacts.
Read-only normalization established
that the difference is exactly four additive guarded-module registrations,
with prior dependencies and entries intact. The root agent reviewed and
approved the explicit scope adjustment above; no old proof body is exempted
and no kernel dependency is skipped. Fresh attempt02 began 18:09:13 UTC with
the corrected scoped manifest and exact registration-normalization gates.

The root agent also ran a broader documentation diagnostic:

```sh
git diff --check -- theories/self_consistency docs/direct-r-handoff/STATE.md docs/direct-r-handoff/BUILD.md docs/direct-r-handoff/DECISIONS.md
```

It exited2 because unchanged NamedTemplates.v:283 has an existing extra EOF
blank line. That frozen proof was not edited. The scoped fresh/final whitespace
checks cover all actual continuation edits and archive sources, retaining the
previous proof hashes. The broad diagnostic is not represented as passing.

## Fresh proof verification and explicit registration recovery

Attempt02 freshly compiled 18:09:36–18:14:39 UTC (303s), exit0. All 90 new
public endpoint reports are closed (91 aggregate). Complete recursive
VM-enabled kernel checking passed 18:14:39–18:22:11 UTC (452s), exit0,
without skipped or admitted dependencies. Its entire inventory equals the
fresh pristine inventory exactly: inherited functional_extensionality_dep
only and no unsafe entries. Original kernel, frozen ZFC and the proof-safety
scan also passed. Exact artifacts and the original driver are in audit-02.

Attempt02 is NOT an all-pass driver run. At 18:22:18 it stopped at the raw
source-stability gate, exit1: the concurrent combinatory Dune file had added
GuardedBetaGraphs and GuardedHilbertTables. All other 509 scoped entries were
unchanged. During recovery that separate development added
GuardedHilbertCoverage as well. The root independently reviewed each exact
registration-only delta; all seven additions normalize back to the original
b09b748ec0da0da4980558d6d778df950918fb77ef1c4ce9273e68c04642d2a8 hash.
No prior body or dependency clause is excluded from checking.

FINAL-CHECKS.sh passed all 13 recovery/light stages, 18:28:16–18:28:24 UTC,
exit0. Logs are archived in final-checks; live directory
_build/self-consistency-source-provenance-final.ddsFzI. The 509 other entries
agree across fresh before/after/current snapshots. All 503 earlier proof
entries remain frozen, while all three registration files normalize exactly
to their old hashes. Inventory, safety, original kernel, frozen ZFC, HEAD,
note hashes, scoped whitespace and archive-artifact checks pass. This recovery
does not rerun or weaken the already successful fresh recursive proof check.

The earlier light run 18:27:40–18:27:48 returned0, but inspection found an
overescaped word-boundary in its additional safety-scan wrapper. The original
fresh proof scan was correct. That wrapper was corrected and all 13 checks
were rerun; only the latter run is reported as final. Earlier artifacts are
retained in final-checks-01. No proof source changed during this correction.

Registration snapshots are in registration/. The four-entry and six-entry
snapshots are reconstructed from the captured seven-entry file and their
hashes match the actual original run manifests exactly: 4c3ff088... and
cb9d497a... respectively. The captured recovery snapshot is 865c2163... .
The top-level future AUDIT.sh now expects exactly the reviewed seven additions;
any other change still fails. Newly added concurrent proof modules themselves
are informational context only, not claimed as verified by this audit.

No staging, commit, push or cleanup was performed. Build trees, pristine
tarballs, objects, TeX caches and rendered images remain outside this archive.
