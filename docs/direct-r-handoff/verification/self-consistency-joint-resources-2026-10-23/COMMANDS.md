# Joint traversal, resource bounds and contract boundary

This folder records verification of InternalJointTraversal,
CheckerResourceBounds and ComputationBoundary, and their aggregate
JointResourceAudit. JointTraversalRealization is included only if its proof
completes and remains registered under theories; otherwise the unverified
candidate is archived separately and is not counted as a verified module.
The registered-modules and declaration-coverage audit stages check the exact
compiled scope dynamically. This does not claim that source compilation,
internal dependent soundness or internal consistency has been established.

The fresh audit driver is AUDIT.sh. Run from the repository root with:

```sh
bash docs/direct-r-handoff/verification/self-consistency-joint-resources-2026-10-23/AUDIT.sh
```

The driver records exact commands, statuses, UTC times, resolved versions,
public-declaration coverage, before/after source hashes and full recursive
kernel inventories. It compares the latter against a separately built pristine
upstream tree. All previously audited theory source files are frozen except
the additive self_consistency/Audit.v and Dune registration.

Timeouts are 3600 seconds for the fresh integrated compilation and complete
recursive kernel check. The process remains observable; the long limits do
not authorize silently waiting without progress updates or ignoring a stalled
proof. The unrelated old full audit and repository-wide CI are not run.

The actual registered scope is THREE modules and 59 public endpoints:
InternalJointTraversal (10), CheckerResourceBounds (38), ComputationBoundary
(11). The first module retains only the compiled carrier/constructor,
projection and guard-formation prefix and reusable native helper lemmas. The
full joint-traversal builder and integration are archived as unverified design
files; neither is counted as a verified result.

Fresh run started 2026-10-23 11:17:16 UTC. Live logs:
/Users/akuklev/air/pts-rk/_build/self-consistency-joint-resources-audit.VWulyQ.
Fresh build: /tmp/pts-rk-joint-resources-fresh.TqBIPV.
Pristine build: /tmp/pts-rk-joint-resources-pristine.d7jjko.
All 24 stages passed, exit 0, ending 11:28:25 UTC. Compilation passed
11:17:31–11:22:22 UTC (291 seconds), with 59 new and 60 aggregate closed
assumption reports. Complete recursive VM-enabled kernel verification passed
11:22:22–11:28:19 UTC (357 seconds), with no skipped or admitted modules.
The entire assumption/unsafe-context inventory equals the fresh pristine
inventory exactly: inherited functional_extensionality_dep only, no unsafe
entries. Every new public declaration is covered. All 500 frozen prior source
entries are unchanged, all 506 current before/after hashes match, and the
original kernel, frozen ZFC, safety and tracked/untracked whitespace checks
pass. The unrelated old full audit and repository-wide CI were not rerun.

Exact commands, statuses, timings, inventories and hashes are archived under
audit-final. The pristine source tarball and both build trees remain only in
their live temporary locations, not in the archive. Final documentation/source
light checks passed all ten stages, 11:33:35–11:33:41 UTC, exit 0; logs are
under final-checks (live _build/self-consistency-joint-resources-final.FWuKdZ).
HEAD, all 506 current hashes, all 500 frozen prior entries, original kernel,
frozen ZFC, final note/PDF hashes, changed/untracked whitespace and archive
scope all pass. No checked source changed after fresh verification.

Two earlier final-check runs failed only on an extra empty EOF line in each
of two archived, unverified draft display copies. Those failure logs are
preserved under final-checks-01 and final-checks-02. Only those display-copy
trailing empty lines were removed, with explicit authorization for the full
candidate. Byte-exact originals remain in design/*.original.txt and in the
worker directory; design/README.md records both hashes. No proof was edited,
and no audit check was weakened or skipped.

All interrupted and failed worker attempts are retained under joint/, including
the explicit SIGKILL exit 137, intentional SIGINT exits 1 and uncompleted
proofs. Resource and boundary worker evidence is separate. No objects, build
caches, pristine archives or rendered page images belong in this directory.
