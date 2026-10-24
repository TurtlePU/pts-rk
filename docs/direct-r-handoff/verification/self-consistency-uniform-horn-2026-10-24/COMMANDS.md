# Uniform Horn continuation — independent verification

The finalized scope is UniformHorn (19 public proof declarations),
FiniteRawDecoding (31), UniformHornReindex (16), FiniteRawTables (22) and
UniformGuardedHorn (16), with the 104-endpoint aggregate UniformHornAudit and
alias uniform-horn-audit. Root froze these sources; all supplied source hashes
were independently checked. Fresh-run status is recorded below.

Final result: integrated attempt 2 passed, exit 0, with archival exit 0.
It freshly compiled 64 native modules, checked exactly 414 closed assumption
reports and all 104 public Check/Print pairs, and recursively kernel-checked
the full closure with the VM backend enabled. The complete raw kernel
inventory equals pristine upstream; no new axiom or unsafe flag was added.
The retained successful evidence is audit.V54reH; the earlier whitespace-only
failure is preserved separately in audit.9lGA47. This is a focused proof
continuation audit, not full repository CI or an internal consistency proof.

The one-shot CAPTURE.sh completed successfully at 2026-10-23 23:05:58 UTC
(24 October locally). It preserved 549 existing proof/build-registration
hashes, exact self-consistency Audit/Dune and combinatory Dune snapshots,
the dirty worktree/index state, toolchain versions and disk observations.
HEAD is 6a8dc984fb59a9b3743503cd405ffe59a31d1978. No prior proof, source
registration, global handoff document, staged change or commit was modified.
Disk had about 661 MiB free; no cache cleanup was performed.

## Prepared audit contract

AUDIT.sh refuses an unfrozen SCOPE.sh. After root freeze it makes read-only
copies of every driver/scope/gate file and executes only that snapshot.
Each run records exact commands, UTC start/end, exit status and raw logs;
failure propagates explicitly through helper functions. Archived readable
logs have separate byte-exact compressed originals, checked on creation.

The audit compiles a new absolute Dune dependency closure and separately
builds pristine upstream 723cf2ec. It recursively checks every dependency
with the supported VM backend enabled, with no admitted/skipped modules.
The complete raw kernel inventory must equal pristine, and all unsafe
categories must explicitly be empty. The fresh .vo inventory maps back to
identical built/live sources; every Print Assumptions command in that closure
must produce exactly one closed report. The new aggregate's Check and Print
inventories must each equal its public theorem-like declarations.

Every baseline proof body remains fixed. Only additive self-consistency
module/alias registration and one aggregate import are accepted; old Dune
dependencies/registrations and the prior aggregate body remain unchanged.
Concurrent combinatory registrations require explicit review. Source and
immutable-driver hashes are checked before and after verification. This is
a focused continuation audit, not a claim to have rerun full repository CI.

The negative gate tests exercise removed old registrations/dependencies,
duplicate registrations/reports, missing audit aliases/Check/Print lines,
changes to prior audit text, extra axioms, unsafe flags, repeated inventory
markers and missing closed reports, alongside passing controls.

Commands after final scope review and freeze:

```sh
bash docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24/AUDIT.sh
```

Verification of this scaffolding and the actual fresh run will be recorded
separately below; preparation does not establish a Rocq theorem.

## Scaffolding checks

Shell syntax checks pass for CAPTURE.sh, SCOPE.sh, AUDIT.sh and RUN-AUDIT.sh.
`PYTHONDONTWRITEBYTECODE=1 python3 .../GATE-TESTS.py` passes all 18 positive
controls and negative mutations. The unfrozen launcher returns exactly exit
2 without creating a build directory. Supplying two head-hash files as kernel
inventories makes the actual gates.py CLI return exit 1 with the missing-context
diagnostic; it does not accept equality of malformed reports as success.
Exact raw outputs, exit codes and preparation timestamps are retained under
preparation/. No proof compilation or kernel verification is claimed here.

## Final scope preparation and disk estimate

During preparation SCOPE.sh listed the five proposed modules while retaining
HORN_FROZEN=no. The exact permitted changes are their six module registrations
(including UniformHornAudit), one uniform-horn-audit alias depending on
UniformHornAudit.vo, and exactly one new full-audit import line:

```rocq
From PTSrk.SelfConsistency Require Import UniformHornAudit.
```

Existing registration order, theory dependencies, aliases and aggregate bytes
must be preserved. The declaration gate verifies all Check/Print pairs after
the aggregate exists; the counts above are observations, not a substituted
hard-coded coverage assumption.

After root added the five-module registrations, the read-only registration
gate passed against the original baseline (exit 0). Exact output and UTC
start/end are in preparation/additive-registration.*. The aggregate source
and final proof freeze were still pending; no compilation was launched.

DEPENDENCY-SCOPE.py performs a read-only native import walk. For UniformHorn
and FiniteRawDecoding it finds 58 native modules: 12 self-consistency, 18
combinatory, 13 normalization, 5 shared assembler and 10 kernel. Their sources
total 522326 bytes. Existing objects from the working/previous fresh build
cover all but five modules and total 4390688 bytes; this is a partial size
measurement, not a bound. The preceding, larger 74-module fresh combinatory
cache occupies 36 MiB. Current free space is approximately 642 MiB, which
appears adequate for the proposed closure absent concurrent growth. Reindex
and FiniteRawTables dependencies remain to be included after the sources freeze. No disk cleanup
or compilation was performed. Exact estimate output and exit 0 are retained
in preparation/dependency-estimate-01.log and its exit file.

A second provisional walk, including all four existing source files before
freeze, finds 60 native modules (14 self-consistency; other groups unchanged)
and 541597 source bytes. The aggregate will add one module. Its output, UTC
times and exit 0 are retained in preparation/dependency-estimate-02.*;
disk-before-freeze.log records the accompanying disk observation. This remains
an estimate of unfinalized sources, not the decisive compiled closure.

## Worker evidence archival preparation

ARCHIVE-WORKERS.sh is a separate, freeze-gated archival driver. It preserves
exact compressed copies of worker commands, timestamps, exit records, source
snapshots and raw logs; readable companions are explicitly normalized copies.
It excludes compiled objects and caches, checks original hashes and file lists
before and after archival, and labels missing end/exit records incomplete.
It does not modify a running audit driver. It was not run before source freeze.
Its unfrozen refusal was exercised: exit 2, with exact output and UTC
start/end under preparation/worker-archive-refusal.*. Shell syntax passes.

WORKERS.sh records all five isolated worker directories. Read-only
inspection found UniformHorn attempts with exits 1,0,1,0,0; FiniteRawDecoding
attempts 01--12 with exit 1 and 13--14 with exit 0; and Reindex attempts 01--02
with exit 0. These are provisional worker observations, not independent fresh
verification. Final records were copied only after root freeze.

Historical-source limitation: FiniteRawDecoding's per-attempt .source files
record SHA256 hashes, not source bytes. Its worker retains only the final
source snapshot. The failed-attempt logs/commands/times/exits and hashes will
be preserved, but cannot reconstruct those intermediate sources. UniformHorn
and Reindex do retain individual attempt source snapshots. FiniteRawTables
retains source snapshots for attempts 08--13 and final, but only hashes/logs
for attempts 01--07. GuardedHorn retains its attempt source. These limitations
do not apply to a fresh audit of frozen final sources.

## Frozen worker archive

ARCHIVE-WORKERS.sh completed with exit 0 after the five-worker freeze. The
retained archive is workers.RT14Xj; its status.tsv records every available
stage's exact time/exit, and paths.tsv records original directories. Every raw
gzip was compared against the original, and all source hashes/file lists
remained stable. No compiled objects or caches were copied. The final command
output, UTC times and exit are in preparation/worker-archive.*.

The archive preserves all failed stages, including UniformHorn's initial
dune-version command exit 127 (corrected in its later audit02) and the Tables
compilation failures 01--09 and 11. All stage start records have end/exit
records; no incomplete worker stage was silently treated as success.

## Integrated audit attempt 1

Exact launch:
`bash docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24/AUDIT.sh`.
Immutable live run: _build/self-consistency-uniform-horn-audit.WBo9qV;
fresh build: /tmp/pts-rk-uniform-horn-fresh.UZpzNs;
pristine root: /tmp/pts-rk-uniform-horn-pristine.P40hXA;
retained evidence: audit.9lGA47.

The run started 2026-10-23T23:32:42Z and stopped at 23:32:49Z, exit 1;
archival exited 0. Driver hashes, gate regressions, initial source manifest,
all previous proof bodies, additive registrations, all 104 Check/Print pairs
and safety checks passed. The whitespace gate then correctly rejected a new
blank line at EOF of UniformHornAudit.v (line 224). No Rocq compilation or
kernel stage ran. Root was asked to remove only that terminal blank and
refreeze the aggregate; the failed driver/logs remain unchanged.

## Integrated audit attempt 2 — passed

Root removed only the aggregate's terminal blank and refroze it with SHA256
37c786c516fb3ebdd4e4c22793ead72fd76fe97ae5c78fb214b89e2ee6b5bf40.
All five proof-body hashes remained unchanged. The six final hashes are
recorded in frozen-sources.sha256 and were checked before relaunching the
same exact AUDIT.sh command above, with a new immutable driver snapshot.

- Live run: _build/self-consistency-uniform-horn-audit.lD2nv7.
- Fresh absolute Dune build: /tmp/pts-rk-uniform-horn-fresh.cCcZgE.
- Pristine root: /tmp/pts-rk-uniform-horn-pristine.oSFBh4.
- Retained evidence: audit.V54reH, including exact compressed raw logs,
  readable companions, immutable driver, commands and status records.

All stages exited 0. The recorded stage window is
2026-10-23T23:33:49Z--23:35:50Z (24 October locally). Pristine compiled in
2 seconds and kernel-checked in 7; the fresh project build took 69 seconds;
its complete recursive kernel check took 27 seconds. No timeout occurred.
The final execution and archival exit codes are both 0.

The actual compiled closure contains 64 native modules (the earlier import
walk was only an estimate), with exactly 414 closed Print Assumptions reports.
All freshly built source bytes equal the frozen working sources. Aggregate
coverage is exactly 104 Check/Print pairs: 19 UniformHorn, 16 Reindex,
16 GuardedHorn, 31 RawDecoding and 22 RawTables endpoints. Every baseline
proof body, the full source manifest, driver hashes and reviewed additive
registrations remained unchanged throughout. Original kernel sources equal
upstream 723cf2ec and ZFC_model remains byte-identical to ffa7131.

The complete raw CONTEXT SUMMARY is byte-identical to pristine upstream:
predicative Set, no rewrite rules, only the inherited
Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep axiom,
and no type-in-type, unsafe (co)fixpoints or assumed positivity. Kernel
checking used `-bytecode-compiler yes`; no module was admitted or skipped.
All 18 positive/negative gate controls passed again. Source safety and
whitespace checks passed without weakening any gate.

No source cleanup, cache cleanup, commit or push was performed by this audit.
