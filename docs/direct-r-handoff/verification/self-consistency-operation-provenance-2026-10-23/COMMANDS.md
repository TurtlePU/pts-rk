# Comparison and context-operation provenance

Fresh compilation and full recursive checking PASS for seven modules and the
eighty-endpoint aggregate, with complete pristine-inventory equality.
The original attempt 02 is not an all-pass invocation: its build succeeded,
then an in-place driver edit caused Bash to stop before kernel checking.
The recovery below preserves that failure and every integrity-gate failure.
The immutable continuation passes all eighteen stages; final documentation
checks pass all fourteen gates. Both completed output sets are archived.

```sh
bash docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/AUDIT.sh
```

The prepared driver uses the pinned pts-rk-ci environment, a fresh absolute
Dune directory and a separately built pristine upstream snapshot. It records
every exact command, UTC start/end, exit, resolved toolchain, public-declaration
coverage, closed assumption report, full recursive VM-enabled kernel inventory
and before/after source manifest. No kernel dependency is skipped or admitted.
The entire inventory must equal pristine, not merely omit selected axioms.

## Baseline and concurrent work

At 18:36:27 UTC the baseline captured 517 pre-existing named theory sources:
the previous 510 paths plus the seven guarded combinatory modules. Those
modules are being independently audited elsewhere; their inclusion here means
preservation, not a claim that this audit verifies them unless they become
actual dependencies. All 515 bodies/other registrations remain byte-for-byte
frozen. Only the self-consistency Audit import and Dune module/alias additions
may receive a reviewed exact normalization. The current combinatory Dune file,
already containing seven guarded registrations, is frozen at its present hash.
Any further concurrent metadata change must be reviewed explicitly, with raw
failure retained; no old proof body is silently exempted.

The initial informational full-tree snapshot has 518 entries: the comparison
worker had just created InternalComparisonGraph. That new candidate is excluded
from the 517-entry old-source baseline and will be included in the final new
module scope. All later unrelated new modules are informational snapshots,
not automatically part of the verified closure. Baseline registration copies
match their original hashes exactly.

Current HEAD is 6a8dc984fb59a9b3743503cd405ffe59a31d1978. The worktree contains
substantial prior user changes and intent-to-add entries; nothing is staged,
committed, reset or pushed by this audit. Disk headroom was 150 MiB during
preparation. No cleanup was performed. The concurrent guarded-model audit
previously encountered disk exhaustion; all such external status remains
separate from this continuation's proof evidence.

Fresh compile and full kernel process limits are 3600 seconds each, observed
without long silent blocking waits. The older full audit and whole-repository
CI are not part of this scoped verification. All failed experiments and their
commands must remain distinct from the final successful evidence.

## Documentation and scope preparation

The root delegated two narrowly scoped prose corrections after the guarded
combinatory audit completed. README.md and DIRECT_ROADMAP.tex now recognize
the executable fixed finite guarded Hilbert models and rank-at-most-four
original-PTS local-validity certificates. They retain the independent
catalogue/native-source completeness gap, external canonicity boundary and
explicitly open milestone four. No unverified operation-provenance result
was added. The latest guarded live state and ledger were checked first:
fresh fifty-module compilation and recursive checking pass; the original
driver's archival whitespace failure and successful separate recovery remain
distinct. These prose edits have not yet been rebuilt into the roadmap PDF.

The provisional six-module list is NamedBeta, ContextLookupCodes,
InternalContextLookup, ContextLookupRealization, InternalComparisonGraph and
ComparisonGraphRealization, plus OperationProvenanceAudit. The scope remains
unfrozen, and exact additive registration normalization remains intentionally
unfinalized. The driver compares both aggregate Check statements and Print
Assumptions statements against every new public theorem-like declaration.
Shell syntax and scoped whitespace checks pass; no fresh proof audit ran.

## Exact additive registration check

Both audit drivers now normalize only the reviewed single aggregate import,
the exact two-line seven-module registration, and the terminal four-line
alias. Each added block must occur exactly once; the normalized files must
compare byte-for-byte with the original snapshots. Their recovered hashes
are 6d0517ce170899afc7772bef6d7c675f53158003943e1e105d4ca1363d8c3c0a
(Audit.v) and b2e6ff738685ffbff4348b420abe149eaee9be1722027a13f1f9e72de05c6e72
(Dune). No other import, proof or dependency change is exempted.

A registration-only shell experiment initially used
`source <(sed -n '/^registration_normalization()/,/^}/p' "$OPERATION_EVIDENCE/AUDIT.sh")`
followed by `registration_normalization | tee "$OPERATION_LOG/audit-normalization.log"`.
The function was not defined in that shell; the invocation stopped with
`registration_normalization: command not found` (exit 127). It did not run
either audit driver or alter proof sources. The corrected explicit extraction
below passes, exit zero; both normalization functions recover the two exact
baseline hashes. This failure is retained rather than described as a pass.

```sh
set -euo pipefail
OPERATION_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23
OPERATION_LOG=/tmp/pts-rk-operation-registration.0XdIvQ
OPERATION_FINAL_EVIDENCE="$OPERATION_EVIDENCE"
OPERATION_FINAL_LOG="$OPERATION_LOG"
eval "$(sed -n '/^registration_normalization()/,/^}/p' "$OPERATION_EVIDENCE/AUDIT.sh")"
registration_normalization | tee "$OPERATION_LOG/audit-normalization-02.log"
eval "$(sed -n '/^registration_normalization()/,/^}/p' "$OPERATION_EVIDENCE/FINAL-CHECKS.sh")"
registration_normalization | tee "$OPERATION_LOG/final-normalization-02.log"
shasum -a 256 "$OPERATION_EVIDENCE/baseline/Audit.v.snapshot" "$OPERATION_EVIDENCE/baseline/self-consistency-dune.txt"
git diff --check -- "$OPERATION_EVIDENCE"
```

Scope remains unfrozen. No compilation or recursive checking was launched.

## Pending checkpoint and root attempts

At the root's request, BUILD.md and DECISIONS.md received concise explicitly
pending entries covering native NamedBeta helpers, literal contexts versus
certificate serialization, actual-Zip-indexed symbolic Trace outputs, and
the limitations of exact-rank-one Same. No constructor/agreement completion
or fresh integrated verification is claimed.

The root-worker subdirectory archives 73 original text records: CHECK.sh and
codes01--04, beta01--07, symbolic01, each with command/start/end/exit/hash/log.
ARCHIVE-RAW.sh ran successfully; every compressed file's decompressed hash
equals its live original. Independent normalization comparison verifies all
73 whitespace-clean readable copies. No object caches are included. Exact
statuses, including all six failed compiles, are retained. Scoped whitespace
checks pass. This archival work neither changes nor verifies pending proof
sources, and the full fresh driver remains disabled until source freeze.

## Boolean transport helper added before freeze

BooleanAgreement is now the seventh proposed proof module (plus the aggregate).
It factors scope-polymorphic applications of existing Same, reflexivity and
conjunction congruence, avoiding a dependency cycle through realization. Its
eight endpoints include conversion from actual beta equality to exact-rank-one
predicate transport, never the converse. This does not prove the comparison
constructors or their global agreement consumer.

Both exact normalizers and SCOPE.sh now include BooleanAgreement in the first
added Dune line. Registration-only checks again recover the two original
baseline hashes; scope remains unfrozen and no audit ran. The root-worker
archive adds boolean01--04, exit sequence 1,1,1,0, with 24 new readable records
and exact compressed originals. ARCHIVE-BOOLEAN.sh succeeds, and all 97 raw
records independently match their normalized readable copies. Syntax and
readable-archive whitespace checks pass. Earlier 73-file archival evidence
was preserved unchanged.

The first expanded readable-copy comparison stopped with exit 255 at
`readable mismatch: boolean-01.log`: the JSON archival reader had interpreted
UTF-8 bytes as characters in four new log files. Reading those originals
explicitly as UTF-8 corrected the readable copies; compressed originals were
always byte-exact and were not changed. The rerun passes all 97 comparisons
and all archive whitespace/shell-syntax checks. Registration-only logs are
/tmp/pts-rk-operation-registration.Z07vpg, with both normalized hashes equal
to the saved baseline. This archival failure is not a compiler failure or a
successful fresh verification run.

## Completed isolated context module

The source-graph worker was delegated only the context-worker subdirectory
for archival. It contains 140 readable records, 140 byte-exact compressed
originals and four metadata files; all 140 raw roundtrips and normalized
comparisons pass. Final InternalContextLookup attempt13 exits zero at
19:16:41 UTC after starting at 19:12:30 (251 seconds); its report invocation
passes 19:17:13--19:17:14 with exactly 15 closed reports. The repository source
matches 0d0e02f986f0ca28e776356b4648ff77964faf5bd187e8b94246a9fa5be0befb.

All thirteen attempts, wrapped diagnostic failures and source snapshots are
retained, along with the explicit missing-raw-output/timestamp limitation
for unwrapped probe01. These are isolated checks against reused dependencies,
not fresh recursive verification. Read-only final review confirms that the
structural telescope equality changes proof engineering, not the operation
interface, and both scope-template helper parameters are discharged by
previously proved PTS inhabitants. The source-lookup bridge remains standard
realization, not arbitrary internal endpoint coherence. Scoped archive
whitespace passes; the main driver remains unfrozen.

## Overall freeze and fresh attempts

The root froze NamedBeta (11 endpoints), BooleanAgreement (8),
ContextLookupCodes (13), InternalContextLookup (15), ContextLookupRealization
(16), InternalComparisonGraph (14), and ComparisonGraphRealization (3), plus
OperationProvenanceAudit. Both Check and Print Assumptions inventories contain
exactly these 80 declarations. The comparison scope remains the explicit
checkpoint: formation/scoped application, local observation schemata and
standard symbolic output, not Church constructor or arbitrary-Trace folding.

Attempt 01 runs 19:25:25--19:25:39 UTC, exit 1, before compilation. Only the
concurrent combinatory Dune registration differs from the old manifest;
all 514 other nonowned entries pass. Its original driver, exact compressed
logs and readable copies are retained in attempt-01. The root reviewed and
approved precisely eight added MM0 module and .vo registrations, with no
dependency or preceding registration changes. Their exact normalization
recovers baseline hash
865c216310c87178a3a37c1e0ced5f84b3d8e97647b0bf46eef01ec7e90085d5.
No old proof body was exempted and no concurrent file was edited.

Attempt 02 starts 19:27:45 UTC. Logs:
_build/self-consistency-operation-provenance-audit.dLxE0S; fresh absolute
build /tmp/pts-rk-operation-provenance-fresh.DkOoCf; separately built pristine
/tmp/pts-rk-operation-provenance-pristine.Smzrtd. The raw 525-entry before/after
scope includes all 517 preceding paths and eight newly frozen files, including
the live concurrent Dune file. All three exact registration checks pass;
514 other preceding entries remain byte-identical. Complete public coverage
passes, fresh pristine compilation passes 19:27:59--19:28:02 and pristine
kernel checking passes 19:28:02--19:28:08. Aggregate compilation starts next.
Initial disk availability is about 1 GiB; no cleanup was performed.

Completed worker archives are independent of the pending fresh check:
comparison-worker verifies 199 raw/readable records, including 31 attempts
(13 successful, 11 exit 1, seven timeout 124), final source and 14 closed
reports. root-worker/final verifies another 37 records: all five realization
attempts (1,1,1,0,0), latest wrapper and six frozen root-source snapshots.
It preserves the interrupted conversion/Qed, unknown CL.stop and omitted
template-argument failures. All six snapshot hashes match the freeze.

## Final note archive and read-only review

note-final contains fourteen exact raw/readable build/version/log/exit/text
records across the three layout builds and two inspection outputs, with
verified repository TeX/PDF hashes. The first layout produced nine pages
with a root-observed five-line orphan; later builds produced eight pages.
The final inspector reports eight nonempty pages and six links, required
text/mathematics and successful all-page rendering. The ledger attributes
visual review to the root and records missing historical stdout/timing
limitations explicitly. Final built/repository PDFs match; the seven earlier
reviewed page images match the final images byte-for-byte. No PDF, PNG or
build caches were copied into evidence.

The comparison worker also independently reviewed the final note, README
and newest EVIDENCE paragraph read-only. Their wording retains the absence
of Church Trace constructors/full induction, distinguishes standard symbolic
beta agreement from internal Trace realization, and keeps lookup coherence,
original-PTS catalogue completeness and milestone four open. Same remains
exact-rank-one predicate transport, not syntax identity. No overclaim was
found; that review is not a substitute for the pending fresh kernel check.

## Coverage failure-propagation correction

While the unchanged proof compilation was running, the root found a shell
wrapper defect: the first declaration comparison lacked an explicit return,
so run()'s set +e context could mask a Print-list mismatch with a later
successful Check-list comparison. The actual initial eighty-entry lists
match independently; this defect did not hide a real mismatch in this run.
The exact running driver/SCOPE snapshots are preserved in attempt-02-driver.

The reusable AUDIT.sh now explicitly propagates every declaration-generation
pipeline and both comparison failures. FINAL-CHECKS.sh includes the same
coverage gate. DECLARATION-REGRESSION.sh runs both functions under set +e
against the actual files and a retained fixture missing exactly the first
Print Assumptions line while preserving all eighty Check lines. For each
wrapper the actual case returns zero and the 80-versus-79 Print case returns
one, before producing the Check output. The four result directories are
archived in coverage-regression/results: fourteen exact raw/readable outputs
and successful roundtrip/normalization verification. Both source and actual
report lists remain unchanged; no proof rebuild was restarted for this shell
correction. Final checks will independently repeat the corrected coverage.

At 19:43:06 UTC compilation had run 14:58. Its live child was genuinely
computing InternalRenaming.v: elapsed 7:36, CPU time 7:34.69, 98.5 percent CPU,
running state and 1,551,232 KiB RSS. The log advanced from binder to application
proofs; Dune was waiting on the active child, not stalled on a lock or disk.
Fresh output size was 9.1 MiB and disk availability 860 MiB. This expensive
older dependency was absent from the preceding 303-second source-only closure.

## Fresh compilation and immutable continuation

The fresh aggregate build passes at 19:56:57 UTC, after starting at 19:28:08
(1729 seconds). Its output contains 81 closed reports, including all 80 new
public endpoints, and no Axioms/Assumptions section. The driver then exits 2
with an unexpected-EOF diagnostic before launching kernel checking. Editing
the live Bash source during the long compile had changed the byte offsets
from which Bash resumed reading. Both the preserved original driver and the
corrected reusable driver independently pass bash -n; this does not erase
the actual invocation failure. attempt-02-driver/wrapper-failure.log retains
the diagnostic. No proof source or compiled object was changed by the fix.

The first generated continuation candidate also fails bash -n: a JavaScript
replacement string interpreted a shell-regex dollar/quote sequence as its
special suffix substitution. An outer shell lacking set -e then invoked the
invalid candidate, which stopped before checks or kernel execution. Its exact
source is preserved as attempt-02-driver/CONTINUE-candidate01.txt. Literal
line handling corrected the generation; no proof execution was misreported.

The valid first continuation starts at 20:00:47 UTC and stops at its strict
525-path hash gate: all 524 other entries pass, but the concurrent combinatory
Dune registration grew from eight additions to thirteen. continuation-01
preserves six original output records and the unchanged wrapper, with all
seven exact compressed originals and readable copies verified. The root
independently reviewed the baseline diff and approved only those thirteen
module names and their matching vo registrations. No old registration,
dependency or proof body changed; exact normalization again recovers
865c216310c87178a3a37c1e0ced5f84b3d8e97647b0bf46eef01ec7e90085d5.
The five additional concurrent modules are outside the checked closure.

CONTINUE-AUDIT-02.sh starts at 20:02:56 UTC and remains immutable while
running. It uses the SAME fresh compiled tree and pristine snapshot, not a
cached substitute. HEAD stability, all 524 non-Dune raw source hashes, exact
thirteen-registration normalization and a new raw 525-path before manifest
pass. The corrected declaration gate independently compares all eighty
Check and Print entries; the 81-report gate also passes. Full recursive
VM-enabled kernel checking starts at 20:03:03 UTC with no skipped dependency.
The new before manifest pins raw combinatory Dune hash
e918dc5f22ceb03d35b458adecc949e48ac6c8d923b10d7788280f15f1286fa6.
The complete pristine inventory comparison and remaining source/safety gates
were pending at that point. Later prose/PDF updates do not modify these inputs.

## Horn-backend roadmap update

Concurrent checked Horn results prompted the root to reprioritize the roadmap
without changing this frozen proof closure. The separate note-horn-final
archive preserves all four subsequent note builds and inspector exits
133,133,0,0, including the missing qualified-name diagnostic, an uncaptured
initial-call limitation, and the nine-page orphan layout iteration. All 46
raw gzip/readable pairs verify, and all 97 archive files are text or compressed
text/metadata, not PDF/render/cache copies. The final eight-page, six-link
inspection passes. Visual review is attributed to the root; equality of the
built/repository PDF and reused rendered pages 2--6 was checked independently.

The latest repository TeX hash is
85749fa09e186fc31c09da98feafdffc2afa42db7f5a55ff201cd4754b169b2d;
the PDF hash is
97381411194dba5e433ff4819ba784b63effb398c2c2687493fe6d127dc712a8.
FINAL-CHECKS.sh now uses note-horn-final/source.sha256; the earlier note-final
history remains unchanged. This documentation update recognizes arbitrary
represented Horn-proof reflection at a fixed fragment but retains the
original-PTS/source-to-Horn/internal uniformity obligations. It does not claim
milestone four or verification of the concurrent Horn modules by this audit.

## Completed recursive verification

The immutable continuation passes all eighteen stages and exits zero at
20:24:40 UTC. Full recursive checking runs 20:03:03--20:24:26 (1283 seconds),
exit zero. The complete context inventory equals pristine byte-for-byte:
only the inherited functional_extensionality_dep axiom, predicative Set,
no rewrite rules, and no type-in-type, unsafe fixpoints or assumed positivity.
All eighty new reports are closed; the full fresh output contains 81.

The final 525-path raw manifest equals the continuation's before manifest;
all 514 preceding entries outside the three reviewed registration files
(506 Rocq sources and eight older Dune registrations) remain unchanged.
Exact normalization of those three reviewed files recovers their baselines.
Original-kernel, frozen-ZFC, safety and scoped whitespace checks
also pass. No proof, Dune dependency, audit scope or running wrapper was
changed to obtain this result. The original driver and strict-gate failures
remain failures, followed by this explicitly recorded successful continuation.

Final documentation checks pass all fourteen gates, 20:26:43--20:26:50 UTC
(seven seconds), exit zero. They recheck the raw source freeze, preceding
entries, exact registration normalization, all eighty declaration/report
pairs, pristine inventory, original kernel, frozen ZFC, safety, latest note
hashes, whitespace and absence of archived caches. Logs are
_build/self-consistency-operation-provenance-final.o9Z9IF. audit-final verifies
56 exact raw/readable records; final-checks verifies 23. Their twelve and nine
empty logs respectively remain zero bytes. All archival verification and
scoped whitespace checks pass. No commit, push or cleanup was performed.
The final archive-wide scan covers all 709 non-gzip files, including untracked
logs and snapshots: zero trailing-horizontal-whitespace or redundant-EOF
failures; scoped git diff --check also exits zero.
