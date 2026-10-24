# Binder-lifted replacement and limits of scope-only soundness

23 October 2026. All six new modules pass isolated compilation, with all
69 new public assumption reports closed. Milestone 1 is complete: fixed-rank
binder-lifted annotated replacement, exact standard substitution, and internal
output-scope preservation. Milestones 2–4 remain open at the hereditary
application/conversion gate described in the paper.

Snapshot 1 was superseded before source edits, **exit 130 at 04:45:34 UTC**,
not passed. Its pristine build/check pass. Snapshot 2 started **04:49:40 UTC**
in the same fresh absolute directory, with Audit.vo absent. Its fresh build
passes **05:43:05 UTC**, exit 0, with **495/495 closed reports** and identical
before/build manifests. Complete new-closure checking passes
**05:29:20–06:11:50 UTC**, 2550 seconds, exit 0, over explicitly source-mapped
coherent isolated objects. Its entire context inventory equals fresh pristine
exactly; all final source/inventory checks pass. No full
repository CI, commit, staging, push or cleanup is part of this continuation.

## Intended contracts and boundaries

- `InternalTermLookup`: one fixed term-valued environment/base, independent
  base/zero/successor rules, and explicit binder depth. The successor clause
  contains the existing annotated shift-renaming graph with the same target
  successor edge. Neither output scope nor the environment bound is a
  constructor premise. The graph has rank 18; its exact rank-12 scope fold
  has a quantified type at rank 19. Recursive lookup is retained for
  operational coverage even though the scope consequence can use the
  independently proved renaming bound without that induction hypothesis.
- `TermLookupRealization`: actual constructor applications and executable
  pointwise lifting for original `Syntax.transpose`; old images use the
  already realized `shift_witness`. The standard single-substitution family
  is constructed from the independently defined original environment, not
  retained as a hypothesis.
- `InternalReplacement`: independent annotated source-directed replacement,
  with fixed environment/base and lifted source/target/depth only in binder
  bodies. The graph has rank 20; its output-scope fold has quantified type
  rank 21. The fold's template takes the previously proved lookup theorem
  as a parameter, then the public closed term **discharges** that parameter
  by original application. This is proof reuse, not an assumed target.
- `ReplacementRealization`: executable original-syntax replacement witnesses
  from a supplied pointwise family; standard single substitution constructs
  its whole family. Decoder and raw-operation bridges identify literal
  endpoints. The substituted-scope witness applies the actual internal fold
  to the constructed graph and environment-bound witnesses.
- `InvariantObstructions`: precise **native Rocq** limits on candidate next
  invariants. Original product ranks force an implication's rank strictly
  above its domain rank; `E -> P` fits the rank of `P` exactly when the rank
  of `E` is smaller. Raising all indices together does not solve a graph-
  premise/motive cycle. Separately, an accepted original conversion
  certificate can detour through an untyped, non-strongly-normalizing term
  while retaining well-typed endpoints. Thus requiring every raw equality
  intermediate to be strongly normalizing would change the checker domain.

These contracts pass isolated compilation and closed-assumption reporting;
the combined checks are recorded separately below. The obstructions rule out those particular invariant choices,
not all fixed-rank internal interpretations. In particular, they are not an
internal PTS consistency theorem. Scope preservation, exact standard
realization and dependent typing/conversion preservation are separate goals.
Dependent soundness, independent operation/resource sufficiency, raw-input
admission, terminal separation and the all-budget internal implication remain
open. Full global functionality/inversion remain optional absent a consumer.

Registered endpoint counts are 9 + 7 + 12 + 11 + 14 + 16 = **69 new**, **495 total**
after the previous 426 reports. The driver's registration check passes for
every new Lemma/Theorem/Example against the actual Audit source. All 69 new
isolated reports are closed; the combined fresh 495-report run also passes.

## Environment and reproducible focused audit

The reusable one-shot driver now allows **7200s for a wholly fresh build**
and 3600s for its full recursive check. Observed constituent compilation
times exceed 3600s when the old closure must also be rebuilt. This future-run
allowance does not alter repository CI, any proof check, or recorded past
limits/statuses. The actual staged snapshot2 continuation retains its
original 3600s build allowance because it reuses already completed unchanged
dependencies. The updated one-shot script is syntax-checked, not claimed
to have passed as one unit.

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
bash -n docs/direct-r-handoff/verification/self-consistency-replacement-2026-10-23/AUDIT.sh
```

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. The driver records actual installed package and
tool versions, HEAD, disk availability, all commands, stage start/end times
and exits. The workspace currently has about 1.4 GiB free; no cleanup is
performed or silently required for success.

For snapshot 1, the following one-shot command was launched after source freeze:

```sh
bash docs/direct-r-handoff/verification/self-consistency-replacement-2026-10-23/AUDIT.sh
```

**Superseded, exit130; not passed.** The script creates one fresh absolute Dune
directory, one fresh pristine tree and one log directory using `mktemp -d`.
At that historical launch, the limits selected upfront were **3600 seconds**
for all-public-report compilation and
**3600 seconds** for complete new-closure checking; pristine build/check
each have 300 seconds. The larger allowance reflects nested replacement
graphs, not removal of proof checks. It does not change repository CI.
There is one fresh build of the audit alias, not a duplicate report build.

The pristine revision is `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
The driver builds/checks pristine `PTSrk.Ranks`, then builds every current
public report using:

```sh
opam exec -- timeout 3600 dune build --build-dir "$SC_BUILD" \
  --display=short --no-buffer -j 2 @theories/self_consistency/audit
opam exec -- timeout 3600 rocq check -silent -o -bytecode-compiler yes \
  -Q "$SC_BUILD/default/theories" PTSrk \
  -Q "$SC_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$SC_BUILD/default/theories/self_consistency" PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.ReplacementRealization \
  PTSrk.SelfConsistency.InvariantObstructions
```

Here `SC_BUILD` is the absolute fresh path assigned and recorded by the
script, not an existing cache. The two roots recursively cover **all six new
modules and their entire dependency closure**. No `-admit` or `-norec` is
used. Supported `-bytecode-compiler yes` still checks all proof bodies, with
the standard VM conversion/serialized-bytecode trust path. It is distinct
from the ordinary conversion path that timed out in an earlier checkpoint.

Successful completion requires actual report-count equality and no reported
axioms in those public reports, complete nonempty context inventories equal
to fresh pristine, original-kernel source equality, a passing safety scan,
and before/after source-manifest equality. Scanner errors fail the run;
missing reports, timeouts and incomplete inventories are not success. The
expected inherited complete-closure inventory is solely upstream
`functional_extensionality_dep`, without unsafe entries, but this must be
confirmed from this run rather than inferred from the previous audit.

This focused check does not repeat kernel checking of unrelated older
optional modules. Their unchanged sources retain their separately recorded
complete checks. Previous renaming/environment verification passed with
426 closed reports and a full new-closure recursive check in 875 seconds;
its exact logs and source manifests are recorded in
`self-consistency-renaming-2026-10-23/COMMANDS.md`. Historical interruptions
and the earlier VM-disabled timeout are preserved, not relabeled successes.

## Actual isolated results

- **InternalTermLookup**, `/tmp/pts-rk-term-lookup.LNt7Ed`: attempt 01 passes,
  exit 0 (`attempt-01.exit`). Its separate assumptions compilation passes,
  exit 0 (`assumptions.exit`), with **9 closed reports** in `assumptions.log`.
  The log reaches the final bound theorem and module end. The final bound
  uses checker fuel 524288; its evaluation and Qed checking take about 171
  and 169 seconds respectively. The process start file is a host-local
  timestamp; `observed-complete-utc.txt` records observation at 04:05:21 UTC,
  not an exact process-end timestamp. No inferred exact duration is claimed.
- **TermLookupRealization**, `/tmp/pts-rk-term-lookup-realization.Q89Jed`:
  attempt 01 passes, **04:05:49–04:10:37 UTC**, 288 seconds, exit 0;
  `attempt-01.start`, `.end` and `.exit` preserve actual times/status.
  `assumptions.exit` is 0 and `assumptions.log` has **7 closed reports**.
  Source manifests are retained alongside the compiled copy.
- **InvariantObstructions**, `/tmp/pts-rk-invariant-obstructions.62zYsp`:
  attempt 01 fails in the reverse direction of `implication_fits_motive_iff`:
  rewriting `r` selected the wrong occurrence, leaving an application whose
  result sort would not unify. Attempt 02 instead constructs the typed
  implication first and rewrites its resulting maximum; it passes, exit 0
  as confirmed by the owning process result. Its assumptions log contains
  **14 closed reports**, prefixed by `Rocq <` because they were printed in
  an interactive session. The separate recursive check passes, exit 0;
  `kernel.log` has a complete inventory containing only unchanged upstream
  `functional_extensionality_dep`, no unsafe entries. This checks this
  module's closure, not the entire new replacement development.
- **InternalReplacement**, `/tmp/pts-rk-replacement.4FJeXN`: attempt 01
  started **04:05:23 UTC** (`attempt-01.start`), with a 2400-second allowance.
  It ended04:45:23UTC, exit124 after2400s, during application checking.
  Binder checking807.268s and Qed836.205s passed, but this is not a
  completed module. No type error was reported. Exact command:

  ```sh
  opam exec -- timeout 2400 rocq compile -time \
    -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories PTSrk \
    -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories/Interpretation_of_R Interpretation_of_R \
    -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories/self_consistency PTSrk.SelfConsistency \
    -Q /tmp/pts-rk-term-lookup.LNt7Ed PTSrk.SelfConsistency \
    -Q /tmp/pts-rk-replacement.4FJeXN PTSrk.SelfConsistency \
    /tmp/pts-rk-replacement.4FJeXN/InternalReplacement.v
  ```

- **ReplacementRealization**, `/tmp/pts-rk-replacement-realization.Fcusuc`:
  launcher attempt 01 exits 127 before invoking Rocq because `opam exec` was
  omitted. Corrected attempt 02 passes **05:10:04–05:28:10 UTC**, 1086 seconds,
  exit 0. Separate fresh assumptions compilation passes, exit 0, with
  **11 closed reports**. Binder telescope equality checking takes 236.345s
  and Qed takes 223.933s; neither is a proof failure. Exact commands and
  timestamps are preserved in the attempt and assumptions logs.

## Snapshot1 — deliberately superseded

The complete driver was launched at **04:14:23 UTC**, process session 18776.
Logs: `_build/self-consistency-replacement-audit.vyvjwb`; fresh absolute Dune
directory `/tmp/pts-rk-replacement-fresh.87Hwa9`; pristine tree
`/tmp/pts-rk-replacement-pristine.k3FQjN`. `status.tsv` preserves each actual
stage result and `commands.txt` its exact invocation. HEAD/version/disk,
81-entry source snapshot, safety and registration checks, pristine archive
and extraction all pass. Pristine compilation passes **04:14:24–04:14:26**;
its VM-enabled recursive check passes **04:14:26–04:14:33 UTC**, both exit 0.
The first fresh build ran04:14:33–04:45:34UTC, then exited130 after a deliberate
SIGINT before adopting template proofs. InternalTermLookup was still checking;
Audit.vo was absent. Subsequent stages did not run. This snapshot is superseded,
not a successful audit.

Before the intentionally extended Audit/Dune registration, all **74 previous
source entries** excluding those two files matched their checked manifest.
The frozen PR#1 ZFC-model comparison passes, and the index remains empty.
Logs: `_build/self-consistency-replacement-progress.aS3W5y`, including
`previous-sources.sha256`, `previous-unchanged.log`, `frozen-zfc.log`,
`index.log`, and the first81-entry `sources-before.log`. Snapshot2
has82entries after adding NamedTemplates. No cleanup or old-proof edits occurred.

## Snapshot2 — verified through the recorded staged/isolated route

The public binder/application TERMS now apply lookup-parametric templates to
actual term_at; graph clauses and literal public TYPES are unchanged. Exact
assembler specialization and original tApp discharge the parameter. No target
hypothesis survives. NamedTemplates adds16 public native syntax lemmas;
InternalReplacement helper lemmas are local.

Naive concrete-body specialization expanded closed payloads and was deliberately
cancelled143: attempt-01, specialize-01 and app-01 in
/tmp/pts-rk-replacement-template.BtTZx5. Generic binder/app templates instead
pass about175/77s including Qed. Exact public-type specialization passes under1s.
The exact scope probe passes04:36:26–04:47:30UTC, exit0, including337.774s
checker/320.2sQed and original application to term_at_bound; two reports closed.
Its logs are scope-01.*. NamedTemplates compiles exit0 in
/tmp/pts-rk-named-templates.c4yc2f. Optimized InternalReplacement passes in
/tmp/pts-rk-replacement-optimized.tifSP4,04:47:42–05:09:34UTC,1312s,exit0,
attempt-01.*. Its separate assumptions compilation has12closed reports,exit0.
Twenty-six graph/scope/public-type declarations were compared literally
against the original isolated source and are unchanged. ReplacementRealization
attempt01 failed127 before Rocq ran (launcher omitted opam exec); corrected
attempt02 passes05:10:04–05:28:10UTC,1086s,exit0, with11closed reports in
/tmp/pts-rk-replacement-realization.Fcusuc.

Snapshot2 started04:49:40UTC, session44302. Exact STAGED-AUDIT.sh,
staged-commands.txt, staged-status.tsv and snapshot2-* logs are in
_build/self-consistency-replacement-progress.aS3W5y. It retains the same
fresh /tmp/pts-rk-replacement-fresh.87Hwa9, reusing only unchanged completed
dependencies. Audit.vo absence was checked; all495 reports will be fresh.
Initial manifest/safety/registration and74prior-source checks pass. Dune passes
04:49:40–05:43:05UTC,3205s,exit0:495freshclosed reports, no axioms, unchanged
before/build manifests. It had3600s; complete new-closure recursive checking
has3600s with the explicit
VM flag and roots above, transitively including all six new modules.
Inventory comparison, original/frozen-ZFC equality and 82-entry before/after
manifest comparison all pass in the independent final continuation below.

### Complete coherent isolated closure

This independent check began **05:29:20 UTC**, overlapping the fresh build.
Its initial source comparison matches all 74 preceding entries, all six
isolated source copies, and the complete 82-entry frozen snapshot. The exact
kernel command, with the pinned environment above, is:

```sh
opam exec -- timeout 3600 rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories PTSrk \
  -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-renaming-fresh.T1RZXE/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-term-lookup.LNt7Ed PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-term-lookup-realization.Q89Jed PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-named-templates.c4yc2f PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-replacement-optimized.tifSP4 PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-invariant-obstructions.62zYsp PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-replacement-realization.Fcusuc PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.ReplacementRealization \
  PTSrk.SelfConsistency.InvariantObstructions
```

The wrapper `/tmp/pts-rk-replacement-realization.Fcusuc/kernel-check.sh`
records `kernel.start`, `.end`, `.exit`, `kernel.log`, complete current/pristine
inventories, inventory-comparison exit, source-copy comparisons and before/after
manifests. The command **passes 05:29:20–06:11:50 UTC**, 2550 seconds, exit 0.
Complete inventory comparison and source stability both exit 0. The inventory
contains only unchanged upstream `functional_extensionality_dep`, with no
type-in-type, unsafe (co)fixpoint or assumed-positivity entries. Both mapping
logs verify all old/new compiled source copies; the full manifest matches the
frozen snapshot before and after checking.

The separate continuation was then run:

```sh
bash _build/self-consistency-replacement-progress.aS3W5y/ISOLATED-CLOSURE-CONTINUATION.sh
```

All **15 stages pass at 06:13:32 UTC**. It independently verifies the fresh
build/report/stability results, all 495 reports, isolated kernel/inventory/
mapping success, both exact snapshot comparisons and complete pristine
inventory equality; then repeats original-kernel, frozen-ZFC, 74 previous-source
and final 82-entry manifest checks. Exact commands, stage exits/times and
success text are `isolated-continuation-commands.txt`,
`isolated-continuation-status.tsv` and `isolated-continuation-success.txt` in
the progress directory.

Only after those passes was the redundant fresh checker (validated PID 19872)
sent SIGTERM. Its actual stage exit is **143**, **05:43:05–06:14:19 UTC**,
recorded in `staged-status.tsv`; command, reason and cancellation timestamps
are preserved separately in the progress directory. That stage is superseded,
not successful. The complete coherent isolated check is the successful
alternative. Snapshot 1 remains cancelled, exit 130, and the earlier isolated
2400-second timeout remains exit 124. No failed or cancelled stage is relabelled
passed; no proof sources changed throughout snapshot-2 verification.

## Paper and native helper checks

NamedTemplates' separate assumptions compilation passes, exit0,16closed
reports in /tmp/pts-rk-named-templates.c4yc2f/assumptions.log. This is not
a substitute for the pending complete new dependency-closure check.

Roadmap build02 passes, exit0, in /tmp/pts-rk-consistency-note.GFlQd9.
The inspector's first02 invocation exited133 because its output directory
did not exist (NSCocoaErrorDomain4/ENOENT), not because of an invalid PDF.
After creating the output directory, invocation02b passes, exit0:17nonempty
pages,7links, required text/math and every-page rendering. Pages13,15,16
were visually reviewed. Exact logs/exits are note-build-02.* and
pdf-inspection-02*/pdf-02 under the progress directory.

Final roadmap build 03 passes, exit 0, in
`/tmp/pts-rk-consistency-note.T9YdGt`, using
`bash theories/self_consistency/build-note.sh DIRECT_ROADMAP`. It includes
the completed substitution result, the rank-feasible whole-history alternative
and its remaining hereditary gate, and the Willard discussion. PDFKit
inspection 03 passes, exit 0: **17 nonempty pages, 7 links**, required
text/mathematics and every-page rendering. Pages 13, 14, 16 and 17 were
visually reviewed; the Willard page was also reviewed after build 02.
Exact logs are `note-build-03.*`, `pdf-inspection-03.*` and `pdf-03` in the
progress directory. `final-note.sha256` records the final source/PDF hashes.

Build 04 supersedes build 03 only to add the closure/stack-machine alternative
and its first dependent-coherence obligation. It passes, exit 0, in
`/tmp/pts-rk-consistency-note.kNYiVl`. Inspection 04 passes, exit 0:
**18 nonempty pages, 7 links**, required text/math and every-page rendering.
Pages 14, 16, 17 and 18 were visually reviewed. Logs are `note-build-04.*`,
`pdf-inspection-04.*` and `pdf-04`; `final-note.sha256` now records this final
source/PDF pair. Exact process start/end times were not separately recorded
for this build; it was observed complete at 05:45:19 UTC. This prose-only
change does not alter the frozen proof snapshot.
