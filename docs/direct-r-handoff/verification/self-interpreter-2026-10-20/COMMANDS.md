# Self-interpreter research — 20 October 2026

Initial HEAD: ffa7131be99bcbef3f1a787fce23126c3d310811, branch main.
The existing large dirty worktree and concurrent BZC changes were preserved.
Paper commit: 73c4303dca2228bb6b3a8ec6ba5099a86da00bb0. Only the note,
PDF, new preamble and new note-build script are in that commit. No push.
Proofs, CI/README integration, handoff and evidence remain uncommitted.

## Scope

The user supplied Brown and Palsberg's POPL 2016 PDF and requested a note,
compiled PDF, commit and separate Rocq development. After the fixed-head
rank obstruction was found, the user explicitly chose exploring an external
rank-indexed family. Five proof modules plus Audit.v implement the exact
negative result, shallow retraction and genuine indexed STLC precursor.
Full dependent quotation is NOT established. Quotation is a Prop relation
with existence/normality/typing/recovery/injectivity theorems, not extracted
executable code. Injectivity is at each fixed budget.

The closed positive endpoint is ClosedDecoder.closed_every_source_interpreted.
Its only source premise is independent ChurchSTLC.has_type, not original
target typing or an assumed quotation property. The finite budget is proved
to exist. The decoder and its two arguments are actual original closed PTS
terms, and reduction returns the original annotated close t.

## Environment

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Verified versions: OCaml 4.14.2, Dune 3.23.1, Rocq 9.2.0,
Stdlib 9.1.0, Equations 1.3.2+9.2. Full inventories are in versions.log
inside baseline/ and final.P38sk0/. No package installation.

## Pristine baseline and development failures

baseline/RUN.sh retains exact commands to archive pristine upstream
723cf2ec61c737ae82ba33d2e7db44f650122b0e, compile its original Ranks.vo,
check it recursively, and compare it with a fresh RankObstruction build.
All eight stages pass (baseline/status.tsv). The original build directories
are under /tmp/pts-rk-self-audit.jUwKR5; raw copied logs retain those paths.

decoders/COMMANDS.md records every attempt for RankObstruction (1–2),
RankedDecoder (1–5), TelescopeDecoder (1–2) and ClosedDecoder (1–5).
quotation/COMMANDS.md records attempts 1–14 for RankedQuotation.
The first actual compiler error was fixed before proceeding in each series.
All compiler failures remain in adjacent raw logs. Quotation attempt 1's
shell wrapper masked an unknown-target Dune failure; its numeric Dune status
was not separately retained, and the report explicitly says so. Subsequent
attempt statuses and the successful final checks are captured.
No timeout or deliberate interruption occurred in this task's proof builds.

## Final isolated audit

Exact driver invocation, exit 0:

```sh
bash docs/direct-r-handoff/verification/self-interpreter-2026-10-20/RUN-final.sh
```

RUN-final.sh allocates new absolute build and evidence directories on every
invocation. This run used /tmp/pts-rk-self-final.Cxrc4w and final.P38sk0/.
The driver logs exact expanded commands in driver.log. All eight stages pass:
fresh build, core kernel check, whole new library recursive kernel check,
pristine-core comparison, frozen-ZFC comparison, original-kernel comparison,
shell syntax and source-hash stability. status.tsv retains numeric statuses.

The build target is @theories/self_interpreter/audit, including Audit.v's nine
printed public types. fresh-build.log contains 49 closed assumption reports:
39 across the five new proof modules, nine public audit repetitions, and one
upstream core report. The recursive kernel inventory has only unchanged
upstream functional_extensionality_dep. No type-in-type, unsafe fixpoints
or assumed positivity. The source-level theorem reports are individually
closed. A logical loadpath remapping warning is retained in kernel.log.

Source hashes before and after the check match. theories/ZFC_model and the
original kernel sources have no diff against ffa7131. New sources contain
no admitted declarations, axioms, parameters, disabled checks or bypasses.
The source scan's rg exit 1 means no matches, not compilation failure.

## Complete local CI

The first full run passed while the closed-interface module was still being
completed. Its output is in full-ci/ and full-ci-driver.log. It is not the
final verification of that later module.

After all source modules and Audit.v were frozen, reran:

```sh
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/self-interpreter-2026-10-20/full-ci-final bash tools/check-local-ci.sh
```

Exit 0; all 222 stages pass. stdout/stderr are in full-ci-final-driver.log;
full-ci-final/ contains the pristine upstream stage, final new-library stage,
all other existing stages, versions, stages.tsv and result.txt. No CI stage
was removed or weakened. The only task-specific driver edit adds the
self-interpreter audit after normalization complexity. Unrelated concurrent
BZC driver/source edits were preserved. This is a local result, not remote CI.

## Note and PDF

```sh
bash tools/build-self-interpreter-note.sh
```

Final exit 0, /tmp/pts-rk-self-note.Jbrndz. build.log, versions.log and
PTS-rk_self_interpreter.log copied here. LuaLaTeX/latexmk with TeX Live 2026;
six pages. No missing glyphs, unresolved references or overfull boxes.
One underfull paragraph warning remains (badness 1314). PDFKit extracted all
six pages; content checks passed. Rendered pages 1, 4 and 6 were visually
inspected. PNG review artifacts remain in the final temporary directory.

Earlier successful builds remain in /tmp/pts-rk-self-note.T3dud7,
/tmp/pts-rk-self-note.dufqPo and /tmp/pts-rk-self-note.lM1Lv1. They exposed
the missing-author rendering artifact and overfull code spans, which were
corrected in the isolated note preamble/prose. No existing manuscript or
Markdown runtime was edited. note-sha256.txt binds final source/PDF/build
dependencies; note-commit.txt records the exact four-file commit.

## Next work

Implement an executable external quoter with correctness against the STLC
quotation relation. For full dependent PTS-rk, first define the bounded
source fragment independently and solve substitution/conversion coherence;
the current simple-type proof does not do this. The fixed-head impossibility
does not exclude arbitrary externally generated abstraction wrappers or
alternate observational semantics. Do not infer full self-applicability
from interpretation of the simply typed fragment.
