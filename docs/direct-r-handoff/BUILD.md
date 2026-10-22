# Build, logs, and recovery

Direct internal-consistency roadmap (2026-10-22, documentation only):

`bash theories/self_consistency/build-note.sh DIRECT_ROADMAP` final build
exits 0, 12:01:53–12:01:58 UTC, /tmp/pts-rk-consistency-note.O8CmUV.
Eight pages, no overflow/underflow, missing glyph or LaTeX warning.
PDFKit inspector exits 0: eight nonempty pages, four links, required text,
primary citation, no unrendered TeX; all pages rendered and changed formulas/
pagination visually reviewed. latexmk 4.88, LuaHBTeX 1.24.0/TeX Live 2026,
Apple Swift 6.3.3. The optional build argument is limited to README or
DIRECT_ROADMAP; shell syntax check passes, invalid name exits 2 as intended.

Attempts 01/02 compiled but PDF review caught a malformed equation tag;
03 exits 12 because the Markdown display renderer does not permit tag.
Moving the label to prose fixes it; 04/05 compile and inspect successfully.
No validator weakened. Full attempts/hashes/independent mathematical reviews:
verification/self-consistency-direct-roadmap-2026-10-22/COMMANDS.md.
Raw logs: _build/self-consistency-direct-roadmap.HYlErI.

244 original/normalization/self-interpreter/combinatory Rocq/Agda and Dune
hashes compare unchanged. No proof source or original calculus edited;
no new Rocq/Agda/CI/kernel run or internal consistency theorem claimed.
Earlier README.tex/PDF retained. No stage/commit/push; broad user work
preserved. The direct roadmap supersedes priority, not the old target's
provenance or the remaining internal soundness/quantification obligations.

Shared PHOAS fold checkpoint (2026-10-22):

`bash docs/direct-r-handoff/verification/self-interpreter-fold-2026-10-22/AUDIT.sh`
and its documented `--finish` continuation establish the first six modules:
fresh build 11:09:25–11:14:37 UTC, 92/92 fresh public reports at 11:15:07,
recursive kernel check 11:15:07–11:19:55, compatibility audit/source
stability complete 11:32:11. Pristine 723cf2ec61c737ae82ba33d2e7db44f650122b0e
is independently rebuilt. Exact context inventories match; raw log comparison
initially failed only on a preceding logical-loadpath warning. Complete
nonempty CONTEXT SUMMARY extraction fixed the harness without suppressing
raw diagnostics or weakening a proof check.

`GENERIC-AUDIT.sh` adds GenericFold after that source-stable checkpoint.
All previous dependency sources match; new module fresh compile exits 0,
11:34:15–16; 106/106 public reports at 11:34:46; recursive new-module
kernel/inventory equality at 11:35:00; working compatibility audit and final
source stability at 11:35:31. Initial BSD sed basic-regex alternation failure
is retained; portable extended regex fixes the manifest filter. Together
the unchanged checked closure and new kernel check cover every new module.
Only unchanged upstream functional_extensionality_dep in either inventory;
no type-in-type, unsafe fixpoints, or assumed positivity. Rocq 9.2,
Stdlib 9.1, Equations 1.3.2+9.2, Dune 3.23.1, OCaml 4.14.2.
The main script now reproduces all 106 endpoints in one fresh run.

Raw commands/status/stdout: _build/self-interpreter-fold-audit.7pRHdb.
Exact durable commands, incremental failures, source hashes and contracts:
verification/self-interpreter-fold-2026-10-22/COMMANDS.md and sibling
ALGEBRA.md, GENERIC.md, COMBINATORY.md, NOTE.md. No new full-CI claim.
After verification, this run's fresh/pristine temporary directories were
removed (321 MiB); raw logs/manifests retained. The fresh main script
recreates them. Scoped final whitespace passes; unrelated historical raw
combinatory logs explain a separately recorded broader whitespace failure.

`bash tools/build-self-interpreter-note.sh` final build exits 0 in
/tmp/pts-rk-self-note.a3CRxJ: ten pages versus fifteen, 682 source lines,
no overflow/underflow, references, glyph or malformed-math diagnostics.
`bash theories/self_consistency/build-note.sh` exits 0 in
/tmp/pts-rk-consistency-note.7vQRc9: ten pages, clean diagnostics.
New PDFKit inspector renders all pages and verifies required text/primary
citation; changed passages visually checked. No staging/commit/push.

Contextual certificate/finite-package checkpoint (2026-10-22):

`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`
exits 0, 11:04:13–11:04:58 UTC, /tmp/pts-rk-combinatory-agda.xZU85m:
52 project modules, complete safe closure, ignored interfaces, isolated
config/data, stable source copies, no warnings. Earlier .fMhbvK 51-module
run also passed, 10:58:56–10:59:40 UTC. Agda 2.8.0-3d04bac; pinned clean
Cubical v0.9 b150186d. Incremental failures/warnings and structural fixes
are retained; no unsafe bypass or compiler timeout.

`bash theories/CombinatoryLogic-rk/build-note.sh` exits 0,
11:06:27–11:06:41 UTC, /tmp/pts-rk-combinatory-note.5WV08w.
New inspector exits 0: 25 pages, 3-page MM0 appendix, 23 Rocq / 27 Agda
badges, 89 links. All pages render; changed pages visually checked. Initial
1.26pt overfull vbox corrected by shortening the Exact introduction;
stale-PDF and line-break-sensitive inspector failures retained and repaired.
No validation weakened. Exact note commands and review in PDF-REVIEW.md;
full proof commands/failures/source hashes in
verification/combinatory-fragment-soundness-2026-10-22/COMMANDS.md.

All 24 Rocq files/Dune and 38 prior Agda files except import-only Everything
match prior audited manifests. No new Rocq/MM0/full-CI run. No stage/commit/
push; unrelated user work preserved. All-six-rule contextual certificate
soundness and external Void exclusion are proved; fixed finite first-order
model closure and internal checker/compiler reflection remain open.

Total typed Agda/fragment-soundness checkpoint (2026-10-22):

`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`
exits 0, 10:08:50–10:09:32 UTC, /tmp/pts-rk-combinatory-agda.vPyHLe:
39 project modules, complete safe closure with ignored interfaces, isolated
config/data, stable source copies and no warnings. Earlier .KZ77Fr 38-module
run also passed. Agda 2.8.0-3d04bac; pinned clean Cubical v0.9 b150186d.
Incremental failures and fixed indexed-match warnings are retained, not
hidden or suppressed; no compiler timeout/unsafe check bypass.

`bash theories/CombinatoryLogic-rk/build-note.sh` exits 0,
10:11:02–10:11:16 UTC, /tmp/pts-rk-combinatory-note.FofOTf; first .wsHeUv
build also passed. New inspector exits 0: 23 pages, 3-page MM0 appendix,
23 Rocq / 20 Agda badges, 77 links. All pages rendered in
/tmp/pts-rk-total-agda-pdf.Q3NbK2; changed pages 11–16 visually checked
across initial/final renders. No glyph/overfull/reference/highlighting
failure; one unchanged underfull MM0 footnote diagnostic remains.
Commands, logs, hashes and PDF review:
verification/combinatory-total-agda-2026-10-22/COMMANDS.md.

The 24 Rocq sources and Dune match the previous audited manifest byte-for-byte;
no new Rocq/MM0/full-CI build claimed. No stage/commit/push; broad user changes
preserved. Total typed Agda normalization is now complete. Full fragment
model/certificate interpretation and Church/QIIRT/Hilbert adequacy remain open.

Combinatory future-work note update (2026-10-22):

`bash theories/CombinatoryLogic-rk/build-note.sh` exits 0 in
/tmp/pts-rk-combinatory-note.nY0x2K, 09:30:31–09:30:45 UTC; all existing
glyph/layout/reference/highlighting validation passes. New future-work
inspect.swift exits 0, retaining all previous checks and checking every
new requirement and the arXiv:2102.00905 link: 22 pages, 3-page appendix,
23 Rocq / 11 Agda badges, 66 links. All-page renders in
/tmp/pts-rk-future-work-review.ni5QCq; future-work pages 17–18 visually checked.
Initial .JxOvX1 build passed; the final edit removed a one-word page widow.
The first inspector attempt exited 133 only because PDF line-break hyphenation
split Noncollapsed; extraction now normalizes that break, retaining the test.
No compiler failure, timeout or disabled check. Previous Rocq/Dune and Agda
source manifests still match byte-for-byte; no new proof/MM0/full-CI run.
Exact commands/logs: verification/combinatory-future-work-2026-10-22/COMMANDS.md.
No staging, commit or push.

Finite Church compilation checkpoint (2026-10-22):

`bash docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/AUDIT.sh`
exits 0, 19/19, 08:59:33–09:00:25 UTC. Logs _build/combinatory-church-finite-audit.0ceAEs;
fresh /tmp/pts-rk-combinatory-church-finite.aVVCMj; independently rebuilt
pristine /tmp/pts-rk-combinatory-church-finite-pristine.Yk50Y4.
24 modules, 241 own / 242 aggregate closed reports, including 17 new ChurchFinite
reports. Recursive assumptions match pristine byte-for-byte: only unchanged
upstream functional_extensionality_dep. Original kernel/source stability,
safety and whitespace pass. Pinned Rocq 9.2 / Stdlib 9.1 / Equations 1.3.2+9.2,
Dune 3.23.1 / OCaml 4.14.2. No full-CI claim.

`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`
exits 0, 08:59:00–08:59:34 UTC, /tmp/pts-rk-combinatory-agda.4jl4SO:
25 project modules, fresh safe import closure/ignored interfaces, isolated
configuration/data, stable source copies, no warnings. Agda 2.8.0-3d04bac,
clean Cubical v0.9 b150186d.
`bash theories/CombinatoryLogic-rk/build-note.sh`
exits 0, 09:03:29–09:03:43 UTC, /tmp/pts-rk-combinatory-note.2lG4Vk.
New church-finite inspect.swift exits 0: 21 pages, 3 appendix pages, 23 Rocq / 11 Agda badges,
65 links. All pages rendered _build/combinatory-church-finite-pdf-final.DKzMEm;
new pages 13–16, 18 visually checked. No missing glyphs/overfull/undefined
references/highlighting failures. One unchanged MM0 footnote underfull box.

First note .rYmbmc failed layout validation on two wide displays; split them.
Intermediate .NNVuYl/.IKoScA passed build validation; visual inspection found
literal texttt commands in the latter, fixed with Markdown code spans.
Final inspector explicitly rejects that defect. No validator weakened.
The new COMMANDS.md and ChurchFinite-check.txt preserve exact commands,
incremental failure ledgers and remaining obligations. No timeout/commit/push.
No new MM0 check (specification unchanged). The code-to-code programs do
not finish total typed Agda normalization, model soundness or consistency.

Finite IIR Agda and bounded application checkpoint (2026-10-22):

`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`
exits 0, 08:12:27–08:13:03 UTC, /tmp/pts-rk-combinatory-agda.7UFFIh:
23 project modules plus full safe import closure, ignored interfaces,
isolated data/configuration, stable copied sources, no warnings.
Agda 2.8.0-3d04bac and clean Cubical v0.9 b150186d.
`bash theories/CombinatoryLogic-rk/build-note.sh`
exits 0 in /tmp/pts-rk-combinatory-note.5X2knp, 08:17:32–08:17:45 UTC.
LuaHBTeX 1.24.0/TeX Live 2026, latexmk 4.88, latexminted 0.7.0, Pygments 2.19.2.
No glyph/layout/reference/highlighting validation failures.
New verification/combinatory-finite-agda-2026-10-22/inspect.swift exits 0:
18 pages, 3-page complete MM0 appendix, 22 Rocq badges, 17 Agda links (9 proof
badges), 58 links. All-page renders _build/combinatory-finite-pdf.6WaFbZ;
changed pages visually inspected.

First note .bB5vJG failed glyph validation (exit 1) for inline ≤ and Agda ∥;
math-mode prose and local Latin Modern Math fallback repaired the defects.
Intermediate .Nltp4k passed before the final listing-layout adjustment.
No validator disabled. Incremental Agda attempts, failures and exact commands:
verification/combinatory-finite-agda-2026-10-22/COMMANDS.md and module check
records. Final raw logs/source manifests/version reports archived there.
Scoped whitespace, shell syntax and safety scans pass. Existing 23 Rocq
sources/Dune match the prior fresh/pristine audit manifest; no new native,
MM0 or full-CI run claimed. No timeout/staging/commit/push.

The checked finite IIR/typed-fibre injections, raw single-beta peak bounds and
finite-indexed traces do NOT complete the total typed Agda normalizer.
Maybe(Result) remains; native preservation/rank descent and carrier-only
execution remain explicit obligations. No target-shaped premise is added.

Combinatory BCKW arithmetic/QIIRT and Knuth bounds (2026-10-22):
`bash docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/AUDIT.sh`
exits 0, 19/19 stages, 06:36:36–06:37:27 UTC. Logs
_build/combinatory-bckw-audit.Hukon3; fresh 23-module
/tmp/pts-rk-combinatory-bckw.bnSrlP; independent pristine
/tmp/pts-rk-combinatory-bckw-pristine.p0tvSU. 224 own/225 aggregate closed
reports; recursive assumption inventory identical to pristine, only unchanged
functional_extensionality_dep, no unsafe/new assumptions. Original kernel,
source stability, safety and whitespace pass. Pinned Rocq 9.2, OCaml 4.14.2,
Dune 3.23.1, Stdlib 9.1, Equations 1.3.2+9.2. This is a focused audit, not full CI.

`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`
exits 0, 06:31:13–06:31:36 UTC, /tmp/pts-rk-combinatory-agda.Td8Ru5:
all 10 source modules with fresh safe import closure/stable copies.
`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda bash docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/dependent/CHECK.sh`
exits 0 at 06:36:04 UTC; required individual exits 0/42/42/42, exact scope
diagnostics archived. This is not a BCKW nondefinability theorem.
`MM0_RS=/tmp/pts-rk-mm0.lhphPY/upstream/mm0-rs/target/release/mm0-rs MM0_C=/tmp/pts-rk-mm0.lhphPY/mm0-c bash theories/CombinatoryLogic-rk/check-mm0.sh`
passes 4/4, /tmp/pts-rk-combinatory-mm0.FNFzjw, 06:39:23–06:39:24 UTC.
`bash theories/CombinatoryLogic-rk/build-note.sh`
passes in /tmp/pts-rk-combinatory-note.2GZNlI, 06:40:24–06:40:36 UTC.
New bckw inspect.swift passes: 15 pages, 3 appendix pages, 22 badges, 43 links,
all-page renders _build/combinatory-bckw-pdf.RO8PaR; changed pages visually
checked. No layout/glyph/reference/highlighting warnings.

Initial note .yvUk4c failed layout validation on single-dollar display
delimiters; restoring double dollars fixed it. Initial inspector exit 133
was its text expectation “7n+2” instead of extracted “7n + 2”; corrected
test passes. No validator was disabled. Native incremental failures and final
checks are archived in verification/combinatory-bckw-2026-10-22/native;
Knuth and Agda incremental logs are linked from CombinatoryLogic-rk/EVIDENCE.md.
No timeout, staging, commit or push. Full dependent Hilbert replacement,
native completeness, QIIRT coherence/adequacy and MM0 adequacy remain open.

Combinatory affine numerals and finite peak bounds (2026-10-22):
`bash docs/direct-r-handoff/verification/combinatory-bj-bounds-2026-10-22/AUDIT.sh`
exits 0, all 19 stages, 05:25:45–05:26:34 UTC. Logs
_build/combinatory-bj-bounds-audit.4WaD8n; fresh 21-module build
/tmp/pts-rk-combinatory-bj-bounds.TgqGUp; independently rebuilt pristine
/tmp/pts-rk-combinatory-bj-bounds-pristine.de3PBe. 199 own/200 aggregate closed
reports; recursive inventory identical to new pristine, only unchanged
functional_extensionality_dep, no unsafe/new assumptions. Original kernel,
old 17 proof hashes, source stability and safety pass. Pinned Rocq 9.2.0,
OCaml 4.14.2, Dune 3.23.1, Stdlib 9.1.0, Equations 1.3.2+9.2. No full-CI run.
First audit .E63DNW passed proofs but exited 2 at whitespace on two existing
Agda EOF blank lines. Removed only the blanks and reran the unchanged script.
No timeout or weakened check. Incremental failure ledgers and recoverable
generated-artifact relocations are recorded in CombinatoryLogic-rk/EVIDENCE.md.

`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`
exits 0, 05:28:49–05:29:10 UTC, logs /tmp/pts-rk-combinatory-agda.LMgEkR:
all 9 sources, fresh safe import closure, pinned toolchain, stable copies.
`MM0_RS=/tmp/pts-rk-mm0.lhphPY/upstream/mm0-rs/target/release/mm0-rs MM0_C=/tmp/pts-rk-mm0.lhphPY/mm0-c bash theories/CombinatoryLogic-rk/check-mm0.sh`
passes 4/4, 05:28:50 UTC, logs /tmp/pts-rk-combinatory-mm0.asWdz6.
`bash theories/CombinatoryLogic-rk/build-note.sh` exits 0 in
/tmp/pts-rk-combinatory-note.DRrwv0, 05:31:05–05:31:18 UTC; no layout/glyph/
reference/highlighting warnings. New bj-bounds inspect.swift exits 0 with
15 pages, 3 appendix pages, 23 proof badges, 46 links and all-page renders in
_build/combinatory-bj-bounds-pdf-final.Ge5Gtk. Changed BJ/bounds/Horn pages
and references visually inspected. Earlier successful drafts retained.
Shell syntax, scoped whitespace and final proof hashes pass. No staging,
commit or push. These checks do not establish universal typed BJ compilation,
native Hilbert completeness, finite-signature interpretation or MM0 adequacy.

Combinatory safe Cubical signature and reordered note (2026-10-22):
`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`
exits 0, 04:41:14–04:41:34 UTC, logs /tmp/pts-rk-combinatory-agda.M1bpnK.
Agda 2.8.0-3d04bac; Cubical v0.9 b150186d2544e7efeddd31e5d14a8b9ecbb100f7.
All nine source modules and the complete import closure are checked with
--safe and --ignore-interfaces, fresh copied sources and isolated data/config.
Copy/stability hashes pass. S's seven annotation guards and proof irrelevance
are proved; the public family is numeric. General logical-coherence guard
admissibility and native adequacy remain open. No unchecked paper modules
or disabled checks are used. Earlier .ViNmqG/.LsgtLi checks covered I/K/P
only and are superseded. Toolchain and S failure ledgers are in
/tmp/pts-rk-agda-2.8.0.MvVO53/TOOLCHAIN.md and S-DEVELOPMENT-LEDGER.md;
EVIDENCE.md records additional unarchived failures and exits 137/143.
`bash theories/CombinatoryLogic-rk/build-note.sh` exits 0 in
/tmp/pts-rk-combinatory-note.c58OXY, 04:42:55–04:43:06 UTC. PDF inspector
verification/combinatory-agda-2026-10-22/inspect.swift exits 0: 13 pages,
3 appendix pages, 19 proof badges, 40 links and all-page renders. Evidence
_build/combinatory-agda-pdf.QaZM2w; Agda blocks are unbroken and Unicode
highlighting visually checked. No layout/glyph/reference/minted warning.
Initial font/formula failures and intermediate builds remain documented in
CombinatoryLogic-rk/EVIDENCE.md. MM0 recheck .ITdtk4 passes 4/4 stages; the
17 Rocq modules and Dune match the preceding fresh audit. No new full CI or
Rocq assumption audit is claimed. No staging, commit or push.

Combinatory MM0 presentation (2026-10-22):
`MM0_RS=/tmp/pts-rk-mm0.lhphPY/upstream/mm0-rs/target/release/mm0-rs MM0_C=/tmp/pts-rk-mm0.lhphPY/mm0-c bash theories/CombinatoryLogic-rk/check-mm0.sh`
exits 0, 4/4 stages, 03:15:15 UTC. Logs/certificates/source hashes in
/tmp/pts-rk-combinatory-mm0.Bl222O. Official upstream commit
0d414c0bfdaaeb7fea571895127abc1fa5a3d956, mm0-rs 0.1.0, isolated Rust 1.99.1,
mm0-c built with Apple Clang 21.0.0. Specification: 4 sorts, 36 term/def,
55 axiom rules; companion adds two local definitions and ten proved local
theorems, no axioms. Both independent checks compare against the same public
.mm0 source. Negative capture-bug compile/check exits 1/3; exact paths,
commands, tool versions and repeated-build limitations are in
/tmp/pts-rk-mm0.lhphPY/AUDIT.txt. No timeout. These checks do NOT prove a
general MM0/Rocq correspondence, consistency or source completeness.
`bash theories/CombinatoryLogic-rk/build-note.sh` exits 0 in final
/tmp/pts-rk-combinatory-note.rwsq7f, finished 03:16:56 UTC. Fourteen pages,
full source on three appendix pages, highlighted literal Section 4 excerpt,
no layout/glyph/reference/minted warnings. New inspector
verification/combinatory-mm0-2026-10-22/inspect.swift exits 0: 19 proof badges,
35 links, excerpt/source checks and all-page renders. Final evidence
_build/combinatory-mm0-pdf.B8Ovnb. Initial builds FXOv9p and 3ZS6Of compiled
but had rendered inclusion defects, caught by text checks and fixed; details
and hashes in CombinatoryLogic-rk/EVIDENCE.md. The preceding audit's 17 Rocq
files and Dune hash-check passes; no new assumption audit/full CI is claimed.

Combinatory contextual completeness-support continuation (2026-10-22):
`bash docs/direct-r-handoff/verification/combinatory-completeness-2026-10-22/AUDIT.sh`
exits 0, 19/19 stages, 02:24:10–02:25:00 UTC. Fresh seventeen-module build
/tmp/pts-rk-combinatory-completeness.0GagN7 prints 159 own closed reports plus
one unchanged upstream report. Separate pristine archive/build
/tmp/pts-rk-combinatory-completeness-pristine.9z34Nq; recursive checking and
byte-identical inventory comparison pass, only unchanged upstream functional
extensionality and no unsafe entries. Original sources, stability, safety and
whitespace checks pass. Logs _build/combinatory-completeness-audit.fG2a7B.
Initial audit _build/combinatory-completeness-audit.Ko2LoS exits 1 in fresh-build
at a CatalogueShapes Ltac name collision, now fixed. Other targeted failures
and exact commands are retained in the current CombinatoryLogic-rk/EVIDENCE.md.
All eleven preceding proof modules are byte-identical to the previous audit.
Full `bash tools/check-local-ci.sh`, with DIRECT_R_LOG_DIR set to
_build/combinatory-completeness-full-ci.1noh6m, exits 0: actionlint and all
227 stages pass without retry; exit-file timestamp 02:24:40 UTC. No CI stage
was weakened. This is full-driver coverage, not new assumption evidence for
cached unrelated developments. No timeout occurred. The mathematical external
completeness corollary is not a Rocq theorem; general chain shortening and
deduction admissibility remain open despite the successful audit.
`bash theories/CombinatoryLogic-rk/build-note.sh` passes in final
/tmp/pts-rk-combinatory-note.xQ0lm0, finished 02:30:59 UTC. Ten pages,
genuine Agda Pygments highlighting, no overfull/glyph/reference/minted warnings.
The new verification/combinatory-completeness-2026-10-22/inspect.swift passes:
nineteen local proof links, eleven references, all pages rendered; changed
pages 5–10 visually inspected. Evidence _build/combinatory-completeness-pdf.mMbycs
also retains the Agda compatibility probe (exit 1, installed 2.6.0.1 fails
the paper's unchanged 2.8.0 artifact at Prelude:47). This is not an Agda
verification claim. Exact commands and final hashes: CombinatoryLogic-rk/EVIDENCE.md.

Combinatory GAT/catalogue continuation (2026-10-22):
`bash docs/direct-r-handoff/verification/combinatory-gat-2026-10-22/AUDIT.sh`
exits 0, all 19 stages pass, 01:36:23–01:37:09 UTC. Fresh eleven-module build
/tmp/pts-rk-combinatory-gat.hDbC80 prints 92 own closed reports plus one
unchanged upstream report. Separate pristine snapshot
/tmp/pts-rk-combinatory-gat-pristine.bwllE6, recursive kernel/inventory checks,
original-source comparison, source stability and safety checks pass; no new
or unsafe assumptions. Logs _build/combinatory-gat-audit.FoWhA6.
Complete local CI/actionlint, with DIRECT_R_LOG_DIR set to
_build/combinatory-gat-full-ci.ZhCicn, exits 0: 227/227 stages, no retry,
01:36:24–01:36:53 UTC. Cached unrelated targets are not new assumption evidence.
`bash theories/CombinatoryLogic-rk/build-note.sh` passes in final
/tmp/pts-rk-combinatory-note.B5iS8i, nine pages, no LaTeX/layout/reference/glyph
warnings. New inspector verification/combinatory-gat-2026-10-22/inspect.swift
passes on the final PDF: thirteen local proof links, eight reference links,
all pages rendered and visually inspected. Final inspection directory
_build/combinatory-gat-pdf-final.wm5Jze; prior drafts retained separately.
The exact QIIT signature stays together on page 8 and references on page 9.
Pseudocode is not kernel verification. Exact commands, versions, failures,
layout attempts and hashes: theories/CombinatoryLogic-rk/EVIDENCE.md.
Only proof compiler failure: economy Ltac alias matching, fixed; no timeout.

Combinatory Hilbert continuation (2026-10-22):
`bash docs/direct-r-handoff/verification/combinatory-hilbert-2026-10-22/AUDIT.sh`
exits 0, all 19 stages pass, 00:59:24–01:00:00 UTC. Renamed target
@theories/CombinatoryLogic-rk/audit retains PTSrk.Combinatory. Fresh build
/tmp/pts-rk-combinatory-hilbert.ZBLheh prints 51 own closed reports plus one
unchanged upstream report. Separate pristine build
/tmp/pts-rk-combinatory-pristine.iMsccY, all-six-module recursive kernel checks,
inventory/source comparisons, source stability and safety checks pass; no new
or unsafe assumptions. Logs: _build/combinatory-hilbert-audit.H87sn7.
Complete `bash tools/check-local-ci.sh`, with DIRECT_R_LOG_DIR set to
_build/combinatory-hilbert-full-ci.OO1Ub7, exits 0: 227/227 stages including
new 01-combinatory and actionlint, no retry, 00:59:31–01:00:01 UTC. Existing
targets mostly cached; fresh focused evidence supplies new assumption output.
`bash theories/CombinatoryLogic-rk/build-note.sh` exits 0 in final
/tmp/pts-rk-combinatory-note.Y2Kfbl, five pages, no layout/reference/glyph or
LaTeX warnings. PDFKit text/link/render check exits 0: nine local source links,
three reference links; all pages visually inspected. Inspection evidence:
_build/combinatory-hilbert-pdf.dyMANc. Exact commands, toolchain, failed
attempts and hashes: theories/CombinatoryLogic-rk/EVIDENCE.md. No timeout.

Combinatory formulation (2026-10-22):
`bash docs/direct-r-handoff/verification/combinatory-2026-10-22/AUDIT.sh`
exits 0, all 17 focused stages pass, 00:35:48--00:36:22 UTC. Fresh target
@theories/Combinatory/audit in /tmp/pts-rk-combinatory-audit.vEp9MB prints
32 own closed reports plus one unchanged upstream report. The separately built
pristine snapshot /tmp/pts-rk-combinatory-upstream.AkuTX9 and all three new
modules pass recursive kernel checks with byte-identical assumption inventories;
only unchanged upstream functional extensionality, no unsafe entries. Original
kernel source and final source/Dune stability checks pass. Raw logs:
_build/combinatory-audit.ZXAnfW. Same-source dependency-path warnings retained.
Exact commands, failed attempts, versions and hashes: theories/Combinatory/EVIDENCE.md.
No new full staged local-CI result; existing driver and running work preserved.

Uniform closure/numeric-budget continuation (2026-10-22): all six new modules
and the expanded aggregate compile. Fresh compilation used
/tmp/pts-rk-self-uniform-audit.ZjpFUy: prebuild 1032 closed reports,
interface stage 74, final aggregate stage 1601, for 2706 own plus one unchanged
upstream report. The final aggregate ran 00:18:36--00:27:35 UTC, exit 0;
1112 public Check/Print pairs and 129 source/Dune manifest entries.
Both recursive kernel checks pass, with interpreter checking
00:27:42--00:36:42 UTC, exit 0. Historical and freshly rebuilt pristine
inventories agree; original frozen-source comparison and all 129 source
stability checks pass. Own endpoint assumptions are closed. The global loaded
inventory has only unchanged upstream functional extensionality and no unsafe
entries. Complete local CI/actionlint passes 226/226 stages, exit 0, without
retry (00:18:35--00:24:56 UTC). No CI driver was weakened or edited by this work.
The final self-interpreter note builds warning-free to 15 pages in
/tmp/pts-rk-self-note.PKoaj6; PDF text/link/render checks pass. The consistency
note status update builds warning-free to ten pages in
/tmp/pts-rk-consistency-note.7u3pxt. Raw evidence:
_build/self-interpreter-uniform-interface-2026-10-22.
Exact commands, early targeted-log limitations and remaining obligations:
[uniform interface evidence](verification/self-interpreter-uniform-interface-2026-10-22/COMMANDS.md).
The completed 627 MiB audit cache and 2 MiB independent pristine snapshot
were removed after verification; logs and the working build remain. Recreate
them with the recorded pristine/prebuild commands before a fresh recheck.

Internal-consistency research note (2026-10-22):
`bash theories/self_consistency/build-note.sh` exits 0; final temporary
directory /tmp/pts-rk-consistency-note.KlGtoS. Nine-page README.pdf has no
overfull/underfull boxes, LaTeX warnings or missing glyphs. PDFKit text,
section/source-link and rendering checks pass; pages 1,3,5,7,9 visually checked.
Script syntax validation passes. Versions: latexmk 4.88, LuaHBTeX 1.24.0,
TeX Live 2026. Raw inspection: _build/self-consistency-note-2026-10-22.
All attempts, source map and hashes: theories/self_consistency/EVIDENCE.md.
Documentation only: no new Rocq/Dune module or proof/CI audit is claimed.

Capped-quotation continuation: all eight new modules and the incremental
aggregate compile. Fresh aggregate compilation in
/tmp/pts-rk-capped-audit.lpDpbN exits 0 (10:09:50--10:19:47 UTC), with
2549 own closed reports plus one unchanged upstream normalization report.
The core recursive kernel check exits 0 and matches pristine upstream.
The aggregate recursive kernel check exits 0 (10:19:54--10:28:56 UTC).
Own endpoints are closed; only unchanged upstream functional extensionality
appears in the loaded inventory, with no unsafe entries. Original proof
comparisons, all 123 source/Dune stability checks and FINAL-CHECKS pass.
Full local CI/actionlint passes all 226 stages, exit 0, on retry after an
initial Dune concurrency-lock failure. The unchanged driver and all failed
attempt logs are retained. The note builds to 13 pages without layout,
reference or glyph warnings in /tmp/pts-rk-self-note.KAJfjK; PDFKit inspection
passes and changed pages are visually checked. Raw output:
_build/self-interpreter-capped-quotation-2026-10-21.
Exact commands, failures and source/publication boundaries:
[capped quotation evidence](verification/self-interpreter-capped-quotation-2026-10-21/COMMANDS.md).

Fragment-uniformity continuation: all three new proof modules compile
incrementally with closed assumption reports. Fresh aggregate compilation in
/tmp/pts-rk-fragment-audit.umlOaP exits 0: 2347 own closed reports plus one
upstream report. Both recursive kernel checks, pristine inventory comparison,
original proof comparisons and 115-entry source stability checks pass.
Own assumptions are closed; no new or unsafe kernel inventory entries.
Full local CI exits 0, all 226 stages PASS.
The note builds to 12 pages without TeX layout/reference/glyph warnings;
final TeX directory /tmp/pts-rk-self-note.k3lPRz. PDF text/render inspection
passes; changed pages visually checked. Raw logs:
_build/self-interpreter-fragment-uniformity-2026-10-21.
Exact commands, failures and current verification status are in
[fragment evidence](verification/self-interpreter-fragment-uniformity-2026-10-21/COMMANDS.md).

Latest self-interpreter improvement check: all modified targets compile and
full local CI passes all 226 stages, exit 0. Fresh aggregate audit in
/tmp/pts-rk-self-improvements-audit.vjkEgS passes with 2287 own closed reports
plus one upstream report. Core/aggregate recursive kernel checks, pristine
inventory and original proof comparisons pass. All 112 manifest entries are
stable. FINAL-CHECKS exits 0 after correcting an overbroad Git pathspec in the
audit's original-source comparison. Raw logs:
_build/self-interpreter-improvements-2026-10-21.
Extracted sort checks pass; lambda/application each timeout at 30 seconds,
exit 124. Direct enumeration computes 68/1209 trees at sizes 5/7. The updated
11-page note builds without TeX layout/reference/glyph warnings; changed pages
visually checked. Exact commands and all prototype failures:
[improvement evidence](verification/self-interpreter-improvements-2026-10-21/COMMANDS.md).
The enclosing scoped publication commit is based on f5fdac0c; publication was
requested after these checks completed.

Latest editorial check: the streamlined self-interpreter note compiles to
11 pages (formerly 42). All four fresh note builds pass; final directory
/tmp/pts-rk-self-note.0KH9o2. PDFKit text/render checks pass, and the final
log has no overfull/underfull boxes, LaTeX warnings or missing glyphs.
Proof sources are unchanged; no new Rocq/CI build is claimed.
[Exposition evidence](verification/self-interpreter-exposition-2026-10-21/COMMANDS.md)
records commands, review scope and hashes. The user requested publication;
the enclosing scoped commit is based on 2da7627.

Latest documentation-only check: the Brown--Palsberg/CPS discussion builds
successfully in three fresh TeX directories, final
/tmp/pts-rk-self-note.pVKShq, 42 pages. PDFKit renders discussion pages 35--41;
final build has no overfull boxes, LaTeX warnings or missing glyphs.
No Rocq/Dune/core source changed, and no new proof/CI result is claimed.
Exact commands, versions and hashes:
[discussion evidence](verification/self-interpreter-discussion-2026-10-21/COMMANDS.md).
The user requested publication; the enclosing scoped commit is based on ade6387.

Publication scope: the enclosing commit contains the verified self-interpreter
sources and documentation. Its proof sources match the retained fresh audit.
The226-stage complete CI report was obtained in the shared worktree;54stages
belong to unpublished BZC changes. Those sources/script changes are excluded.
The published CI already runs the self-interpreter audit. See newest STATE.

Current self-interpreter milestone: full original-source dependent interpretation
now compiles in FullDependentInterpreter (14closed), with actual six-case
RecursiveQuotation (4closed/kernel0), original closure/open recovery and
syntax fidelity. Indices include finite numeric plans, not just ranks.
Complete CI passes226/226, exit0, under
_build/self-interpreter-open-telescope-final-review.d0SH8N. Fresh aggregate
retry passes with2230closed reports:2229self-interpreter plus unchanged
upstream Ranks.strong_normalization. Recursive kernel/pristine/frozen
comparisons all pass, as do110-entry source stability and final checks, under
_build/self-interpreter-open-telescope-final-review-retry.mfFz4Q.
The first fresh audit failed from disk exhaustion, not a proof rejection;
its log is preserved. Completed scoped Dune caches were cleaned, sources/raw
logs retained, and the successful final aggregate was built in the new empty
/tmp/pts-rk-self-open-telescope-audit-retry.cdzdRH. Audit has885public pairs.
Note-04/PDFKit inspection exit0,37pages; updated theorem/abstract/boundaries
visually checked. See newest STATE entry and final-review/COMMANDS.md.

Canonical publication e822cd6 is confirmed on local main AND origin/main;
the pending ordinary push exited 0 and the Keychain pause is resolved.
See [publication evidence](verification/self-interpreter-canonical-publish-2026-10-20/COMMANDS.md).

Earlier open-telescope intermediate checkpoint (superseded above): arbitrary open-body telescope recovery,
concrete contextual beta application, executable ORIGINAL typechecking,
checked equality-only contextual layers, typed finite Pi views and structural
view substitution now compile. The generic dependent decoder has actual
ordinary P/Q arguments, direct original typing, exact type rank, normality
and literal payload recovery. Root's two scoped recursive kernel checks pass;
only unchanged upstream functional extensionality occurs in the loaded
inventory, with all own endpoint reports closed. Individual records are under
verification/self-interpreter-open-telescope-2026-10-21. Current work is the
six-case source recursion and numeric-layer integration. No full interpreter,
general no-go, new aggregate audit or new full CI is claimed. The expanded
note/PDF builds successfully; pages29–30 visually checked. FaithfulProgramDecoder
and SourceQuotationBudget also pass scoped recursive kernel checks (12/10 own
closed reports). LocalQuotationSpine and NormalEqualityFill pass26/6 own closed
reports plus scoped kernel checks. Current endpoint remains unfinished.
New-module aliases caused severe compilation environment duplication; coordinated
qualified-name expansion and refreshed source checks are underway. Seven exact
completed caches were cleaned, logs retained separately; current caches are live.

Preceding self-interpreter checkpoint: contextual cast-beta laws under arbitrary
dependent telescopes, independent identity programs, normal domain-family
parameters and their constructive actual instantiation, plus a finite
length/rank-vector-only contextual signature. Eleven new modules compile
with 187 closed own reports; all independent contract reviews pass. Fresh
aggregate: 1140 closed reports, 340 aggregate endpoints. Recursive kernel,
pristine inventory and frozen original/ZFC/NormalizationComplexity comparisons
pass; all 68 proof/Dune manifest entries are hash-stable. Full local
CI/actionlint passes 226/226 stages. See the newest
STATE entry and [contextual-beta evidence](verification/self-interpreter-contextual-beta-2026-10-21/COMMANDS.md).
Note/PDF: 33 pages, successful build and visual inspection. No Git/index
mutation; this and five prior local milestones remain uncommitted after
e822cd6. Arbitrary open-body telescope instantiation and full recursive
dependent quotation/coherence remain open.

Preceding self-interpreter checkpoint: predicative equality lowering/reversal,
synchronized dependent graph equality, restricted common-map binder/product
congruence, executable original source substitution and a graph-equality
bridge from the ACTUAL finite beta-law fields. Literal identity computation
and original typings are checked; arbitrary dependent-binder coherence and
full quotation remain open. Fresh audit: 895 closed reports, 282 aggregate
endpoints; recursive kernel/pristine/frozen-source checks pass, all 57
proof/Dune files hash-stable. Full local CI/actionlint: 226/226 stages pass.
Note/PDF: 31 pages, build and visual checks pass. No Git/index mutation; this
and four preceding local milestones remain uncommitted after e822cd6.
Exact commands, failures, versions, hashes and theorem boundaries:
[dependent-coherence checkpoint](verification/self-interpreter-coherence-2026-10-21/COMMANDS.md).

Preceding self-interpreter checkpoint: arbitrary-scope smart operations, exact
full-original computational source derivations, executable typed forward
conversion joins and recursive conversion-evidence canonicalization preserving
literal annotated syntax. A cubic finite beta-law extension has actual
closed normal identity inhabitants and constructive typed fill. Fresh audit:
800 closed reports, recursive kernel/pristine/frozen-source checks pass,
all 52 proof/Dune files hash-stable. Full local CI/actionlint: 226/226 stages
pass. Note/PDF: 28 pages, build and visual checks pass. No Git/index mutation;
this and three preceding local milestones remain uncommitted after e822cd6.
Full dependent quotation and internally generated binder/substitution/conversion
coherence remain open. Exact commands, failures, hashes and boundaries:
[source-conversion checkpoint](verification/self-interpreter-conversion-2026-10-21/COMMANDS.md).

Preceding self-interpreter checkpoint: normal closed sort quotations, concrete
variable-preserving dependent signature extensions, smart local dependent
binders with normal annotations and local input fidelity, and a typed neutral
cast-roundtrip nonconversion regression. Fresh aggregate: 646 closed reports;
recursive kernel/pristine/frozen-source checks pass, all 46 proof/Dune files
hash-stable. Full local CI/actionlint: 226/226 stages pass. Note/PDF: 26 pages,
build and visual checks pass. This and the preceding two local milestones are
uncommitted after e822cd6; no Git/index mutation. Full recursive dependent
quotation and generated source-conversion coherence remain open. Commands,
all compiler failures, versions, hashes and exact theorem boundaries:
[dependent-binder checkpoint](verification/self-interpreter-binders-2026-10-20/COMMANDS.md).

Preceding self-interpreter checkpoint: finite normal original Tarski signature,
exactly 4(k+2)+2(k+1)^2 fields, concrete typed identity instantiation, actual
applied product/law/Abs/App operations and literal substitution recovery.
Homogeneous equality composition and nondependent congruence are checked.
Fresh aggregate: 527 closed reports; recursive kernel/pristine/frozen-source
checks pass, all 42 proof/Dune files hash-stable. Full local CI: actionlint
and all 226 stages pass. Note/PDF: 24 pages, build and visual checks pass.
This and the preceding local milestone are uncommitted after e822cd6; no
new commit/push/index mutation. Full dependent quotation and generated
conversion coherence remain open. Exact commands/failures/versions/hashes:
[finite-signature checkpoint](verification/self-interpreter-signature-2026-10-20/COMMANDS.md).

Preceding self-interpreter checkpoint: seven modules construct actual original
Tarski product/universe codes, rank-indexed equality and two-way casts,
closed normal transport programs, and actual identity witnesses with literal
Abs/App beta recovery. A separate beta-only eta regression protects the
dependent-index boundary. Fresh absolute aggregate: 418 closed reports;
recursive kernel/pristine inventories and frozen-source checks pass. Full
local CI: actionlint and all 226 stages pass. Note/PDF: 22 pages; build and
visual checks pass. New work is uncommitted after the confirmed publication.
Exact commands, every failure, versions, hashes and remaining finite-palette /
source-coherence obligations:
[Tarski checkpoint](verification/self-interpreter-tarski-2026-10-20/COMMANDS.md).
This is local object-language infrastructure, not full dependent PHOAS.

Preceding self-interpreter checkpoint: full dependent original-PTS open-context
canonical normalization, typed hereditary substitution, normalized contexts
with bidirectional literal typing transport, and distinct faithful syntax /
conversion-canonical type indices. These are metalevel operations, not an
internal dependent PHOAS evaluator. Fresh aggregate audit: 326 closed reports;
recursive kernel, pristine core inventory and frozen-source checks pass.
All 226 current-root CI stages and actionlint pass. Updated note/PDF: 20 pages.
Exact commands, failures, versions, hashes and next mathematical boundary:
[canonical-interface checkpoint](verification/self-interpreter-canonical-2026-10-20/COMMANDS.md).
New continuation is uncommitted after the separately completed publication.

The user's requested commit/merge/commit/push is complete at b6c81d1 on
origin/main, including actual two-parent merge 64864e3 of docs/finished-developments.
The clean published snapshot passes all 172 stages; it excludes unrelated
unpublished developments present in the 226-stage root workspace. Details:
[publication checkpoint](verification/self-interpreter-publish-2026-10-20/COMMANDS.md).
Raw logs remain local in /tmp/pts-rk-self-publication.KX9EQK; the fresh build is
/tmp/pts-rk-self-publication-build.GMOcrx. The source merge was published by the
parent; this later evidence/handoff update awaits its separate evidence commit.

Latest self-interpreter checkpoint: finite closed indexed PHOAS for independent
Church-STLC, with normal syntax-injective quotes and an actual closed strong
decoder indexed by budget AND full simple type. No semantic payload is
precomputed. Genuinely dependent local handlers and a limited shared-map
conversion obstruction are also checked; full dependent indexed PHOAS remains
open, not ruled out. The original development worktree's fresh aggregate audit
has 264 closed reports; recursive kernel, pristine core comparison and frozen
ZFC/original-core checks pass. Its actionlint and 226-stage CI passed, including
unrelated unpublished stages. The isolated publication instead contains the
171 committed baseline stages plus the self-interpreter audit; its successful
separate 172-stage verification is recorded in the publication checkpoint above.
Updated note/PDF: 18 pages. Exact commands, failures, versions, hashes and limits:
[finite PHOAS checkpoint](verification/self-interpreter-phoas-2026-10-20/COMMANDS.md).
Historical raw-log paths refer to locally retained evidence, not additional
committed source files. Concise reports and selected provenance are published.

Finished-development documentation: `bash tools/build-development-docs.sh`
rebuilds the five README.tex/PDF pairs indexed by docs/developments/README.md.
The final build gives 38 pages and passes log, PDF text and visual checks.
A fresh audit of every finished library passes with 1,127 closed reports
and recursive kernel checking. Full local CI in the shared checkout at that
documentation checkpoint stopped at a concurrent self-interpreter error;
that observation does not describe this isolated publication checkout.
Exact commands, failures, local logs and cleanup recovery details are in
[the documentation checkpoint](verification/development-docs-2026-10-20/COMMANDS.md).

## Inspect and preserve

From the repository root inspect git status, branch, recent commits, actual
module files, and Dune configuration. Preserve existing user changes. Record
the checkout, available toolchain, and relevant logs in STATE.md. Never reset
to a historical base or expose credential-bearing URLs or environment values.

## Current layout

All project Rocq sources are under theories:

- theories/*.v: original PTSrk kernel.
- theories/Interpretation_of_R/: shared arithmetic infrastructure.
- theories/Interpretation_of_R/relational/: completed Theorem 4.
- theories/Interpretation_of_R/functional/: completed Theorem 7 and effective
  Theorem5Target witnesses.
- theories/ZFC_model/: original set-model typing soundness and open material
  BZC foundation reduction.
- theories/NormalizationComplexity/: costed normalization bounds and STLC
  conversion reduction.
- theories/self_interpreter/: faithful raw HOAS, full-PTS weak interpretation,
  finite closed indexed STLC PHOAS with strong unquotation, genuinely dependent
  local handlers and precise obstructions; full dependent interpretation open.

See [theories/README.md](../../theories/README.md). Rocq library names are
unchanged by the physical moves. Both arithmetic libraries depend on shared
infrastructure and the original kernel, not on each other.

## Toolchain and complete check

The pinned configuration is OCaml 4.14.2, Dune 3.23.1, rocq-prover meta.1,
rocq-core 9.2.0, rocq-stdlib 9.1.0, and rocq-equations 1.3.2+9.2.
Stdlib is independently versioned. Rocq 9.1.1 cannot parse pristine upstream's
Create Rewrite HintDb command.

```sh
bash tools/check-local-ci.sh
# Or, inside an already activated Rocq/Equations switch:
opam exec -- bash tools/ci-check-direct-r.sh
```

The local wrapper selects the dedicated pts-rk-ci switch and runs actionlint
plus the staged build. The CI driver archives pristine upstream commit
723cf2ec61c737ae82ba33d2e7db44f650122b0e into a separate temporary directory
and compiles it before the current developments. It stops at the first actual
failure and retains exit codes, versions, stage logs, and Dune output.
GNU timeout must be available. See [DirectR-CI.md](../DirectR-CI.md) for setup,
platform details, environment overrides, and the Actions workflow.

A timeout is a diagnostic resource limit, not a compiler rejection. A local
successful run does not by itself assert remote CI success.

## Targeted checks and fresh assumptions

From the repository root in the configured environment:

```sh
dune build theories/Ranks.vo
dune build theories/Interpretation_of_R/DirectREval.vo theories/Interpretation_of_R/DirectRCheck.vo
dune build @theories/Interpretation_of_R/relational/audit
dune build @theories/Interpretation_of_R/functional/audit
dune build @theories/ZFC_model/audit
dune build @theories/NormalizationComplexity/audit
dune build @theories/self_interpreter/audit
```

Use a NEW absolute --build-dir for fresh compilation and assumption output.
A cached successful audit does not rerun Print Assumptions. Record exact
public theorem types and transitive reports, distinguishing upstream logical
assumptions from any newly introduced hypothesis.

tools/check-direct-r.sh is a smaller functional smoke check. Its first target
theories/Ranks.vo is in the working tree, not an isolated pristine baseline.
It does not replace the complete staged driver or the public theorem audits.

A green build proves only statements actually present, with their actual
premises. Original set-model soundness has explicit hierarchy, classical,
cardinal, and choice parameters; it does not establish internal BZC
derivability. The checked STLC reduction does not formalize the cited external
hardness theorem or machine-level complexity classes.

## Historical recovery packages

The modular development is already installed. Do not reapply the packages
in inputs over current sources. HANDOFF.md, LATEST_DECISIONS.md, and original
packages retain their original paths and historical limitations.

If recovery is ever necessary, extract packages to a separate temporary
directory, inspect their base and patches, and adapt without overwriting user
work. Do not apply both an aggregate patch and its constituent patches.
Do not run archived publish.sh or require gh.

## Browser CI and durable evidence

Use ordinary Git and the existing Actions workflow; no GitHub CLI is needed.
Actions uploads direct-r-logs-<run-id>-<attempt> on success or failure when
possible. Inspect the matching commit, versions.log, stages.tsv, result.txt,
per-stage logs, and raw Dune logs. An early failure leaves later stages
unchecked. No push or workflow dispatch is authorized merely by reading this
guide.

Update STATE.md and DECISIONS.md with actual milestones and exact next
commands. Keep dated raw verification logs unchanged, including their
historical source paths; add new evidence for the current layout instead.
