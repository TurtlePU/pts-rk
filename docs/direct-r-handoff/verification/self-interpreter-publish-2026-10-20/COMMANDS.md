# Scoped self-interpreter publication verification — 2026-10-20

Verified checkout: `/tmp/pts-rk-phoas-publish.x7qwoT/worktree`, branch
`publish/phoas-2026-10-20`. Proof snapshot commit
`3411f31f007caecfe5251dacb276583edbd4bba9` was merged with documentation commit
`6820469a75acf5a1adda248c193930a9b22daa6a`, yielding the actual two-parent merge
`64864e36b4d748cf117f830cdc4438d4d4054a2f`. The tracked checkout was clean when
verification started. The original dirty worktree and its unrelated changes
were not modified by this audit. No commit or push is performed by this report.

This source snapshot contains the 25 SelfInterpreter proof modules, its Dune
file and README, the research note/PDF, concise historical evidence and scoped
navigation/CI/handoff changes. The requested documentation branch contributes
its finished-development expositions. Unrelated unpublished BZC developments,
other paper tools and bulky historical raw logs are not included. The original
171-stage committed driver gains exactly one self-interpreter audit stage.

## Exact environment and retained raw evidence

Fresh raw evidence: `/tmp/pts-rk-self-publication.KX9EQK`.
Fresh absolute Dune directory: `/tmp/pts-rk-self-publication-build.GMOcrx`.
These directories are local evidence, not tracked source artifacts.
`CI.sh` and `AUDIT.sh` retain the literal launchers; `ci-driver.log` and
`audit-driver.log` retain traced commands, timestamps and failures. Individual
stage logs, exit codes, inventories and the staged driver's Dune logs are kept.

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1 and opam 2.6.1. The exact installed package inventory
is in `versions.log` and the complete staged-driver diagnostics.

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
bash /tmp/pts-rk-self-publication.KX9EQK/AUDIT.sh

export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/tmp/pts-rk-self-publication.KX9EQK/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash /tmp/pts-rk-self-publication.KX9EQK/CI.sh
```

## Fresh assumptions, kernel check and source identity

The audit ran 10:31:25--10:32:14 UTC and exited **0**. All eleven entries in
`status.tsv` have exit code 0. The fresh build printed **264 closed assumption
reports**, including the aggregate's 78 endpoint reports. Exact principal
commands, from the publication checkout:

```sh
timeout 1200 opam exec -- dune build --build-dir=/tmp/pts-rk-self-publication-build.GMOcrx --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o -Q /tmp/pts-rk-self-publication-build.GMOcrx/default/theories PTSrk PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o -Q /tmp/pts-rk-self-publication-build.GMOcrx/default/theories PTSrk -Q /tmp/pts-rk-self-publication-build.GMOcrx/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-self-publication-build.GMOcrx/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.Audit
diff -u /Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log /tmp/pts-rk-self-publication.KX9EQK/core-kernel.log
git diff --exit-code ffa7131 -- theories/ZFC_model
git diff --exit-code ffa7131 -- theories/AbstractRewriting.v theories/Congruence.v theories/Confluence.v theories/Context.v theories/DefEq.v theories/Inversions.v theories/Preservation.v theories/Ranks.v theories/Reduction.v theories/SN.v theories/Syntax.v theories/Typing.v
git diff --exit-code 73c4303 -- 'theories/NormalizationComplexity/*.v'
bash -n tools/ci-check-direct-r.sh tools/build-self-interpreter-note.sh
```

The recursive kernel inventory has only the existing upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
type-in-type, unsafe (co)fixpoints and assumed positivity inventories are empty.
The fresh core inventory is byte-identical to the retained pristine upstream
inventory for `723cf2ec61c737ae82ba33d2e7db44f650122b0e`. This comparison uses
that previously recorded pristine inventory; the full CI independently builds
pristine upstream again. Known physical/logical loadpath-remapping warnings
are retained and no proof check was disabled.

All 27 SelfInterpreter source/Dune/README SHA-256 values match the original
reviewed worktree snapshot and remain unchanged before/after verification.
The complete manifests are `source-sha256.txt`, `source-original-snapshot.log`
and `final-source-sha256.txt`; both exact `cmp` checks exit 0. Manifest SHA-256:
`86aac66c0d05400b3772f1e64455a0d108cbbd312e54fadbde8b9909a2d07b1e`.
The committed SelfInterpreter directory tree is
`4d07584b45ee12ccc530708107ede26b514f301b`.

## Complete scoped CI

The unchanged wrapper invokes actionlint and `tools/ci-check-direct-r.sh`,
including a fresh pristine upstream build. This clean publication has 172
stages, unlike the earlier 226-stage dirty-worktree audit that also compiled
unpublished unrelated developments. No committed stage was removed or weakened.

Result: **PASS**, exit code **0**, 10:31:23--10:40:39 UTC. All **172/172**
entries in `staged/stages.tsv` are `PASS` with exit code 0;
`staged/result.txt` reports `Last stage: complete`. There were no failed or
timed-out stages. This was a cold isolated build, not reuse of the original
development worktree's Dune cache. The separate fresh self-interpreter audit
above additionally supplies a complete fresh transitive-assumption replay.
Existing loadpath, notation-prefix and large-native-numeral warnings are
retained in the raw logs; no warning was hidden by changing the driver.
After full CI, `post-ci-source-sha256.txt` again matches the initial source
manifest by exact `cmp` (exit 0). `git diff --exit-code HEAD` on the complete
self-interpreter directory and note TeX/PDF also exits 0. Scoped handoff
`git diff --check`, the new report's trailing-whitespace check and both
launcher `bash -n` checks pass. Only this report and STATE/BUILD verification
updates were written by the reviewer in the publication checkout.

## Published note identity

Parent inspection of the actual published PDF confirms 18 pages. PDFKit
all-page text is retained as `pdf-text.txt` in the raw evidence directory;
the finite-PHOAS theorem/decoder on page 12 was rendered to `page12.png`
and visually checked. The current equations and index-boundary text render
correctly. This inspection is separate from the historical PDF build.

The publication snapshot contains the same TeX as the previous PHOAS checkpoint
but a different PDF. Its actual identities, captured before verification, are:

```text
2f9550a4c4c78e44754b2ab7544809b5b86b57a1b5433bc50ea98adc2f0df62e  PTS-rk_self_interpreter.tex
73c94e7dcc5e4113ebb828bf9a194c31d22a2d27d6a21dff0c5120878cb1f04e  PTS-rk_self_interpreter.pdf
```

The current PDF is **262401 bytes**. The historical checkpoint instead records
PDF SHA-256 `c517305ceb412d336af0db29876a41ef7b69dea5a8da83352d5c79ebb28c8a23`
and 259236 bytes. Its build/visual-check claims refer to that historical output;
this audit does not silently transfer them to a different file or claim a new
PDF build. The parent performs the current PDF inspection separately.

## Theorem and publication boundary

The checked strong PHOAS interpreter covers the independent Church-STLC
fragment, with external budget and full simple-type indices. Full dependent
context/type/term translation and substitution/conversion coherence remain
open; the shared-map obstruction does not rule them out. The full-PTS
semantic-payload construction remains weak and normalization-assisted.
No new generic elementary compiler, model reduction or external hardness
theorem follows from the successful checks above. These are local results,
not a remote CI result. After the fresh self audit passed and while full cold
CI was still running, the parent published the exact merge above. A read-only
`git ls-remote --heads origin main` after CI completion returned
`64864e36b4d748cf117f830cdc4438d4d4054a2f`; its output is retained as
`remote-main.log`. This reviewer did not commit, merge, stage or push. The
parent records the original-worktree/index-preservation operation separately.
