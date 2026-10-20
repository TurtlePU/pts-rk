# Finite indexed PHOAS and dependent boundary — 2026-10-20

Worktree verification at HEAD `73c4303dca2228bb6b3a8ec6ba5099a86da00bb0`.
No commit or push requested or performed in this continuation; no staged
content diff. Preserve the pre-existing large dirty worktree and unrelated
BZC/documentation changes. New bulky raw logs remain ignored under `_build`.

## Actual result and limits

- `PHOASTelescope`: generic finite original-context closure, normality,
  injectivity, code-type formation, actual sequential application and direct
  application typing from original `TypedSub`.
- `PHOASAlgebra` / `PHOASFaithful`: polymorphic rank-pair handler specialization,
  original quotation typing, normality and literal annotated-source fidelity
  under target beta comparison. The eraser handles explicit pretype arguments.
- `PHOASRecovery`: strong recovery after actual replacement, with family and
  handler laws needed only inside the computed finite source budget.
- `PHOASPackage`: a finite well-formed, normal context with
  `1+(k+2)+2*(k+1)^2` binders; actual closed code and code type; normality,
  syntax injectivity, original typing, and a constructed typed substitution
  supplying every identity family and handler. Coverage starts from the
  independent Church-STLC source relation, not target quotation properties.
- `PHOASDecoder.closed_phoas_interpretation`: an actual closed decoder whose
  application to the closed normal quote reduces to the original, unreduced
  `lambda o:U_0.t`. Its external indices are **k and the full simple type A**,
  not rank alone. At fixed `(k,A)` it is the same program for every source
  derivation within budget. No normal form or semantic value is stored in the
  quote. A computed budget-one example has a reducible source, normal quote,
  and strong recovery. Package/decoder universe existence is checked; no exact
  new numerical sort formula is claimed.
- `DependentPHOAS`: genuinely dependent local product and Abs/App types,
  actual typed identity handlers and beta equations, direct original result
  typing of the applied dependent App handler, and a candidate universe
  decoder under the stated literal-sort convention. Its dependent family on
  `F_a(A)` is supplied, not recursively translated from every source family.
- `PHOASConversion`: normal syntax injectivity cannot coexist with conversion
  preservation in one map, nor with pointwise beta agreement to a separate
  conversion-preserving index map. The witnesses fit fixed small independent
  bounds. This limited result does **not** rule out genuinely distinct syntax
  and semantic indices, or arbitrary dependent indexed PHOAS.

Thus finite strong PHOAS unquotation is completed for independent Church-STLC,
not full dependent PTS-rk. The recursive dependent type/family translation and
substitution/conversion coherence remain open. No target theorem, parametricity,
no-junk property or generic elementary compiler is assumed as an axiom.

Intermediate failures and exact module runs are retained in:
[telescope/recovery](telescope-recovery/COMMANDS.md),
[finite algebra/package](package/COMMANDS.md),
[faithfulness](faithful/COMMANDS.md), [closed decoder](decoder/COMMANDS.md),
[dependent handlers](dependent/COMMANDS.md),
[conversion obstruction](conversion/COMMANDS.md), and
[independent review/full CI](final-review/COMMANDS.md).
These reports include failed attempts rather than presenting only green logs.

## Fresh aggregate and recursive kernel check

Command: `bash _build/self-interpreter-phoas-final.AM5spg/RUN.sh`, exit **0**.
Raw driver, exact commands, version inventory, hashes and all stdout/stderr:
`_build/self-interpreter-phoas-final.AM5spg`.
Fresh absolute Dune directory: `/tmp/pts-rk-self-phoas-final.t8AzBr`.

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --build-dir=/tmp/pts-rk-self-phoas-final.t8AzBr --display=short --no-buffer @theories/self_interpreter/audit
opam exec -- rocq check -silent -o -Q /tmp/pts-rk-self-phoas-final.t8AzBr/default/theories PTSrk PTSrk.Ranks
opam exec -- rocq check -silent -o -Q /tmp/pts-rk-self-phoas-final.t8AzBr/default/theories PTSrk -Q /tmp/pts-rk-self-phoas-final.t8AzBr/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-self-phoas-final.t8AzBr/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.Audit
diff -u docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log _build/self-interpreter-phoas-final.AM5spg/core-kernel.log
git diff --exit-code ffa7131 -- theories/ZFC_model
git diff --exit-code ffa7131 -- theories/Syntax.v theories/Context.v theories/Typing.v theories/Inversions.v theories/Preservation.v theories/Ranks.v theories/Reduction.v theories/DefEq.v
bash -n tools/ci-check-direct-r.sh tools/build-self-interpreter-note.sh
```

All commands exit 0. Fresh output has **264 closed assumption reports**:
185 self-interpreter module reports, 78 aggregate endpoints, one core report.
The recursive kernel inventory contains only the existing upstream
`functional_extensionality_dep`; type-in-type, unsafe (co)fixpoints and assumed
positivity inventories are empty. The fresh core inventory is byte-identical
to the retained pristine upstream baseline at commit
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`. Frozen ZFC and original kernel
source comparisons are empty. Before/after SHA-256 inventories for every
self-interpreter Rocq source and Dune match; source-stability stage exits 0.

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. The full switch inventory is in `versions.log`.
No fresh aggregate failure or timeout. Known physical/logical loadpath
remapping warnings are harmless; no proof checks were disabled.

## Full CI and source review

Independent read-only contract review passes; no source fix requested.
The unchanged `bash tools/check-local-ci.sh` exits **0**: actionlint and all
**226/226** stages pass, including a fresh pristine upstream build. Raw logs:
`_build/self-interpreter-phoas-ci.v3H6S5`; exact launcher, timestamps and
settings in [final-review/COMMANDS.md](final-review/COMMANDS.md).
Frozen source hashes remained unchanged across the run. No stage weakened.
This is local worktree verification, not remote CI. Ordinary staged CI can
reuse caches; the separate fresh aggregate above supplies fresh assumptions.

Scoped whitespace and shell checks pass. A safety scan of the eight new
modules finds no admissions, new axioms/parameters, unchecked casts or disabled
guard/universe/positivity checks. No edits to original PTS rules or frozen ZFC.
Final `git diff --check` on the note, READMEs, self-interpreter and handoff
paths exits 0; `git diff --cached --exit-code` also exits 0. Separate
`rg -n '[ \t]+$'` checks on the eight untracked proof sources and new evidence
directory exit 1 (no matches). The source-safety `rg` scan likewise exits 1
(no matches). A final `shasum -a 256` rerun matches every proof/Audit/Dune hash
below, after documentation changes. These scans supplement, not replace, the
fresh kernel check.

## Note and PDF

Command: `bash tools/build-self-interpreter-note.sh`, exit **0**.
Build/log directory: `/tmp/pts-rk-self-note.545XF9` (two TeX passes).
Final PDF: **18 pages, 259236 bytes**. No overfull boxes, missing glyphs,
undefined references or final rerun warning. Three mild underfull boxes
remain (badness 1314, 2111, 1629), already present in earlier prose.
All-page text extracted with PDFKit into `pdf-text.txt` in the aggregate
raw directory. New package/decoder, dependent-handler, obstruction and
closing pages 11, 12, 13, 14, 18 rendered and visually inspected there.
No clipping, broken math fences or missing mathematical symbols observed.
The reviewed exposition states the full-A decoder index and the exact
dependent boundary; it does not overstate the shared-map no-go theorem.

## Frozen SHA-256

```text
13ea13586b288fd8a96a29285a1f1dc160892682506624b51d4c3e9da881387b  theories/self_interpreter/DependentPHOAS.v
0e433a5d40c5b79241704848f55784c5e0a8e8ea1c37e4098e1f426af7efc848  theories/self_interpreter/PHOASTelescope.v
29c3452e4817e387b4f2e82ef50309e4720fb7068d9382cbcb589bc7f787e8c6  theories/self_interpreter/PHOASConversion.v
d5180f6efa44c2a03bafd7712c161a4a2b0045b7ce0fb4e4a94ce6671cc2cb2e  theories/self_interpreter/PHOASAlgebra.v
be380cd2859e255f4202f71316ca5ab5d9cf50ef6a8aaac4b47bac9467ffe073  theories/self_interpreter/PHOASFaithful.v
f921cc8efb66106db5519901b2e5e367db413526d59d29c29e3ba53efd2952e8  theories/self_interpreter/PHOASRecovery.v
8dff8574ecb500e058dcfcfc3159fad559da5fa066febd4a8d898f52a637febf  theories/self_interpreter/PHOASPackage.v
f52518d4b040126a1c02c998404727be789fd350cfe02bf6bc11b6f3580e1576  theories/self_interpreter/PHOASDecoder.v
9ccda979394b526785fd037692c6bb6321cdc8253d608ba0ad069867d58ff194  theories/self_interpreter/Audit.v
bd2f7a682afd406a391bcd6d4c35055aee720aa56d7b01e84bbbb39a70c511cd  theories/self_interpreter/dune
2f9550a4c4c78e44754b2ab7544809b5b86b57a1b5433bc50ea98adc2f0df62e  PTS-rk_self_interpreter.tex
c517305ceb412d336af0db29876a41ef7b69dea5a8da83352d5c79ebb28c8a23  PTS-rk_self_interpreter.pdf
```

First remaining PHOAS construction: dependent context/type/term translation
with genuinely separate syntax and semantic indices, proving substitution
and conversion coherence inside original PTS. Separately internalize the
current full-A decoder index. The elementary compiler route remains open
independently; the existing full-PTS semantic-payload decoder is still weak.

Next exact smoke command in the pinned environment:
`opam exec -- dune build @theories/self_interpreter/audit`.
Allocate a NEW absolute build directory for new assumption output; the
directory above is retained evidence, not a future fresh build.
