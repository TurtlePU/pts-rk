# Finished-development documentation — 20 October 2026

Original shared-checkout snapshot:
HEAD `73c4303dca2228bb6b3a8ec6ba5099a86da00bb0`, before commit/push was requested.
Documentation/build support and disposable generated artifacts only: no
Rocq source, Dune theory or theorem statement changes. Existing dirty work,
including concurrent BZC/self-interpreter edits, is preserved.

## Subsequent publication preparation

The user requested commit and push, warning of concurrent self-interpreter
work. Publication uses branch `docs/finished-developments` in the isolated
checkout `/tmp/pts-rk-doc-publish.WocE1R/worktree`, based on remote main
`ffa7131be99bcbef3f1a787fce23126c3d310811`. The shared local main and index
are untouched. The separate unpushed self-interpreter note commit and all
ongoing proof changes are excluded. Shared navigation/handoff files contain
only this documentation task's selected additions.

Corrected publication references to use the committed frozen-model audits;
the ZFC exposition explains that the separate ongoing BZC work is outside
publication scope. Rebuilt with `bash tools/build-development-docs.sh` from
the isolated checkout: exit 0, logs in `/tmp/pts-rk-development-docs.2eouKv`,
38 pages across the same five documents. All compiler/validation statuses
are 0. All local links in the changed navigation files resolve; proof/Dune
and frozen-ZFC comparisons against the base are empty. Refreshed
DOCUMENTS.sha256 records these publication sources/PDFs, superseding the
original output hashes. The earlier proof audit still applies to unchanged
finished-development sources; no new complete CI run is claimed here.

The authorized publication is an ordinary commit and push to
`origin/docs/finished-developments`, with no force, merge or PR update.
Confirm the remote commit after pushing with
`git ls-remote --heads origin docs/finished-developments`.
All results below describe the earlier shared-checkout audit.

## Outputs and PDF verification

Five README.tex/README.pdf pairs are indexed by `docs/developments/README.md`:

| Development | Pages |
| --- | ---: |
| `theories/Interpretation_of_R` | 6 |
| `theories/Interpretation_of_R/relational` | 7 |
| `theories/Interpretation_of_R/functional` | 9 |
| `theories/NormalizationComplexity` | 9 |
| `docs/developments/ZFC_model` | 7 |

The 38-page collection covers infrastructure, theorem statements, approach,
crucial proof steps, discussion and verification boundaries. ZFC documentation
is external to preserve the whole reference directory at `ffa7131`.
Existing Markdown overviews remain and link the new documents.

Exact final command:

```sh
bash tools/build-development-docs.sh
```

Exit 0; fresh directory `/tmp/pts-rk-development-docs.yJpNLU`. All five
compiler and validation statuses are 0. The script requires LuaLaTeX,
latexmk and ripgrep, uses the local Markdown runtime/new minimal preamble,
and publishes PDFs only after all builds pass. Log-search errors fail too.
TeX Live 2026/LuaHBTeX and latexmk versions are retained in `pdf/versions.log`.
No original paper, Markdown runtime or existing preamble was changed.

All final PDF pages passed PDFKit text extraction, testing for empty pages
and unparsed `$$`, `\begin{`, `\end{`, `\operatorname`, `:::Theorem`
and `:::Proof`. Representative visual checks covered common pages 1/3/5,
relational 4/5/7, functional 1/5/9, normalization 1/4/7/8/9, and set-model
1/4/5/7. No clipping, broken math, overfull boxes, missing glyphs or
unresolved references remain. Mild underfull paragraphs are accepted.

Earlier attempts are retained:

- `/tmp/pts-rk-development-docs.bd8MoJ`: first collection exited 12 on
  figure-style theorem-caption syntax; fixed bracketed theorem titles.
- `/tmp/pts-rk-normalization-doc.9QdwCr`: initial lowercase theorem fences
  requested undefined theorem*; fixed capitalized fences. Final build-05.log
  exits 0; layout refinements retain the same theorem statements.
- `/tmp/pts-rk-doc-agent.GW9v6X` and `/tmp/pts-rk-doc-agent.u6AjZq`:
  isolated common/relational attempts fixed long spans/displays. Inspection
  found a silently unparsed math display caused by a trailing backslash;
  this was corrected before the final collection build.
- `/tmp/pts-rk-functional-doc.Rx6vcn` and `/tmp/pts-rk-zfc-doc.TUHvdU`:
  isolated builds identified long inline declarations; prose/layout fixes
  removed the overflows before final publication.

Final raw logs, numeric statuses and hashes are local under
`_build/development-docs-audit.Pyd9JH`; PDF logs are in its `pdf/` subtree.
`pdf-text-check.log` records all five page counts and the final text scan.
`DOCUMENTS.sha256` binds final sources, PDFs and new build dependencies.
New bulky temporary logs are deliberately not tracked; historical dated
raw evidence remains unchanged at its recorded paths.

## Fresh finished-development audit

Environment:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Versions: OCaml 4.14.2, Dune 3.23.1, Rocq core 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2, opam 2.6.1. No installation.

```sh
opam exec -- timeout 1800 dune build \
  --build-dir /tmp/pts-rk-finished-audit.WOMXfC \
  --display=short --no-buffer \
  @theories/Interpretation_of_R/relational/audit \
  @theories/Interpretation_of_R/functional/audit \
  @theories/NormalizationComplexity/audit \
  @theories/ZFC_model/audit
```

Exit 0, freshly allocated absolute directory, 1,127 closed assumption
reports (including dependencies and repeated public-audit queries).
Existing loadpath warnings remain visible. Parameterized model theorems
retain their explicit hierarchy, classical, cardinal and choice arguments.

Recursive kernel check, exit 0:

```sh
opam exec -- timeout 900 rocq check -silent -o \
  -Q /tmp/pts-rk-finished-audit.WOMXfC/default/theories PTSrk \
  -Q /tmp/pts-rk-finished-audit.WOMXfC/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-finished-audit.WOMXfC/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finished-audit.WOMXfC/default/theories/Interpretation_of_R/relational Interpretation_of_R.relational \
  -Q /tmp/pts-rk-finished-audit.WOMXfC/default/theories/Interpretation_of_R/functional Interpretation_of_R.functional \
  -Q /tmp/pts-rk-finished-audit.WOMXfC/default/theories/ZFC_model PTSrkModel \
  -Q /tmp/pts-rk-finished-audit.WOMXfC/default/vendor/zfc ZFC \
  PTSrk.NormalizationComplexity.Audit \
  Interpretation_of_R.relational.DirectRRelationalAudit \
  Interpretation_of_R.relational.DirectRUnaryAudit \
  Interpretation_of_R.functional.DirectRFunctionalAudit \
  PTSrkModel.ModelSoundness PTSrkModel.MaterialZermelo
```

Only upstream functional_extensionality_dep occurs in the loaded global
context; no type-in-type, unsafe fixpoints or assumed positivity.
Separate core check, exit 0:

```sh
opam exec -- timeout 180 rocq check -silent -o \
  -Q /tmp/pts-rk-finished-audit.WOMXfC/default/theories PTSrk PTSrk.Ranks
```

Its output is byte-identical (`diff -u`, exit 0) to the retained pristine
inventory in `verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log`.
No build/kernel timeout occurred. Logs: fresh-build.log, kernel.log,
core-kernel.log, core-comparison.log and numeric *-exit.txt in the local
evidence directory above.

## Full CI snapshot: independent concurrent failure

```sh
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/development-docs-audit.Pyd9JH/full-ci \
  bash tools/check-local-ci.sh
```

Exit 1. actionlint, 01-upstream and 01-normalization-complexity pass.
01-self-interpreter fails in ChurchSyntaxFold.v, line 72, characters 54–64:
`Tactic failure: congruence failed.` Later CI stages were not run.
That excluded directory was under concurrent development, with new
BrownPalsberg/TypedHOAS work. This describes the observed snapshot, not
later changes. No excluded proof was edited and no CI stage was weakened.
The independent fresh finished-library audit passed. No complete local
or remote CI success is claimed. Logs: full-ci-driver.log and full-ci/.

## Cleanup, consistency and continuity

Moved 17 disposable files into ignored `_build/obsolete-generated.713zwP`:
14 Python .pyc files from Markdown tests/prose tools, root .lia.cache and
the two generated latex/PTS-rk.markdown.* body/preamble sidecars. The
Markdown class regenerates these from the real source; their checkout
copies had no build/source consumers. The 15 cache files had intent-to-add
index entries only; removing those leaves no staged diff. An initial
git rm --cached refused directory targets without -r; the subsequent
explicit git rm -r --cached succeeded. No committed source/test was deleted.
Ignore rules prevent these artifact classes returning to the change list.

All tests, local builds, dated proof-verification logs, provenance archives,
vendored libraries and unrelated user work remain. Scoped git diff --check,
Markdown local-link checks and bash -n tools/build-development-docs.sh pass.
git diff --exit-code ffa7131 -- theories/ZFC_model exits 0; all finished
tracked Rocq sources and Dune files are also unchanged against HEAD.
An initial continuity patch was rejected when concurrent self-interpreter
work prepended a new entry; reread the file and inserted only this new
entry, preserving the concurrent material. No partial patch was applied.

Documentation and cleanup are complete; no theorem changes status.
Next exact documentation command: bash tools/build-development-docs.sh.
The first unrelated CI issue to recheck is the concurrent self-interpreter
stage. Material BZC soundness and dependent unquotation remain outside scope.
