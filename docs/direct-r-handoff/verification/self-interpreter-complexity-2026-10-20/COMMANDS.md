# Complexity route and full-PTS weak interpretation — 2026-10-20

Worktree verification at HEAD `73c4303dca2228bb6b3a8ec6ba5099a86da00bb0`.
No commit or push was requested in this continuation or performed. The
pre-existing large dirty worktree and unrelated documentation/BZC changes
are preserved; there is no staged content diff. New bulky logs stay in
ignored `_build`, following the current repository policy.

## Result and exact scope

- The introduction of `PTS-rk_self_interpreter.tex` now gives the positive
  fixed-budget elementary-normalization argument. Non-uniform elementary
  representability is a manuscript theorem, not an existing Rocq compiler.
  The numeric self-reducer proposition is explicitly conditional on that
  theorem and elementary serialization. No new axiom formalizes it.
- `RankedNormalization.v`: actual executable metalevel normalization followed
  by full raw HOAS quotation, automatic coverage of every closed original
  typed source, conversion-canonical codes, normalization-stage cost and
  separate output-size bounds. Canonical codes intentionally forget raw
  distinctions between beta-convertible sources.
- `LiteralObstruction.v`: raw quote at carrier rank r has maximum literal r;
  fixed heads cannot decode all normal U_k, even at redex bound and type rank
  zero. The statement does not exclude additional literal bounds or the
  conservative syntax bound, which already includes literals.
- `WeakFullInterpretation.v`: every CLOSED original t:A has an executable
  normal representation carrying nf(t), at nf(A), and the faithful raw HOAS
  tag of t. An actual closed indexed decoder of type rank max(s+3,r+6)
  projects nf(t) in five beta steps, with original result type A. The exact
  A:U_s witness comes from original validity. Conversion of representations
  retains literal annotated source-term equality via the tag.
- The last result is WEAK semantic-payload interpretation, NOT evaluation of
  pure HOAS/PHOAS syntax and NOT strong recovery of the unreduced source.
  External quotation performs normalization. The generic elementary compiler,
  typed adapters and dependent reifier remain open. Earlier strong STLC
  quotation and parameterized indexed PHOAS components remain intact.

Independent reviews and all intermediate compiler failures are in:
[representability audit](representability/COMMANDS.md),
[normalization attempts](normalization/COMMANDS.md),
[literal obstruction](literals/COMMANDS.md),
[weak interpretation](weak-full/COMMANDS.md), and
[final review/full CI](final-review/COMMANDS.md).
The context-search skill's requested `jbcontext search` bootstrap was
unavailable (exit 127); direct source searches supplied the audit instead.

## Fresh aggregate build and kernel checks

Raw runner, versions, source hashes, stdout/stderr and status TSV:
`/Users/akuklev/air/pts-rk/_build/self-interpreter-complexity-final.jKsix8`.
Command: `bash _build/self-interpreter-complexity-final.jKsix8/RUN.sh`, exit 0.
Fresh absolute Dune directory: `/tmp/pts-rk-self-complexity-final.sOJTwD`.
The driver performs the following with the pinned environment:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --build-dir=/tmp/pts-rk-self-complexity-final.sOJTwD --display=short --no-buffer @theories/self_interpreter/audit
opam exec -- rocq check -silent -o -Q /tmp/pts-rk-self-complexity-final.sOJTwD/default/theories PTSrk PTSrk.Ranks
opam exec -- rocq check -silent -o -Q /tmp/pts-rk-self-complexity-final.sOJTwD/default/theories PTSrk -Q /tmp/pts-rk-self-complexity-final.sOJTwD/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-self-complexity-final.sOJTwD/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.Audit
diff -u docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log _build/self-interpreter-complexity-final.jKsix8/core-kernel.log
git diff --exit-code ffa7131 -- theories/ZFC_model
git diff --exit-code ffa7131 -- theories/Syntax.v theories/Context.v theories/Typing.v theories/Inversions.v theories/Preservation.v theories/Ranks.v theories/Reduction.v theories/DefEq.v
bash -n tools/ci-check-direct-r.sh tools/build-self-interpreter-note.sh
```

Every command exits 0. Fresh assumption output has **179 closed reports**
(126 in self-interpreter proof modules, 52 aggregate endpoints, one core).
The recursive kernel inventory contains only existing upstream
`functional_extensionality_dep`; no unsafe fixpoints, assumed positivity or
type-in-type. The fresh core inventory matches the retained pristine
upstream baseline byte-for-byte (upstream commit
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`). Frozen ZFC and original kernel
comparisons are empty. Before/after SHA-256 inventories of all library
sources and Dune match (source-stability stage exit 0).

Observed versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. The complete package inventory is in versions.log.
Source safety scan for admissions, new axioms/parameters, disabled checks
and unchecked casts in the three added modules found no matches (rg exit 1).
Scoped `git diff --check` passes (exit 0). No fresh aggregate failure or
timeout occurred. Intermediate development failures remain in the module
reports above; they were fixed before this audit.

## Full local CI

The independent reviewer ran the unchanged `bash tools/check-local-ci.sh`
with a fresh `DIRECT_R_LOG_DIR`, after all Rocq/Dune sources were frozen.
**Exit 0: actionlint and all 226/226 stages pass**, including pristine upstream.
Exact launcher, settings, times and per-stage logs are recorded in
[final-review/COMMANDS.md](final-review/COMMANDS.md).
Raw directory: `_build/self-interpreter-complexity-ci.4sCyGR`.
This is local worktree verification, not a remote CI result or a fresh replay
of every cached print command; the separate build above supplies fresh prints.
The historical documentation-task ChurchSyntaxFold failure records an older
concurrent snapshot, not this verified source state.

## Note/PDF checks

Command: `bash tools/build-self-interpreter-note.sh`, twice, both exit 0.
First successful build: `/tmp/pts-rk-self-note.ZiL8Gc`; final build after
separating the concluding paragraph from the numbered list:
`/tmp/pts-rk-self-note.W7xAaD`. Both retain full versions/build/TeX logs.
Final PDF: 14 pages, 233069 bytes. No overfull boxes, missing glyphs or
unresolved references; three mild underfull boxes remain (badness
1314, 2111, 1629). PDFKit text was extracted for all pages. Introductory
equations, the conditional proposition, literal/normalization discussion,
weak interpretation theorem and final obligations were visually inspected.
The final list-separation fix was checked again on page 14. Generated PDF
text and representative PNGs remain in the ignored aggregate evidence dir.
No source document except the research note was rebuilt in this task.

## Frozen SHA-256

```text
8cba486895077ccbfa417cc4cdc22eb1a8cd7d26c447e3e88c4c3f3a9a9335e1  theories/self_interpreter/RankedNormalization.v
f391b5a5656d5f3428dffc497e931902355d10cfab3b65b185c112bdb3abb093  theories/self_interpreter/LiteralObstruction.v
ed2818269d20d89f7f8101fa6a756eaa2b3861c1840517e1cb0e92eb68a3244e  theories/self_interpreter/WeakFullInterpretation.v
c00f0f8a938d21acb5b6ec22f1a48f6e5b325eda5af24294fc6cc739c3ca4867  theories/self_interpreter/Audit.v
dcd49cb746b73e551682cf0ea19e8231f5e315e769c79468b769b82fbc9369b8  theories/self_interpreter/dune
473f24205cd5820fc6bbb03398ad56c883c635ce6372208d33594b5df1b4c553  PTS-rk_self_interpreter.tex
0b51c5d43a1a077cea9e4e92076f42f0afcad5a7dba041b8ae067d8f6b83b0b6  PTS-rk_self_interpreter.pdf
```

First remaining construction: a checked original-PTS compiler for explicit
elementary programs, starting with the all-rank numeral family and corrected
arithmetic basis, then fixed-budget numeric normalization. Typed HOAS adapters
and dependent reification are additional obligations, not consequences of
the runtime bound. Independent strong PHOAS closure/coherence remains open.

Next exact smoke command in the pinned environment:
`opam exec -- dune build @theories/self_interpreter/audit`.
Use a newly allocated absolute build directory if new assumption output is
required; the directory above is evidence, not a future fresh build.
