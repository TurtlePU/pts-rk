# Finite Church compilation — 22 October 2026

## Reproduce the checks

From the repository root:

```sh
bash docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/AUDIT.sh

AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh

bash theories/CombinatoryLogic-rk/build-note.sh

swift docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-church-finite-pdf-final.DKzMEm

shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/source-before.log
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/agda-sources.sha256
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/note-sources.sha256
bash -n theories/CombinatoryLogic-rk/build-note.sh \
  docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/AUDIT.sh
git diff --check -- theories/CombinatoryLogic-rk \
  docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md \
  docs/direct-r-handoff/BUILD.md
```

All final commands exit 0. For a fresh PDF inspection, create an output
directory with mktemp and replace the final argument. The proof/build scripts
allocate fresh directories themselves. No check was weakened.

## Verified results

- Native audit: exit 0, all 19 stages, 08:59:33–09:00:25 UTC.
  Logs _build/combinatory-church-finite-audit.0ceAEs; fresh Dune build
  /tmp/pts-rk-combinatory-church-finite.aVVCMj; independent pristine
  /tmp/pts-rk-combinatory-church-finite-pristine.Yk50Y4.
  24 modules, 241 own / 242 aggregate closed reports. The 17 ChurchFinite
  reports are closed. Recursive assumptions match pristine byte-for-byte:
  only unchanged upstream functional_extensionality_dep. Original kernel
  unchanged, formal sources stable, safety and whitespace pass.
  Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, Dune 3.23.1, OCaml 4.14.2.
- Agda: exit 0, 08:59:00–08:59:34 UTC,
  /tmp/pts-rk-combinatory-agda.4jl4SO. All 25 project modules and full import
  closure freshly checked with --safe and --ignore-interfaces; isolated
  configuration/data and stable copied sources. No warnings. Agda
  2.8.0-3d04bac; clean Cubical v0.9 b150186d2544e7efeddd31e5d14a8b9ecbb100f7.
- Note: exit 0, 09:03:29–09:03:43 UTC,
  /tmp/pts-rk-combinatory-note.2lG4Vk. LuaHBTeX 1.24.0 / TeX Live 2026,
  latexmk 4.88, latexminted 0.7.0, Pygments 2.19.2. Build and glyph/layout/
  reference/highlighting validation pass. One unchanged underfull MM0 footnote
  remains, not an overfull/glyph error.
- PDF: inspector exit 0, 21 pages, 3-page complete MM0 appendix, 23 Rocq and
  11 Agda proof badges, 21 total Agda links and 65 total links. Source targets,
  heading order, new program excerpt and references checked. All pages
  rendered; pages 13–16 and 18 visually checked. See PDF-REVIEW.md.
- No MM0/full-CI run in this checkpoint; MM0 was unchanged. No staging,
  commit or push. HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef;
  existing broad dirty and intent-to-add work preserved.

## Incremental commands and failures

ChurchFinite.v used the existing pinned native build during development:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq compile \
  -Q /tmp/pts-rk-combinatory-bckw.bnSrlP/default/theories PTSrk \
  -Q /tmp/pts-rk-combinatory-bckw.bnSrlP/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -o /tmp/pts-rk-church-finite.2Ap6qJ/ChurchFinite.vo \
  theories/CombinatoryLogic-rk/ChurchFinite.v
```

Logs /tmp/pts-rk-church-finite.2Ap6qJ/attempt-01.log through attempt-26.log.
Attempts 05/07/13/15/18/19/26 exit 0 with 4/7/8/9/10/13/17 closed reports.
All other attempts exit 1 with ordinary incomplete-proof, type matching or
arithmetic errors. Late failures 20–25 concerned scope-specialized normalb/
nodes inductions; explicit scoped IHs and arithmetic normalization fixed them.
Final direct check has only the existing module-name masking warning.
No generated native artifacts were written into the source directory.
The fresh audited build above supersedes these incremental checks.

FiniteMachine.agda checks used:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/FiniteMachine.agda
```

Both /tmp/pts-rk-finite-machine.LpQSkZ/attempt-{01,02}.log exit 0 without
warnings. The second includes application tables and their correctness.
ChurchFinite.agda's eight attempts, exact command, fixed diagnostics and
fresh standalone check are recorded in ChurchFinite-check.txt.

First note /tmp/pts-rk-combinatory-note.rYmbmc compiled but failed validation
(exit 1) on two overfull displays, 137.97pt and 21.15pt. Splitting the binary
map formula and naming the application source repaired them. Intermediate
.NNVuYl and .IKoScA build/validation exited 0; visual inspection of .IKoScA
found literal texttt commands in Markdown prose. Code spans repaired them;
the final inspector now explicitly rejects unprocessed texttt. No validator
was disabled. No timeout occurred.

The context-search skill requested jbcontext search for the unfamiliar
self_interpreter sources; jbcontext was absent (exit 127). Direct rg/source
inspection supplied the fallback. No semantic-search result is claimed.

## Proof boundary and next goals

FiniteMachine proves exact decoding of its finite transitions on inputs
satisfying a numerical source budget, without assuming successful normalization.
ChurchFinite.v proves arbitrary unary map/iteration typing and beta laws
in original PTS. ChurchFinite.agda constructs explicit original syntax and
proves selector typing/normality/size. Binary map regressions are examples,
not the missing all-index theorem. No checked cross-language correspondence
or arbitrary Agda/Cubical-to-PTS compiler is claimed.

1. Prove generic binary target typing/beta, then generator correspondence.
2. Finish Agda original subject reduction/rank descent to remove Maybe and
   return TypedResult at Y[y]. Existing code-to-code functions do not do this.
3. Construct graded fragment closure and embeddings; a fixed finite syntax
   carrier is not closed under application and is not automatically a model.
4. Supply internal finite-case principles, independent certificate soundness
   and the stated interpretation J for the Pakhomov-style consistency route.
   No self-consistency or Void-exclusion theorem is established here.

Keep the alphabet restriction a≤N, annotated source node count N, and
original redex-rank bound d. Encoding rank r is a separate parameter; at r=0
data/maps have ranks 1/2 but their syntax grows with carrier cardinality.
A canonical selector has 2K+3 nodes. No whole-runtime bound follows.
