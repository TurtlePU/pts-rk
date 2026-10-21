# Internal dependent equality and structural binder congruence — final review

Verified on 21 October 2026 at base commit
`e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`, with all five new proof
modules, Dune and Audit frozen. No Git/index mutation or proof edit was
performed during this audit. Parent owns the note/PDF and handoff updates.

## Results

- Fresh absolute Dune aggregate: exit 0, **895** closed assumption reports.
  Audit contains 282 Check/Print pairs. The increase is 66 new module
  reports and 29 new aggregate reports over the previous 800.
- Recursive `rocq check -silent -o` of original `PTSrk.Ranks` and the
  complete self-interpreter Audit: both exit 0.
- Original core inventory is byte-identical to the retained pristine
  upstream inventory. The loaded aggregate lists only the pre-existing
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
  no type-in-type, unsafe fixpoints or assumed positivity.
- Complete `bash tools/check-local-ci.sh`: exit 0, actionlint successful,
  **226/226** staged checks PASS. The driver freshly builds pristine
  upstream `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Original kernel, NormalizationComplexity sources and frozen PR #1 ZFC
  sources match reference `ffa7131`; all comparisons exit 0.
- All 57 source/Dune manifest entries remained byte-identical across the
  fresh aggregate/kernel run. The five-module safety and whitespace scans
  found no matches; scoped Git whitespace and shell-syntax checks pass.
- No failed final-audit stage or timeout. Development failures remain in
  each module's own evidence; no stage or theorem was weakened to obtain green.

Aggregate timing: 02:29:50–02:32:55 UTC. Complete local CI timing:
02:29:51–02:30:58 UTC. Known logical-loadpath remapping and deprecated
arithmetic-notation warnings are retained in the raw logs.

## Exact runners and environment

Ignored local-only raw artifacts:
`_build/self-interpreter-coherence-final-review.qs3wIG/`.
Complete scripts: `AUDIT.sh`, `CI.sh`, `CHECK-SOURCES.sh`. Outputs include
`audit-driver.log`, `fresh-build.log`, `core-kernel.log`, `kernel.log`,
`status.tsv`, `ci-driver.log`, `staged/stages.tsv`, both source manifests,
versions and all comparison logs. These local raw paths are not promised
to exist in a clean checkout.

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-coherence-audit.mM2Zir \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-coherence-audit.mM2Zir/default/theories PTSrk \
  PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-coherence-audit.mM2Zir/default/theories PTSrk \
  -Q /tmp/pts-rk-self-coherence-audit.mM2Zir/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-self-coherence-audit.mM2Zir/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.Audit

export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-coherence-final-review.qs3wIG/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash tools/check-local-ci.sh
```

Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1. Full package inventory and CI switch export are
retained. The pristine comparison used
`docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log`.

## Independent contract review

All five modules passed read-only mathematical review. BinderCongruence,
written by this reviewer, separately passed TWO independent agent reviews
at its frozen hash; details are in `../binder-congruence/COMMANDS.md`.

- IndexedEqualityLevels derives lowering/reversal from the exact predicate
  level `max(a+2,d+1)`, using originally typed motives and seeds. It is not
  cumulativity or same-level symmetry. Type-law reversal at U_c uses input
  predicate c+2 and output c+1. Normality has explicit neutral-proof guards.
- DependentEquality has exact graph rank `max(a+2,b+2,d+1)` and predicate
  rank `max(a+1,b+1)`. Dependent congruence uses the SAME input level d and
  jointly relates indices and values, without claiming agreement with an
  independently prescribed transport. Fixed-fiber embedding, direct original
  typing and literal reflexivity computation are checked. Normality requires
  a non-lambda family and appropriate neutral function/proof inputs.
- BinderCongruence constructs an actual common map whose body may depend
  on both z:D and x:X, with X/C independent of z. Equality evidence is
  supplied OUTSIDE the x binder. Family substitution is exact and double-
  lifted, and product-code specialization uses the actual constructor p A.
  Reflexivity at the identity product computes the literal annotated Pi.
  No arbitrary pointwise-to-function lift or general normality is asserted.
- SourceSubstitution computes structural replacement/renaming of supplied
  FullSource data, preserving annotations and literal dependent result types.
  Variable evidence is Type-valued; its finite equivalence with original
  TypedSub is Prop-valued inhabitation, not proof extraction or Choice.
  Literal beta-contractum derivation is executable without a new wf domain
  restriction. Arbitrary-step Type-valued preservation and target equality
  generation are not claimed.
- TarskiGraphBeta feeds the ACTUAL finite beta field to fixed-fiber graph
  congruence. The explicit decoded-family reduction retypes the predicate
  application; there is no endpoint-typing extraction or subject expansion.
  Identity filling reduces to graph reflexivity while retaining the literal
  substituted decoded domain and lambda family. No eta, external normalizer,
  lambda-family normality or new coherence assumption is used.

The updated development README and research note also passed independent
review without corrections. The note's abstract, new rank formulas,
finite graph-beta connection, source-substitution account and closing
inventory match the frozen proofs. Its proposed dependent-telescope beta
generator is explicitly unformalized: formation, annotation normality,
contextual closure and sufficient length/rank-vector indices remain proof
obligations. Neither prose source claims prescribed-transport agreement,
general pointwise function equality or a full dependent quoter. Parent
separately records PDF compilation and visual verification.

## Frozen hashes

SHA-256 of the complete 57-entry source manifest:
`d904d67c0b152fb98a8a18ed42cfdd32336816ba35af3e5ab79740a5dce27b96`.

```text
726d67825f42a05a97ad200ba99af1f44030d26923ae8d27593add4e8da2bac0  IndexedEqualityLevels.v
144e1177c901bc2ce6d748d430aa574077ef08394e3c4a6cdaeb6c7dec05f875  BinderCongruence.v
f81d159880d8f447fffe514c55e77396dc13be4535d99e65586a4d31bc916ff9  DependentEquality.v
2198863c000673c55be4ff7c9c76cefbf9e9cd608bca10b51c67380ee11eafa7  SourceSubstitution.v
f67b71589ca645e6cd83d675395f86d7a8dd973344e6fa7114fb6fbbfc887d29  TarskiGraphBeta.v
7f39ec344fd05c045741e9504d469e3fbbf4159c06c20723fc8010c47c8d68e3  Audit.v
3d2f8cc8a1a9dca364c69ba42b5a5f136febca707950747b2706344a6214f565  dune
```
