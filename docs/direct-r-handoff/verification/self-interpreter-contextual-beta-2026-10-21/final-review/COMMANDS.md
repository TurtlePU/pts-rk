# Uniform contextual cast-beta — final independent audit

Base commit `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`, 21 October 2026.
All eleven new modules, Dune and Audit were frozen before this audit.
No proof/Git/index mutation is performed during verification. Parent owns
the note/PDF and live handoff updates.

## Verification status

Fresh aggregate and complete local CI launched in parallel at 03:30 UTC.
The fresh absolute build passed with exactly 1140 closed assumption
reports: preceding 895 + 187 new module reports + 58 aggregate reports.
Audit contains 340 Check/Print pairs. The frozen manifest contains 68
entries: 67 proof files including Audit, plus Dune.

Complete local CI passed, exit 0, **226/226** stages PASS, including fresh
pristine upstream and actionlint. Timing: 03:30:56–03:33:13 UTC.
Both original-core and aggregate recursive `rocq check -silent -o` checks
passed, exit 0. The original core inventory is byte-identical to retained
pristine upstream. Loaded aggregate inventory lists only unchanged upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
no type-in-type, unsafe fixpoints or assumed positivity.
Frozen PR #1 ZFC, original kernel and NormalizationComplexity sources match
reference ffa7131. All 68 source/Dune entries remained byte-identical across
the fresh build and kernel audit. Every comparison exited 0.
New-module safety/whitespace scans, scoped Git whitespace and runner shell
syntax checks passed. No failed final-audit stage or timeout.
Fresh aggregate/audit timing: 03:30:55–03:37:31 UTC. Known logical-loadpath
remapping and deprecated arithmetic-notation warnings remain in raw logs.

## Exact runners and environment

Ignored local-only raw artifacts:
`_build/self-interpreter-contextual-beta-final-review.nNuNVo/`.
Complete scripts: AUDIT.sh, CI.sh, CHECK-SOURCES.sh. Outputs include
audit-driver.log, fresh-build.log, core-kernel.log, kernel.log, status.tsv,
ci-driver.log, staged/stages.tsv, both source manifests, versions and all
comparison logs. These local raw paths are not promised in a clean checkout.

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-contextual-beta-audit.tzMxfv \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-contextual-beta-audit.tzMxfv/default/theories PTSrk \
  PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-contextual-beta-audit.tzMxfv/default/theories PTSrk \
  -Q /tmp/pts-rk-self-contextual-beta-audit.tzMxfv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-self-contextual-beta-audit.tzMxfv/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.Audit

export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-contextual-beta-final-review.nNuNVo/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash tools/check-local-ci.sh
```

Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1. Full installed package inventory is retained.
The pristine core inventory reference is
`docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log`.
The full staged driver independently builds pristine upstream commit
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

## Independent mathematical review

All eleven module contracts passed read-only review. The three modules
written by this reviewer received separate independent agent reviews:
RealizedSignature, ContextualBetaSignature and TelescopeBetaSignature.
Their scoped evidence records exact frozen hashes and build failures.

- ContextualTelescope stores literal original dependent annotations and
  independent formation evidence over arbitrary original contexts. Closure
  typing, exact rank, normality, original TypedSub lifting and structural
  renaming/substitution retain all binders. No length bound follows from rank.
- ContextualBeta constructs the specific cast-Abs/App beta equation under
  an arbitrary supplied telescope. Both complete endpoints are originally
  typed, and the independent identity witness computes to literal reflexivity.
  Normality has explicit annotation and neutral-input guards. No arbitrary
  pointwise equality is lifted to function equality.
- ContextualBudgets gives executable exact/length-bounded rank-vector
  enumeration, exact cardinality and computed coverage, including arbitrarily
  long rank-one vectors. Descriptors contain no domain syntax.
- UniformTelescope actually binds each domain family over the preceding
  dependent domains. Its rank-vector-only generator yields normal neutral
  domain spines and independently formed parameter/domain telescopes.
- UniformTelescopeRecovery computes parameter values by lambda-closing the
  supplied literal declarations. Original typed substitution and annotation-
  wise recovery are derived from independent telescope formation. Transparent
  scope transports do not alter original constructors. The final exposed
  closure recovery ends in U_s; arbitrary-body scope transport and application
  of every uniform beta witness to every concrete telescope remain separate.
- TelescopeBetaFamily binds A,B,f,u as actual dependent functions over the
  supplied telescope, and compares complete annotated lambda closures.
  Its rank is max(ceiling(rs)+2,a+2,b+2,d+1). Independent plain identity typing
  is converted only at its type by proved forward reductions; four actual
  beta applications yield literal reflexivity. Normality requires normal
  telescope annotations, not an assumed normalization operation.
- UniformContextualBeta closes that family over the generated domain
  parameters. Thus only rs,a,b,d are external indices. It has original
  formation, normal syntax, substitution naturality and an independently
  typed normal identity implementation. The numerical k+3 rank bound is
  neither cumulativity nor a claimed complete translated-source budget.
- ContextualBetaFamily provides the separate five-argument one-binder
  instance X,A,B,f,u, with normal closed identity implementation and literal
  recovery. ContextualBetaSignature appends exactly (k+1)^4 such fields to
  the existing local-beta signature. Direct application typing and normality,
  original typed filling, and fixed-index input/conversion injectivity are
  local contracts, not full-source quotation fidelity.
- RealizedSignature registers any finite independently sorted base-only
  family list with actual closed base/field realizers. Its hypotheses do not
  assert source quotation or assume the existence of the desired interpreter.
- TelescopeBetaSignature appends count(L,k)*(k+1)^3 actual uniform fields
  to the existing local-beta signature. Executable lookup and computed
  descriptor budgets give actual typed fields. Context normality, wf,
  inherited environment, identity TypedSub, literal fill equations and
  closed package/run contracts are derived, not new field-existence premises.
  The inherited carrier range through S k covers max(a+1,b).

This checkpoint does not provide mutually compatible translated contexts,
families, types and terms for all original derivations, nor global
quotation/substitution coherence, full normal quotation, source fidelity
and strong literal recovery. It uses no eta, function-extensionality axiom,
neutral-cast cancellation, extra calculus rule or external normalizer.

The new note section, abstract, inventory/remaining programme and development
README passed independent read-only prose review. Exact ranks, finite counts,
rank-versus-length separation, normal-domain guards and the U_s-only exposed
closure-recovery boundary match the frozen contracts. Neither prose source
claims full dependent quotation or arbitrary pointwise function equality.
Parent separately records PDF compilation and visual inspection.

## Development disk failure and preserved evidence

TelescopeBetaSignature attempt02 failed with `No space left on device`
during dependency scanning/building. Its full log remains at
`_build/telescope-beta-signature.pWomgH/attempt-02.log`. Parent removed ONLY
the following validated OLD generated Dune caches, preserving historical
raw logs and tracked evidence:

- `/tmp/pts-rk-self-coherence-audit.mM2Zir`
- `/tmp/pts-rk-self-conversion-audit.SRZ7pU`
- `/tmp/pts-rk-self-binder-congruence.tkK21j`

The initial recursive-force request was tool-policy rejected and performed
no deletion; subsequent ordinary recursive removals succeeded. Those old
cache paths are now historical, not retained build artifacts. Current-phase
directories were preserved. This resource cleanup changed no source, CI
stage, theorem statement or proof-integrity check. All other development
failures/timeouts are recorded in each module's scoped evidence.

## Frozen hashes

SHA-256 of complete 68-entry manifest:
`fd9f2e2d3da9c111d3ffcd073efd6ad428ccf7391a875e87ad397c118b8d216d`.

```text
1d3e86333e00942a12264d1507bf041e67a23d952b5b3b7d56a4a8faa1021eaa  ContextualTelescope.v
9e16dea560b32d237179fdf6b2821477a353f621e4c0d64bee865932466436b0  ContextualBeta.v
1d59d4699feccd7ef74ca8ed0e6ca04989e5d7ef9ca081f6a19e4bde6aebf658  ContextualBudgets.v
bc22e3ce60f501a8ab5021895ab0ca4dff292fd300c5c5135ce039c78a57de8b  UniformTelescope.v
9bff20445692168310b6dfa17a714f099b4bf0bbf76e3952ab84b9d342f883e6  UniformTelescopeRecovery.v
bca1c48e337cfb84fa7084239f23793dcc41653d8d31a1e142568695ecd54be8  RealizedSignature.v
4c94735ff6a52f15ae0c866a9efe3a7edbf7ad4b8889500d136af38c00d6a620  TelescopeBetaFamily.v
7f064a58f61e6e59a4f67de23ad1ec4fddf04cec58af7d6e07cdab2984a605a2  UniformContextualBeta.v
b7d4dba52efb7bc0400a0783c603849fd43bccd5cf4031cbb9dc1d7cb2fa39cb  ContextualBetaFamily.v
733d2d0ed64e38084d0422ea17cf644c28543eb8547ebd43e3655f83735790ec  ContextualBetaSignature.v
24fb7ee970bc609f54a43cb7fa84e4a7f75bcbb7ac87381fd3fd79b8448c56a3  TelescopeBetaSignature.v
6b35277fd99028cecccb89924efdd757a0bfa8037f0506b692bae5813c712ca6  Audit.v
72a6eadd9686d90f3c56e31786376ac1141661f76dea023c42a370bba1822f22  dune
```
