# Unconditional type-head normalization — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental build exits 0,1,0. Run 2 failed because the ambient context
length could not be inferred by equiv_𝓤_inversion; run 3 supplies the
original nat/n parameters explicitly. Five module Print Assumptions reports
are closed. No semantic hypotheses are used by these theorems.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/TypeHeadNormalization.vo > /tmp/pts-rk-type-head-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/TypeHeadNormalization.vo > /tmp/pts-rk-type-head-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/TypeHeadNormalization.vo > /tmp/pts-rk-type-head-3.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/type-head-final" bash tools/check-local-ci.sh > /tmp/pts-rk-type-head-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-type-head-fresh.J5UloR --display=short --no-buffer ZFC_model/TypeHeadNormalization.vo ZFC_model/BetaWitnessTransport.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-type-head-fresh.log 2>&1
```

Head classification is not full normality and is not denotation
preservation. Semantic conversion, ranked membership and the first-order
BZC foundation obligations remain open.

Initial full CI exited 0, but the isolated build above exited 1: the new
SortBounds import was missing from the model's declared theory dependencies.
The first kernel check also exited 1 because TypeHeadNormalization.vo did
not exist. The dune theory dependencies now explicitly include
PTSrk.NormalizationComplexity. Retry commands:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-type-head-fresh.J5UloR/default/vendor/zfc ZFC -Q /tmp/pts-rk-type-head-fresh.J5UloR/default/theories PTSrk -Q /tmp/pts-rk-type-head-fresh.J5UloR/default/ZFC_model PTSrkModel PTSrkModel.TypeHeadNormalization PTSrkModel.BetaWitnessTransport PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-type-head-kernel.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-type-head-fresh.J5UloR --display=short --no-buffer ZFC_model/TypeHeadNormalization.vo ZFC_model/BetaWitnessTransport.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-type-head-refresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/type-head-final-v2" bash tools/check-local-ci.sh > /tmp/pts-rk-type-head-ci-final.log 2>&1
```

Isolated retry, final CI and final recursive kernel check exited 0. The
retry printed 254 closed reports including rebuilt dependencies. All 130
final CI stages passed. Kernel library-wide summary lists imported
functional_extensionality_dep and no unsafe settings. No timeouts.
Source cmp exited 0; a separate attempt to cmp the dune manifest exited
2 because Dune does not copy that manifest into its build tree. The build
itself used the corrected dependency declaration.

```sh
cmp ZFC_model/TypeHeadNormalization.v /tmp/pts-rk-type-head-fresh.J5UloR/default/ZFC_model/TypeHeadNormalization.v
cmp ZFC_model/dune /tmp/pts-rk-type-head-fresh.J5UloR/default/ZFC_model/dune
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-type-head-fresh.J5UloR/default/vendor/zfc ZFC -Q /tmp/pts-rk-type-head-fresh.J5UloR/default/theories PTSrk -Q /tmp/pts-rk-type-head-fresh.J5UloR/default/ZFC_model PTSrkModel PTSrkModel.TypeHeadNormalization PTSrkModel.BetaWitnessTransport PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-type-head-kernel-final.log 2>&1
```
