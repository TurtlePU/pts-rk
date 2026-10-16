# Arbitrary beta values via derived coherence — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo > /tmp/pts-rk-beta-coherence-1.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/beta-coherence-final" bash tools/check-local-ci.sh > /tmp/pts-rk-beta-coherence-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-beta-coherence-fresh.UgJSjv --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-beta-coherence-fresh.log 2>&1
```

Incremental build and full local CI exited 0; all 131 CI stages passed.
One new Print Assumptions report: realized_root_beta. Its Check output
retains all local realization/coherence/conversion premises. This theorem
does not discharge those premises or certify first-order BZC soundness.

Fresh build exited 0 and printed 261 closed reports including dependencies.
Both source comparisons and recursive kernel check exited 0. The library
summary lists imported functional_extensionality_dep and no unsafe settings.
No failed compiler runs or timeouts occurred in this milestone.

```sh
cmp ZFC_model/RootBeta.v /tmp/pts-rk-beta-coherence-fresh.UgJSjv/default/ZFC_model/RootBeta.v
cmp ZFC_model/DenotationInversion.v /tmp/pts-rk-beta-coherence-fresh.UgJSjv/default/ZFC_model/DenotationInversion.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-beta-coherence-fresh.UgJSjv/default/vendor/zfc ZFC -Q /tmp/pts-rk-beta-coherence-fresh.UgJSjv/default/theories PTSrk -Q /tmp/pts-rk-beta-coherence-fresh.UgJSjv/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-beta-coherence-kernel.log 2>&1
```
