# Lambda coherence constructor step — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental build exited 0 with six closed reports (one new theorem).
Full local CI exited 0. Commands:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-lambda-coherence-1.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/lambda-coherence-final" bash tools/check-local-ci.sh > /tmp/pts-rk-lambda-coherence-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-lambda-coherence-fresh.pjo3jJ --display=short --no-buffer ZFC_model/BetaWitnessTransport.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-lambda-coherence-fresh.log 2>&1
```

The product-coherence premise was then restricted to actual domain
extensions. The second incremental build exited 0. The isolated build is
refreshed and CI rerun for this final version:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-lambda-coherence-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-lambda-coherence-fresh.pjo3jJ --display=short --no-buffer ZFC_model/BetaWitnessTransport.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-lambda-coherence-refresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/lambda-coherence-final-v2" bash tools/check-local-ci.sh > /tmp/pts-rk-lambda-coherence-ci-final.log 2>&1
```

The new theorem is a constructor coherence step. Its remaining semantic
premises are domain/body subterm coherence and decoded conversion of the
body-result types. Original typing uniqueness proves syntactic conversion
of those types. This is not a proof of full coherence, conversion, typing
soundness or first-order BZC foundations.

Fresh build, isolated refresh, final CI, source comparison and recursive
kernel check all exited 0. Fresh build printed 248 closed reports with
dependencies; refresh printed 13. Final CI passed all 129 stages. Kernel
library-wide summary lists imported functional_extensionality_dep, with
no unsafe settings. No failed builds or timeouts in this milestone.

```sh
cmp ZFC_model/DenotationInversion.v /tmp/pts-rk-lambda-coherence-fresh.pjo3jJ/default/ZFC_model/DenotationInversion.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-lambda-coherence-fresh.pjo3jJ/default/vendor/zfc ZFC -Q /tmp/pts-rk-lambda-coherence-fresh.pjo3jJ/default/theories PTSrk -Q /tmp/pts-rk-lambda-coherence-fresh.pjo3jJ/default/ZFC_model PTSrkModel PTSrkModel.BetaWitnessTransport PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-lambda-coherence-kernel.log 2>&1
```
