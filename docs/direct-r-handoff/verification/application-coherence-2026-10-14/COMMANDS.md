# Application coherence constructor step — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental build exited 0. Eight closed reports in DenotationInversion,
including two new reports for typed_product_domain and
denotes_application_coherence.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-application-coherence-1.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/application-coherence-final" bash tools/check-local-ci.sh > /tmp/pts-rk-application-coherence-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-application-coherence-fresh.0wMEor --display=short --no-buffer ZFC_model/BetaWitnessTransport.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-application-coherence-fresh.log 2>&1
```

Original typing uniqueness proves syntactic conversion of the two product
witnesses. Original context transport aligns their fiber denotations.
Decoded domain/fiber conversion and function/argument subterm coherence
remain explicit local obligations; the theorem is not full soundness.

Fresh build and CI exited 0; fresh build printed 250 closed reports
including dependencies, and all 129 CI stages passed. Source comparison
exited 0. Source/documentation whitespace checks pass; raw retained logs
contain the compiler's original trailing whitespace and are not rewritten.
Recursive kernel check exited 0. Library-wide summary lists imported
functional_extensionality_dep, no unsafe settings. No failed compiler runs
or timeouts in this milestone.

```sh
cmp ZFC_model/DenotationInversion.v /tmp/pts-rk-application-coherence-fresh.0wMEor/default/ZFC_model/DenotationInversion.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-application-coherence-fresh.0wMEor/default/vendor/zfc ZFC -Q /tmp/pts-rk-application-coherence-fresh.0wMEor/default/theories PTSrk -Q /tmp/pts-rk-application-coherence-fresh.0wMEor/default/ZFC_model PTSrkModel PTSrkModel.BetaWitnessTransport PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-application-coherence-kernel.log 2>&1
```
