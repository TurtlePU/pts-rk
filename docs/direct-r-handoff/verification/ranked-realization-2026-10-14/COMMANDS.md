# Ranked witnesses from realizations — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental builds exited 0,0. Added ranked_realization_witness,
lambda_realization_from_induction and application_realization_from_induction.
Product coherence now needs decoded component equality, not code equality.
Three new closed Print Assumptions reports. Later Check commands print the
new theorem types; the application module header was clarified afterward.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/LambdaRealization.vo > /tmp/pts-rk-ranked-realization-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-ranked-realization-2.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/ranked-realization-final" bash tools/check-local-ci.sh > /tmp/pts-rk-ranked-realization-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-ranked-realization-fresh.CqhSni --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-ranked-realization-fresh.log 2>&1
```

These rule lemmas still require type/body realizations and decoded
coherence. The joint fundamental proof and the first-order BZC foundation
audit are not finished. No theorem is replaced by a final-soundness premise.

Fresh build and final full CI exited 0. Fresh build printed 259 closed
reports including dependencies; all 131 final CI stages passed. Source
comparisons exited 0. The final CI rerun includes the clarified module
header. No failed builds or timeouts in this milestone.
Recursive kernel check exited 0. The library-wide summary lists imported
functional_extensionality_dep, no unsafe settings.

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/ranked-realization-final-v2" bash tools/check-local-ci.sh > /tmp/pts-rk-ranked-realization-ci-final.log 2>&1
cmp ZFC_model/ApplicationRealization.v /tmp/pts-rk-ranked-realization-fresh.CqhSni/default/ZFC_model/ApplicationRealization.v
cmp ZFC_model/LambdaRealization.v /tmp/pts-rk-ranked-realization-fresh.CqhSni/default/ZFC_model/LambdaRealization.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-ranked-realization-fresh.CqhSni/default/vendor/zfc ZFC -Q /tmp/pts-rk-ranked-realization-fresh.CqhSni/default/theories PTSrk -Q /tmp/pts-rk-ranked-realization-fresh.CqhSni/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-ranked-realization-kernel.log 2>&1
```
