# Finite-embedding classification — 2026-10-14

Repository-root commands, each exit 0:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/FiniteClassification.vo > /tmp/pts-rk-finite-classification-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/FiniteClassification.vo > /tmp/pts-rk-finite-classification-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-finite-classification-fresh.OQMqUk --display=short --no-buffer ZFC_model/FiniteClassification.vo > /tmp/pts-rk-finite-classification-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-finite-classification-fresh.OQMqUk/default/vendor/zfc ZFC -Q /tmp/pts-rk-finite-classification-fresh.OQMqUk/default/ZFC_model PTSrkModel PTSrkModel.FiniteClassification > /tmp/pts-rk-finite-classification-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/finite-classification-final" bash tools/check-local-ci.sh > /tmp/pts-rk-finite-classification-ci.log 2>&1
```

Five module reports closed; 42 closed reports in fresh build with dependencies.
Recursive kernel summary: no axioms or unsafe settings. All 106 CI stages
passed. Excluded middle is explicit in subset/embedding classification.
No GCH or choice premise. This does not prove the finite/countable dichotomy
or first-order BZC derivability. Raw output retained unchanged.
