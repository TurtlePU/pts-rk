# Dichotomy and all-product code theorem — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental commands exited 1,0,1,0 respectively. The first failure was an
uninferrable Prop placeholder; the third was finite decode parameter inference.
Raw logs retained; no statement weakened to resolve either failure.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CountableDichotomy.vo > /tmp/pts-rk-dichotomy-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CountableDichotomy.vo > /tmp/pts-rk-dichotomy-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CardinalClassification.vo > /tmp/pts-rk-dichotomy-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CardinalClassification.vo > /tmp/pts-rk-dichotomy-4.log 2>&1
```

Fresh build, kernel check and full CI each exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-dichotomy-fresh.uTsoeY --display=short --no-buffer ZFC_model/CardinalClassification.vo > /tmp/pts-rk-dichotomy-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-dichotomy-fresh.uTsoeY/default/vendor/zfc ZFC -Q /tmp/pts-rk-dichotomy-fresh.uTsoeY/default/theories PTSrk -Q /tmp/pts-rk-dichotomy-fresh.uTsoeY/default/ZFC_model PTSrkModel PTSrkModel.CardinalClassification > /tmp/pts-rk-dichotomy-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/dichotomy-final" bash tools/check-local-ci.sh > /tmp/pts-rk-dichotomy-ci.log 2>&1
```

Five dichotomy reports and two new classification reports are closed, with
138 closed reports in the fresh build including dependencies. Kernel summary
lists imported functional_extensionality_dep, no unsafe settings. All 107
CI stages passed. Family choice, comparability, the powerset-gap principle
and classical logic remain explicit premises of decoded_product_code; native
sequence construction is not yet a first-order BZC bounded-recursion proof.
