# Rank-independent choice — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental command ran five times, N=1–5, exits 1,1,1,0,0. Failures
required explicit hierarchy-base, Cartesian-factor and rank parameters;
statements were not weakened. Raw logs retained unchanged.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/GlobalCodeChoice.vo > /tmp/pts-rk-global-choice-N.log 2>&1
```

The following each exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-global-choice-fresh.STa6jv --display=short --no-buffer ZFC_model/GlobalCodeChoice.vo > /tmp/pts-rk-global-choice-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-global-choice-fresh.STa6jv/default/vendor/zfc ZFC -Q /tmp/pts-rk-global-choice-fresh.STa6jv/default/theories PTSrk -Q /tmp/pts-rk-global-choice-fresh.STa6jv/default/ZFC_model PTSrkModel PTSrkModel.GlobalCodeChoice > /tmp/pts-rk-global-choice-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/global-choice-final" bash tools/check-local-ci.sh > /tmp/pts-rk-global-choice-ci.log 2>&1
```

Six module reports closed; fresh build printed 187 closed reports including
dependencies. Kernel summary lists imported functional_extensionality_dep,
no unsafe settings. All 112 stages passed. The hierarchy and cardinal/choice
premises are explicit, not erased by the closed assumption reports. This is
not yet first-order BZC derivability or original PTS typing soundness.
