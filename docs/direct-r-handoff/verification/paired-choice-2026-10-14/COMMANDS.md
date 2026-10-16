# Joint type/body witnesses — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Both incremental builds exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/PairedChoice.vo > /tmp/pts-rk-paired-choice-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/LambdaRealization.vo > /tmp/pts-rk-paired-choice-2.log 2>&1
```

Each following verification command exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-paired-choice-fresh.BQ4ktk --display=short --no-buffer ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-paired-choice-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-paired-choice-fresh.BQ4ktk/default/vendor/zfc ZFC -Q /tmp/pts-rk-paired-choice-fresh.BQ4ktk/default/theories PTSrk -Q /tmp/pts-rk-paired-choice-fresh.BQ4ktk/default/ZFC_model PTSrkModel PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-paired-choice-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/paired-choice-final" bash tools/check-local-ci.sh > /tmp/pts-rk-paired-choice-ci.log 2>&1
```

All 124 CI stages passed. Fresh build printed 225 closed reports including
dependencies; library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. No timeouts.

Four new module assumption reports are closed. The lambda theorem type is
printed in run 2 and the fresh build. Its pointwise ranked body realization
premise is explicit; no theorem currently proves that premise for every
typing derivation. Application compatibility and conversion remain open,
as does the first-order BZC foundation audit of native denotation predicates.
This is joint witness assembly, not the final model-soundness theorem.
