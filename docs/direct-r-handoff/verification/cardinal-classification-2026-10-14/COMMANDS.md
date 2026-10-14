# Conditional infinite cardinal classification — 2026-10-14

Run from repository root with:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Each following command exited 0. The two incremental builds respectively
checked classification/uniqueness, then code and product specializations.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CardinalClassification.vo > /tmp/pts-rk-classification-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CardinalClassification.vo > /tmp/pts-rk-classification-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-classification-fresh.Aru0Wr --display=short --no-buffer ZFC_model/CardinalClassification.vo > /tmp/pts-rk-classification-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-classification-fresh.Aru0Wr/default/vendor/zfc ZFC -Q /tmp/pts-rk-classification-fresh.Aru0Wr/default/theories PTSrk -Q /tmp/pts-rk-classification-fresh.Aru0Wr/default/ZFC_model PTSrkModel PTSrkModel.CardinalClassification > /tmp/pts-rk-classification-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/classification-final" bash tools/check-local-ci.sh > /tmp/pts-rk-classification-ci.log 2>&1
```

Four new theorem reports are closed; 126 closed reports in the fresh build
including dependencies. Library-wide kernel audit lists imported
functional_extensionality_dep, no unsafe settings. All 105 CI stages passed.
Generic comparability, powerset gap and classical logic remain theorem
premises, not proved consequences of a formal BZC+GCH calculus. Product
classification additionally requires a countable injection. Full model
soundness and the finite case are not established by this checkpoint.
