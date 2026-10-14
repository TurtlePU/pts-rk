# Selected codes and semantic congruence — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental runs in order: SelectedCodes 1 exit 0; ProductExtensionality 1
exit 1, 2 exit 0; SelectedCodes 2 exit 0. The failure was missing explicit
binders for constant-family extensionality, not a changed theorem statement.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SelectedCodes.vo > /tmp/pts-rk-selected-codes-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ProductExtensionality.vo > /tmp/pts-rk-product-extensionality-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ProductExtensionality.vo > /tmp/pts-rk-product-extensionality-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SelectedCodes.vo > /tmp/pts-rk-selected-codes-2.log 2>&1
```

Fresh build, kernel check and full CI each exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-selected-codes-fresh.cCOmjS --display=short --no-buffer ZFC_model/SelectedCodes.vo > /tmp/pts-rk-selected-codes-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-selected-codes-fresh.cCOmjS/default/vendor/zfc ZFC -Q /tmp/pts-rk-selected-codes-fresh.cCOmjS/default/theories PTSrk -Q /tmp/pts-rk-selected-codes-fresh.cCOmjS/default/ZFC_model PTSrkModel PTSrkModel.SelectedCodes > /tmp/pts-rk-selected-codes-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/selected-codes-final" bash tools/check-local-ci.sh > /tmp/pts-rk-selected-codes-ci.log 2>&1
```

Seven new reports closed; 181 reports in the fresh build with dependencies.
Kernel summary lists imported functional_extensionality_dep, no unsafe
settings. All 111 CI stages passed. Fixed-rank selection typing remains
conditional on the explicit cardinal/choice principles; beta and congruence
do not prove rank-independent selection or syntactic substitution/soundness.
