# Actual global coding-witness selection — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental exits 1,0,0,0. Initial failure was a dependent Fin pattern;
fixed with an explicit pointwise environment equality. No statement weakened.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedCodeSelection.vo > /tmp/pts-rk-code-selection-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedCodeSelection.vo > /tmp/pts-rk-code-selection-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedCodeSelection.vo > /tmp/pts-rk-code-selection-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedCodeSelection.vo > /tmp/pts-rk-code-selection-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-code-selection-fresh.KpIQ2x --display=short --no-buffer ZFC_model/BoundedCodeSelection.vo > /tmp/pts-rk-code-selection-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/code-selection-final" bash tools/check-local-ci.sh > /tmp/pts-rk-code-selection-ci.log 2>&1
```

Nine closed reports. Choice and cardinal/hierarchy premises remain explicit.
The graph preserves the existing selector's values, and covers all rank-typed
products. This is not full model soundness or first-order BZC certification.

Fresh isolated build, source comparison, recursive kernel check and full
CI exited 0; all 140 stages passed. Fresh dependency build printed 219
closed reports. Kernel summary lists existing functional_extensionality_dep;
no unsafe settings. No timeouts. HEAD 33d05ab unchanged; work uncommitted.

```sh
cmp ZFC_model/BoundedCodeSelection.v /tmp/pts-rk-code-selection-fresh.KpIQ2x/default/ZFC_model/BoundedCodeSelection.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-code-selection-fresh.KpIQ2x/default/vendor/zfc ZFC -Q /tmp/pts-rk-code-selection-fresh.KpIQ2x/default/theories PTSrk -Q /tmp/pts-rk-code-selection-fresh.KpIQ2x/default/ZFC_model PTSrkModel PTSrkModel.BoundedCodeSelection > /tmp/pts-rk-code-selection-kernel.log 2>&1
```
