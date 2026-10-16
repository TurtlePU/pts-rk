# Bounded formula-defined selection — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Executed incremental commands (both exited 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFormulaSelection.vo > /tmp/pts-rk-formula-selection-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFormulaSelection.vo > /tmp/pts-rk-formula-selection-2.log 2>&1
```

Six closed reports. Selection requires the explicit ordinary family_choice
premise; no axiom is declared. Predicate inputs must be bounded Formula,
not arbitrary Rocq Prop. The selected graph uses bounded_formula_graph,
not native graph. This is not the full model's soundness theorem.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-formula-selection-fresh.45HeSc --display=short --no-buffer ZFC_model/BoundedFormulaSelection.vo > /tmp/pts-rk-formula-selection-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/formula-selection-final" bash tools/check-local-ci.sh > /tmp/pts-rk-formula-selection-ci.log 2>&1
```

Fresh isolated build, source comparison, recursive kernel check and full
CI exited 0; all 139 stages passed. Fresh dependency build printed 84 closed
reports. Kernel summary lists existing functional_extensionality_dep;
no unsafe settings. No timeouts. HEAD 33d05ab unchanged; work uncommitted.

```sh
cmp ZFC_model/BoundedFormulaSelection.v /tmp/pts-rk-formula-selection-fresh.45HeSc/default/ZFC_model/BoundedFormulaSelection.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-formula-selection-fresh.45HeSc/default/vendor/zfc ZFC -Q /tmp/pts-rk-formula-selection-fresh.45HeSc/default/theories PTSrk -Q /tmp/pts-rk-formula-selection-fresh.45HeSc/default/ZFC_model PTSrkModel PTSrkModel.BoundedFormulaSelection > /tmp/pts-rk-formula-selection-kernel.log 2>&1
```
