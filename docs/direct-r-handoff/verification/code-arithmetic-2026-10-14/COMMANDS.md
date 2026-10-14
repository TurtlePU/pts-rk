# Uniform code arithmetic and finite decoding — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Executed incremental commands (all exited 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedRecursion.vo > /tmp/pts-rk-bounded-recursion-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedCodeArithmetic.vo > /tmp/pts-rk-code-arithmetic-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedCodeArithmetic.vo > /tmp/pts-rk-code-arithmetic-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-code-arithmetic-fresh.sWVpNp --display=short --no-buffer ZFC_model/BoundedCodeArithmetic.vo > /tmp/pts-rk-code-arithmetic-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/code-arithmetic-final" bash tools/check-local-ci.sh > /tmp/pts-rk-code-arithmetic-ci.log 2>&1
```

Twelve new closed reports: five generic recursion and seven code arithmetic.
The finite decoder equation is uniform over all indices; no Choice premise.
It is not the full decoder or model soundness, and does not independently
establish first-order BZC derivability of the Ens framework.

Fresh isolated build, both source comparisons, recursive kernel check and
full CI exited 0; all 142 stages passed. Fresh dependency build printed
149 closed reports. Kernel summary lists existing functional_extensionality_dep;
no unsafe settings. No timeouts. HEAD 33d05ab unchanged; work uncommitted.

```sh
for model_file in BoundedRecursion.v BoundedCodeArithmetic.v; do cmp "ZFC_model/$model_file" "/tmp/pts-rk-code-arithmetic-fresh.sWVpNp/default/ZFC_model/$model_file" || exit; done
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-code-arithmetic-fresh.sWVpNp/default/vendor/zfc ZFC -Q /tmp/pts-rk-code-arithmetic-fresh.sWVpNp/default/theories PTSrk -Q /tmp/pts-rk-code-arithmetic-fresh.sWVpNp/default/ZFC_model PTSrkModel PTSrkModel.BoundedCodeArithmetic > /tmp/pts-rk-code-arithmetic-kernel.log 2>&1
```
