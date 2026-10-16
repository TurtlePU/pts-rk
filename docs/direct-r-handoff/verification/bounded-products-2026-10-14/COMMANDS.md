# Bounded dependent products — 2026-10-14

Working directory: /Users/akuklev/air/pts-rk.
HEAD: 5872c848ea9d92339107685f3fd9396010d72218; work uncommitted.

Environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental command run twice (both exit 0); output respectively in
/tmp/pts-rk-bounded-products-1.log and -2.log:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedProducts.vo
```

Fresh build (exit 0, 20 closed assumption reports including dependencies):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-products-fresh.U8TbAT --display=short --no-buffer ZFC_model/BoundedProducts.vo > /tmp/pts-rk-bounded-products-fresh.log 2>&1
```

Recursive kernel check (exit 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-products-fresh.U8TbAT/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-products-fresh.U8TbAT/default/theories PTSrk -Q /tmp/pts-rk-bounded-products-fresh.U8TbAT/default/ZFC_model PTSrkModel PTSrkModel.BoundedProducts > /tmp/pts-rk-bounded-products-kernel.log 2>&1
```

Library-wide summary lists imported functional_extensionality_dep; all four
new theorem-specific reports are closed. No type-in-type, unsafe fixpoints or
assumed positivity reported.

Full local CI, including pristine upstream (exit 0, all 96 stages):

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-products-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-products-ci.log 2>&1
```

Raw logs, stages.tsv and result.txt are retained alongside this file.
These checks prove the stated equivalence in Ens, not a completed BZC model
or original PTS typing soundness. Existence of model-specific family graphs
and coherent cardinal codes remains required.
