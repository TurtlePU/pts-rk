# Bounded comparison gluing and successor — 2026-10-14

All commands ran from the repository root with:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental builds 1 (graph/gluing) and 2 (successor) both exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedComparison.vo > /tmp/pts-rk-bounded-gluing-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedComparison.vo > /tmp/pts-rk-bounded-gluing-2.log 2>&1
```

Fresh build, recursive kernel check and full CI each exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-gluing-fresh.DyjH94 --display=short --no-buffer ZFC_model/BoundedComparison.vo > /tmp/pts-rk-bounded-gluing-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-gluing-fresh.DyjH94/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-gluing-fresh.DyjH94/default/theories PTSrk -Q /tmp/pts-rk-bounded-gluing-fresh.DyjH94/default/ZFC_model PTSrkModel PTSrkModel.BoundedComparison > /tmp/pts-rk-bounded-gluing-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-gluing-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-gluing-ci.log 2>&1
```

The module prints seven closed theorem reports, three new. Fresh compilation
prints 43 closed reports including dependencies. Library-wide kernel summary
lists imported functional_extensionality_dep, no unsafe settings. CI passed
104 stages. Excluded middle remains explicit in bounded_comparison_bijection;
closed assumptions are not a BZC derivability certificate.
