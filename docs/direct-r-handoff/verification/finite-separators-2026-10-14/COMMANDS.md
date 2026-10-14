# Finite bounded separators — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Executed commands:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-finite-separators-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-finite-separators-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-finite-separators-fresh.m5EH5H --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-finite-separators-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/finite-separators-final" bash tools/check-local-ci.sh > /tmp/pts-rk-finite-separators-ci.log 2>&1
```

Incremental exits 1,0. Initial failure confused the pinned library's empty
type F with native False; fixed by elimination, without changing statements.
Two new closed reports, ten module reports total. Correctness no longer
uses carrier_relation; it uses finitely constructed bounded separators.
No set collecting all separators is defined. This is not yet a first-order
BZC derivation or final soundness, and the supplied-hierarchy premises remain.

Fresh isolated build, source comparison, recursive kernel validation and
full CI exited 0; all 138 stages passed. Fresh dependency build printed
137 closed reports. Kernel summary lists imported functional_extensionality_dep;
no unsafe settings. No timeouts. HEAD 33d05ab unchanged; work uncommitted.

```sh
cmp ZFC_model/BoundedIteration.v /tmp/pts-rk-finite-separators-fresh.m5EH5H/default/ZFC_model/BoundedIteration.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-finite-separators-fresh.m5EH5H/default/vendor/zfc ZFC -Q /tmp/pts-rk-finite-separators-fresh.m5EH5H/default/theories PTSrk -Q /tmp/pts-rk-finite-separators-fresh.m5EH5H/default/ZFC_model PTSrkModel PTSrkModel.BoundedIteration > /tmp/pts-rk-finite-separators-kernel.log 2>&1
```
