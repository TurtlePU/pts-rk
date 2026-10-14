# Uniform bounded carrier iteration — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Executed incremental commands, exits 1,1,1,0,0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-bounded-iteration-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-bounded-iteration-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-bounded-iteration-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-bounded-iteration-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-bounded-iteration-5.log 2>&1
```

Failures: instantiating intermediate closure variables; Bounded.conj
shadowing the logical constructor; overly implicit application of closure.
Fixed by explicit arguments. No theorem statement was weakened.

Eight new closed assumption reports, under explicit supplied-hierarchy
premises. The graph is defined by bounded separation. A native indexed
comparison relation remains in its correctness proof, so these reports
do not establish full Replacement elimination or a BZC interpretation.
Semantic conversion and the final soundness theorem remain unproved.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-iteration-fresh.vT4RJU --display=short --no-buffer ZFC_model/BoundedIteration.vo > /tmp/pts-rk-bounded-iteration-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-iteration-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-iteration-ci.log 2>&1
```

Fresh build, source comparison, recursive kernel check and full CI exited
0; 138 stages passed. Fresh dependency build printed 135 closed reports.
Kernel summary lists existing imported functional_extensionality_dep;
no unsafe settings. No timeouts. HEAD 33d05ab unchanged; work uncommitted.

```sh
cmp ZFC_model/BoundedIteration.v /tmp/pts-rk-bounded-iteration-fresh.vT4RJU/default/ZFC_model/BoundedIteration.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-iteration-fresh.vT4RJU/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-iteration-fresh.vT4RJU/default/theories PTSrk -Q /tmp/pts-rk-bounded-iteration-fresh.vT4RJU/default/ZFC_model PTSrkModel PTSrkModel.BoundedIteration > /tmp/pts-rk-bounded-iteration-kernel.log 2>&1
```
