# Concrete code hierarchy bounds — 2026-10-14

Working directory: /Users/akuklev/air/pts-rk. HEAD remains
5872c848ea9d92339107685f3fd9396010d72218; changes uncommitted.

Environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental builds (exits 1,1,1,0; raw logs retained):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CodeHierarchyBounds.vo
```

Fresh build (exit 0; 88 closed reports including dependencies):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-code-hierarchy-fresh.Cehkq2 --display=short --no-buffer ZFC_model/CodeHierarchyBounds.vo > /tmp/pts-rk-code-hierarchy-fresh.log 2>&1
```

Recursive kernel check (exit 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-code-hierarchy-fresh.Cehkq2/default/vendor/zfc ZFC -Q /tmp/pts-rk-code-hierarchy-fresh.Cehkq2/default/theories PTSrk -Q /tmp/pts-rk-code-hierarchy-fresh.Cehkq2/default/ZFC_model PTSrkModel PTSrkModel.CodeHierarchyBounds > /tmp/pts-rk-code-hierarchy-kernel.log 2>&1
```

Full local CI (exit 0; 96 stages; CodeHierarchyBounds was covered by the
separate fresh build/kernel check rather than a CI stage in this checkpoint):

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/code-hierarchy-final" bash tools/check-local-ci.sh > /tmp/pts-rk-code-hierarchy-ci.log 2>&1
```

The checks establish Ens rank bounds only. They do not prove BZC hierarchy
existence, GCH/cardinal coding, or PTS model soundness.
