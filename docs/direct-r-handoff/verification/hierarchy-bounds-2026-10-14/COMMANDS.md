# Hierarchy bounds — 2026-10-14

Working directory: /Users/akuklev/air/pts-rk.
HEAD: 5872c848ea9d92339107685f3fd9396010d72218; work uncommitted.

Environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental command, run twice (both exit 0), output redirected respectively
to /tmp/pts-rk-hierarchy-1.log and /tmp/pts-rk-hierarchy-2.log:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/HierarchyBounds.vo
```

Fresh build (exit 0; 42 closed assumption reports including dependencies):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-hierarchy-fresh.DtcwD8 --display=short --no-buffer ZFC_model/HierarchyBounds.vo > /tmp/pts-rk-hierarchy-fresh.log 2>&1
```

Recursive kernel check (exit 0; no axioms, type-in-type, unsafe fixpoints or
assumed positivity):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-hierarchy-fresh.DtcwD8/default/vendor/zfc ZFC -Q /tmp/pts-rk-hierarchy-fresh.DtcwD8/default/ZFC_model PTSrkModel PTSrkModel.HierarchyBounds > /tmp/pts-rk-hierarchy-kernel.log 2>&1
```

Full local CI, including pristine upstream (exit 0; 94 stages):

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/hierarchy-final" bash tools/check-local-ci.sh > /tmp/pts-rk-hierarchy-ci.log 2>&1
```

Raw logs, stages.tsv and result.txt are retained alongside this file.
These checks certify the stated rank bounds in Ens, not first-order BZC
derivability, hierarchy existence or the full PTS model soundness theorem.
