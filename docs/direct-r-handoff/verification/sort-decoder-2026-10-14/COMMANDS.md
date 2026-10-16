# Exact universes and sort decoder — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Each universe attempt used the following command, with N from 1 through 8.
Exits: 1,1,0,1,1,1,1,0. Failures are retained unchanged.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedUniverses.vo > /tmp/pts-rk-bounded-universes-N.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedSortDecoder.vo > /tmp/pts-rk-sort-decoder-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-sort-decoder-fresh.Dls1fb --display=short --no-buffer ZFC_model/BoundedSortDecoder.vo ZFC_model/BoundedInfiniteDecoder.vo ZFC_model/BoundedCodeSelection.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo > /tmp/pts-rk-sort-decoder-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/sort-decoder-final" bash tools/check-local-ci.sh > /tmp/pts-rk-sort-decoder-ci.log 2>&1
cmp ZFC_model/BoundedUniverses.v /tmp/pts-rk-sort-decoder-fresh.Dls1fb/default/ZFC_model/BoundedUniverses.v
cmp ZFC_model/BoundedSortDecoder.v /tmp/pts-rk-sort-decoder-fresh.Dls1fb/default/ZFC_model/BoundedSortDecoder.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-sort-decoder-fresh.Dls1fb/default/vendor/zfc ZFC -Q /tmp/pts-rk-sort-decoder-fresh.Dls1fb/default/theories PTSrk -Q /tmp/pts-rk-sort-decoder-fresh.Dls1fb/default/ZFC_model PTSrkModel PTSrkModel.BoundedSortDecoder PTSrkModel.BoundedInfiniteDecoder PTSrkModel.BoundedCodeSelection PTSrkModel.RealizationInduction PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization > /tmp/pts-rk-sort-decoder-kernel.log 2>&1
```

Sort incremental build, fresh build, both source comparisons and full CI
exited 0. All 145 CI stages passed. Fresh build printed 353 closed reports;
twelve are new universe/sort lemmas. Explicit premises remain premises.
This does not prove semantic conversion or unconditional model soundness.
Kernel-check result is recorded in STATE.md and its raw log here.

Checkpoint parent: 33d05ab. User authorized commit and push; unrelated
untracked logs/ are excluded. Next proof work: off-branch exclusion and
combined decoder agreement, then the open semantic conversion argument
and first-order foundation certification.
