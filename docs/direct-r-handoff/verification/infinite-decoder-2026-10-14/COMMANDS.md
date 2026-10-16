# Infinite decoder branch — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental exits 1,0: corrected an extra bracket in a destruct pattern.
Four closed reports, with supplied hierarchy premises explicit.
The statements quantify over every infinite code and include agreement
with existing decode. This does not establish sort decoding/full soundness.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedInfiniteDecoder.vo > /tmp/pts-rk-infinite-decoder-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedInfiniteDecoder.vo > /tmp/pts-rk-infinite-decoder-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-infinite-decoder-fresh.e5hwSB --display=short --no-buffer ZFC_model/BoundedInfiniteDecoder.vo > /tmp/pts-rk-infinite-decoder-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/infinite-decoder-final" bash tools/check-local-ci.sh > /tmp/pts-rk-infinite-decoder-ci.log 2>&1
```

Fresh build, source comparison, recursive kernel check and full CI exited
0; all 143 stages passed. Fresh dependency build printed 153 closed reports.
Kernel summary lists existing functional_extensionality_dep; no unsafe
settings. No timeouts. HEAD 33d05ab unchanged; work uncommitted/unpushed.

```sh
cmp ZFC_model/BoundedInfiniteDecoder.v /tmp/pts-rk-infinite-decoder-fresh.e5hwSB/default/ZFC_model/BoundedInfiniteDecoder.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-infinite-decoder-fresh.e5hwSB/default/vendor/zfc ZFC -Q /tmp/pts-rk-infinite-decoder-fresh.e5hwSB/default/theories PTSrk -Q /tmp/pts-rk-infinite-decoder-fresh.e5hwSB/default/ZFC_model PTSrkModel PTSrkModel.BoundedInfiniteDecoder > /tmp/pts-rk-infinite-decoder-kernel.log 2>&1
```
