# Cardinal growth — 2026-10-14

HEAD 91156df3c7fb387f300a83993b4710fd45c81a35, continued uncommitted work.
Earlier CountableCodes changes preserved. No commit/push requested this turn.
Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Equations 1.3.2+9.2.
Commands run from the repository root with:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

1. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CardinalGrowth.vo > /tmp/pts-rk-zfc-growth-1.log 2>&1` — exit 0; seven new assumption reports closed.
2. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CardinalHierarchy.vo > /tmp/pts-rk-zfc-growth-2.log 2>&1` — exit 0; seven additional closed reports. No compiler failure occurred.
3. `mktemp -d /tmp/pts-rk-zfc-growth-fresh.XXXXXX` yielded `/tmp/pts-rk-zfc-growth-fresh.9Nx7jR`.
4. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-zfc-growth-fresh.9Nx7jR --display=short --no-buffer ZFC_model/CardinalHierarchy.vo ZFC_model/CodedFunctions.vo > /tmp/pts-rk-zfc-growth-fresh.log 2>&1` — exit 0; all 67 model reports closed, exact principal theorem types printed.
5. `opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-zfc-growth-fresh.9Nx7jR/default/vendor/zfc ZFC -Q /tmp/pts-rk-zfc-growth-fresh.9Nx7jR/default/ZFC_model PTSrkModel PTSrkModel.CardinalHierarchy PTSrkModel.CodedFunctions > /tmp/pts-rk-zfc-growth-kernel.log 2>&1` — exit 0; no axioms or unsafe checking assumptions.
6. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-growth-final" bash tools/check-local-ci.sh > /tmp/pts-rk-zfc-growth-ci.log 2>&1` — exit 0; pristine upstream and all 89 stages pass. Two new stages, none removed or relaxed. Full individual logs remain in the diagnostic directory; summaries are copied here.

The carriers are concrete powerset iterates. These results do not identify
them as alephs, prove the GCH classification/product bound, or establish
the PTS soundness theorem. Raw compiler logs are retained verbatim.
