# Powerset embeddings — 2026-10-14

Previous work committed as 5872c848ea9d92339107685f3fd9396010d72218, without
push. New proof work remains uncommitted. Rocq 9.2.0, OCaml 4.14.2,
Dune 3.23.1, Equations 1.3.2+9.2. All commands from repository root, with:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

1. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/PowersetEmbedding.vo > /tmp/pts-rk-zfc-powerset-1.log 2>&1` — exit 0, six new audits closed.
2. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SubsetFunctions.vo > /tmp/pts-rk-zfc-powerset-N.log 2>&1` for N=2,3 — exits 1,0. The failure was inability to infer the domain arguments of flatten_injective; explicit A/B fixed it without weakening any theorem.
3. Added the combined dependent-product/subset theorem. `mktemp -d /tmp/pts-rk-zfc-powerset-fresh.XXXXXX` yielded `/tmp/pts-rk-zfc-powerset-fresh.vQKhh9`.
4. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-zfc-powerset-fresh.vQKhh9 --display=short --no-buffer ZFC_model/PowersetEmbedding.vo ZFC_model/SubsetFunctions.vo ZFC_model/CardinalHierarchy.vo ZFC_model/CodedFunctions.vo > /tmp/pts-rk-zfc-powerset-fresh.log 2>&1` — exit 0, all 79 reports closed, including twelve new results and the combined theorem.
5. `opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-zfc-powerset-fresh.vQKhh9/default/vendor/zfc ZFC -Q /tmp/pts-rk-zfc-powerset-fresh.vQKhh9/default/ZFC_model PTSrkModel PTSrkModel.PowersetEmbedding PTSrkModel.SubsetFunctions PTSrkModel.CardinalHierarchy PTSrkModel.CodedFunctions > /tmp/pts-rk-zfc-powerset-kernel.log 2>&1` — exit 0, no axioms or unsafe checking assumptions.
6. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-powerset-final" bash tools/check-local-ci.sh > /tmp/pts-rk-zfc-powerset-ci.log 2>&1` — exit 0, pristine upstream and all 91 stages pass. Two new stages, none removed or relaxed. Full per-stage logs remain in the diagnostic directory; summaries copied here.

These are embedding/exponent-step proofs, not the GCH rank bound, exact
cardinal-code classification, coherent choice or PTS soundness theorem.
