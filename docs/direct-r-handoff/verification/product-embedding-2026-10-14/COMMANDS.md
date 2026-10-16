# Product embedding — 2026-10-14

Prior checkpoint committed as 5c8476ed81316b5ba3cb259ffd4c4d170170705f; no
push requested/performed. This continuation remains uncommitted.
Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Equations 1.3.2+9.2.
Commands run from repository root with:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

1. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ProductEmbedding.vo > /tmp/pts-rk-zfc-product-1.log 2>&1` — exit 0.
2. After adding the graph-family variant, `mktemp -d /tmp/pts-rk-zfc-product-fresh.XXXXXX` yielded `/tmp/pts-rk-zfc-product-fresh.leuaTw`.
3. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-zfc-product-fresh.leuaTw --display=short --no-buffer ZFC_model/ProductEmbedding.vo ZFC_model/CodedFunctions.vo ZFC_model/CodeUniverses.vo > /tmp/pts-rk-zfc-product-fresh.log 2>&1` — exit 0, all 43 assumption reports closed, including seven new ones. Exact theorem types printed.
4. `opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-zfc-product-fresh.leuaTw/default/vendor/zfc ZFC -Q /tmp/pts-rk-zfc-product-fresh.leuaTw/default/ZFC_model PTSrkModel PTSrkModel.ProductEmbedding PTSrkModel.CodedFunctions PTSrkModel.CodeUniverses > /tmp/pts-rk-zfc-product-kernel.log 2>&1` — exit 0, no axioms or unsafe checking assumptions.
5. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-product-final" bash tools/check-local-ci.sh > /tmp/pts-rk-zfc-product-ci.log 2>&1` — exit 0, pristine upstream and all 86 stages pass, including the new product-embedding stage. No older stage removed or weakened. Full individual stage logs remain in that diagnostic directory; summaries copied here.

No failed compile occurred in this continuation. Existing checked baseline
evidence is retained in set-bijections-2026-10-14. This is a concrete product
injection proof, not a finalized cardinal bound or PTS soundness theorem.
