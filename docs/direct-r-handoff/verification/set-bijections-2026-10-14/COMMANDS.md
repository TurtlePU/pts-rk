# Bijections and coded functions — 2026-10-14

Previous checkpoint committed as 072c6d96c31557ae3c36563d8466c53a1c54f6f4;
not pushed (no push requested). This proof continuation is uncommitted.
Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Equations 1.3.2+9.2.
Commands run from the repository root, with direct opam environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

1. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CodeUniverses.vo ZFC_model/SetApplication.vo > /tmp/pts-rk-zfc-bijections-baseline.log 2>&1` — exit 0 (cached; empty log).
2. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SetBijections.vo > /tmp/pts-rk-zfc-bijections-1.log 2>&1` — exit 0, inverse and identity/symmetry proofs checked.
3. After composition and coded functions, `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CodedFunctions.vo > /tmp/pts-rk-zfc-bijections-N.log 2>&1` for N = 2,3,4. Exits 1,1,0. Both failures concern inference of the composite graph's body; explicit graph_beta arguments fix it. No theorem statement weakened.
4. `mktemp -d /tmp/pts-rk-zfc-bijections-fresh.XXXXXX` yielded `/tmp/pts-rk-zfc-bijections-fresh.c1GfHf`.
5. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-zfc-bijections-fresh.c1GfHf --display=short --no-buffer ZFC_model/CodedFunctions.vo ZFC_model/CodeUniverses.vo > /tmp/pts-rk-zfc-bijections-fresh.log 2>&1` — exit 0, 36 closed reports, including 15 new ones. Public coded_beta and empty-fiber transport theorem types are printed.
6. `opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-zfc-bijections-fresh.c1GfHf/default/vendor/zfc ZFC -Q /tmp/pts-rk-zfc-bijections-fresh.c1GfHf/default/ZFC_model PTSrkModel PTSrkModel.CodedFunctions PTSrkModel.CodeUniverses > /tmp/pts-rk-zfc-bijections-kernel.log 2>&1` — exit 0, no axioms, type-in-type, unsafe fixpoints or assumed positivity.
7. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-bijections-final" bash tools/check-local-ci.sh > /tmp/pts-rk-zfc-bijections-ci.log 2>&1` — exit 0, pristine upstream and all 85 stages pass. Two new stages added, none removed or relaxed. Result and stage summaries copied here; full individual logs remain in the diagnostic directory.

These proofs construct inverse/composite graphs and establish local laws for
a supplied coding bijection. They do not prove the existence/coherence of
cardinal-coding bijections, the GCH bound or PTS typing soundness.
