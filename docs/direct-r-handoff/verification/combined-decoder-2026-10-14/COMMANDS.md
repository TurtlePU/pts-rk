# Combined decoder and decoded selection — 2026-10-14

Parent: 3454c9f, already pushed. This continuation is uncommitted/unpushed.
Unrelated user logs/ are preserved.

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Baseline exit 0. Decoder incremental exits 1,1,0,1,0: missing HierarchyBounds
import, multi-goal tactic dispatch and missing Cartesian import corrected.
Decoded selection exits 0,0. Failed compiler logs are retained unchanged.
The fresh directory was allocated by mktemp -d; its expanded path is below.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedSortDecoder.vo ZFC_model/BoundedInfiniteDecoder.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-combined-decoder-baseline.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedDecoder.vo > /tmp/pts-rk-combined-decoder-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedDecoder.vo > /tmp/pts-rk-combined-decoder-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedDecoder.vo > /tmp/pts-rk-combined-decoder-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedDecoder.vo > /tmp/pts-rk-combined-decoder-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedDecoder.vo > /tmp/pts-rk-combined-decoder-5.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedDecodedSelection.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-decoded-selection-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedDecodedSelection.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-decoded-selection-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-combined-decoder-fresh.CfP1CM --display=short --no-buffer ZFC_model/BoundedDecoder.vo ZFC_model/BoundedDecodedSelection.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-combined-decoder-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/combined-decoder-final" bash tools/check-local-ci.sh > /tmp/pts-rk-combined-decoder-ci.log 2>&1
cmp ZFC_model/BoundedDecoder.v /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/ZFC_model/BoundedDecoder.v
cmp ZFC_model/BoundedDecodedSelection.v /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/ZFC_model/BoundedDecodedSelection.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/vendor/zfc ZFC -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/theories PTSrk -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/ZFC_model PTSrkModel PTSrkModel.BoundedDecoder PTSrkModel.BoundedDecodedSelection PTSrkModel.RealizationInduction PTSrkModel.RootBeta > /tmp/pts-rk-combined-decoder-kernel.log 2>&1
```

Fresh build, both source comparisons, recursive kernel check and full local
CI exited 0. All 147 stages passed, including pristine upstream. Fresh
build printed 364 closed reports, including sixteen new reports. Kernel
summary lists existing functional_extensionality_dep; no unsafe settings
or timeouts. The staged runner's result, stages and versions are retained.

Scope: the complete bounded decoder graph equals all_decoding_graph. Its
integration into bounded selection preserves witness fibers, admissible
sources and the SAME selector's outputs. All code indices and admissible
sources are covered. Hierarchy, ordinary Choice and cardinal premises
remain explicit where used. This does NOT establish semantic conversion,
unconditional typing soundness or derivability in first-order BZC.
The next proof command and exact remaining goal are at the top of STATE.md.

