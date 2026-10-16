# Formula-defined bounded graphs — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFormulaTransport.vo > /tmp/pts-rk-bounded-graph-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFormulaTransport.vo > /tmp/pts-rk-bounded-graph-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedGraphs.vo > /tmp/pts-rk-bounded-graph-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedGraphs.vo > /tmp/pts-rk-bounded-graph-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedGraphs.vo > /tmp/pts-rk-bounded-graph-5.log 2>&1
```

Incremental exits 1,0,1,0,0. First error: explicit Formula constructor
indices and dependent return type needed in rename_formula. Second:
uninstantiated proof placeholders in holds_extensional applications;
fixed by naming the pointwise environment equalities. All failures retained.
Seven new closed Print Assumptions reports: holds_rename,
graph_lift_correct, graph_certificate_correct, bounded_formula_graph_spec,
bounded_formula_graph_agrees, bounded_formula_graph_typed,
bounded_formula_function. No Choice premise in the graph construction.
The bounded formula defining the decoder itself is not supplied here;
the Ens/Prod first-order foundation audit and model soundness remain open.

Fresh isolated build, both source comparisons, recursive kernel check and
full CI exited 0. Fresh build printed 278 closed reports with dependencies;
all 133 CI stages passed. Library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. No timeouts.

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-graph-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-graph-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-graph-fresh.N0kunF --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo ZFC_model/BoundedGraphs.vo > /tmp/pts-rk-bounded-graph-fresh.log 2>&1
cmp ZFC_model/BoundedGraphs.v /tmp/pts-rk-bounded-graph-fresh.N0kunF/default/ZFC_model/BoundedGraphs.v
cmp ZFC_model/BoundedFormulaTransport.v /tmp/pts-rk-bounded-graph-fresh.N0kunF/default/ZFC_model/BoundedFormulaTransport.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-graph-fresh.N0kunF/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-graph-fresh.N0kunF/default/theories PTSrk -Q /tmp/pts-rk-bounded-graph-fresh.N0kunF/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta PTSrkModel.BoundedGraphs > /tmp/pts-rk-bounded-graph-kernel.log 2>&1
```
