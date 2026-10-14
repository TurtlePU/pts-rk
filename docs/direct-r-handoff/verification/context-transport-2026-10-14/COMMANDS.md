# Context conversion transport — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental runs exited 0,1,1,0,0. Run 2 lacked the imported symmetry
instance for original beta equivalence; run 3 referenced an index name
changed by dependent elimination. Importing AbstractRewriting and letting
Rocq infer those indices fixed the errors without statement changes.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ContextTransport.vo > /tmp/pts-rk-context-transport-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ContextTransport.vo > /tmp/pts-rk-context-transport-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ContextTransport.vo > /tmp/pts-rk-context-transport-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ContextTransport.vo > /tmp/pts-rk-context-transport-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ContextTransport.vo > /tmp/pts-rk-context-transport-5.log 2>&1
```

Each following verification command exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-context-transport-fresh.0Q2xfP --display=short --no-buffer ZFC_model/ContextTransport.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-context-transport-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-context-transport-fresh.0Q2xfP/default/vendor/zfc ZFC -Q /tmp/pts-rk-context-transport-fresh.0Q2xfP/default/theories PTSrk -Q /tmp/pts-rk-context-transport-fresh.0Q2xfP/default/ZFC_model PTSrkModel PTSrkModel.ContextTransport PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-context-transport-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/context-transport-final" bash tools/check-local-ci.sh > /tmp/pts-rk-context-transport-ci.log 2>&1
```

All 127 stages passed. Fresh build printed 236 closed reports including
dependencies; library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. No timeouts.

Seven new module assumption reports closed. denotes_context_conversion is
printed in runs 4–5 and the fresh build. Its premises are syntactic context
convertibility and original well-formedness, not semantic coherence or
soundness. General term conversion, typing soundness and the first-order
BZC interpretation remain unproved; context transport alone does not imply
any of those targets or transport valid_valuation across conversion.
