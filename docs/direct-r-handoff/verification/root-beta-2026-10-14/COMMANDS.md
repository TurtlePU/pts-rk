# Arbitrary-witness root-beta constructor step — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental exits 0,0,0. Run 2 restricts the semantic conversion premises
to well-typed types. Run 3 transports the codomain into the lambda context
so the conversion premise is same-context. One new closed Print Assumptions
report; Check prints all remaining semantic premises explicitly.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo > /tmp/pts-rk-root-beta-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo > /tmp/pts-rk-root-beta-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo > /tmp/pts-rk-root-beta-3.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/root-beta-final" bash tools/check-local-ci.sh > /tmp/pts-rk-root-beta-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-root-beta-fresh.JO0GsL --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-root-beta-fresh.log 2>&1
```

This is not final beta preservation or model soundness: local conversion,
rank and membership premises still need the joint fundamental proof.
First-order bounded denotation and BZC foundations remain open as well.

Fresh isolated build and full CI exited 0; the fresh build printed 256
closed reports including dependencies. All 131 CI stages passed. Source
cmp exited 0. No failed builds or timeouts in this milestone.
Recursive kernel check exited 0. Its library-wide summary lists imported
functional_extensionality_dep and no unsafe settings.

```sh
cmp ZFC_model/RootBeta.v /tmp/pts-rk-root-beta-fresh.JO0GsL/default/ZFC_model/RootBeta.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-root-beta-fresh.JO0GsL/default/vendor/zfc ZFC -Q /tmp/pts-rk-root-beta-fresh.JO0GsL/default/theories PTSrk -Q /tmp/pts-rk-root-beta-fresh.JO0GsL/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-root-beta-kernel.log 2>&1
```
