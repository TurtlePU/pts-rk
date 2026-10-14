# Shared beta value from realizations — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental build exited 0. One new closed assumption report for
realized_beta; Check prints all constituent-realization and decoded
coherence premises explicitly.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationBeta.vo > /tmp/pts-rk-realized-beta-1.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/realized-beta-final" bash tools/check-local-ci.sh > /tmp/pts-rk-realized-beta-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-realized-beta-fresh.nAJ0iJ --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-realized-beta-fresh.log 2>&1
```

The theorem constructs a common value for redex/reduct and a ranked code
for the actual substituted result type. It does not prove coherence of
all alternative denotations or the constituent induction premises.
Full soundness and first-order BZC justification remain open.

Fresh build and full CI exited 0. Fresh build printed 260 closed reports
including dependencies; all 131 CI stages passed. Source cmp exited 0.
No failed compiler runs or timeouts in this milestone.
Recursive kernel check exited 0. Library-wide summary lists imported
functional_extensionality_dep, no unsafe settings.

```sh
cmp ZFC_model/DenotationBeta.v /tmp/pts-rk-realized-beta-fresh.nAJ0iJ/default/ZFC_model/DenotationBeta.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-realized-beta-fresh.nAJ0iJ/default/vendor/zfc ZFC -Q /tmp/pts-rk-realized-beta-fresh.nAJ0iJ/default/theories PTSrk -Q /tmp/pts-rk-realized-beta-fresh.nAJ0iJ/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-realized-beta-kernel.log 2>&1
```
