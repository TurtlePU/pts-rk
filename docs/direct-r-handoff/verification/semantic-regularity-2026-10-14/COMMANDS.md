# Typed semantic regularity — 2026-10-14

Environment (repository root):

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Commands executed:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo > /tmp/pts-rk-semantic-regularity-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo > /tmp/pts-rk-semantic-regularity-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-semantic-regularity-fresh.ndBrvb --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo ZFC_model/BoundedFiniteCarriers.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-semantic-regularity-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/semantic-regularity-final" bash tools/check-local-ci.sh > /tmp/pts-rk-semantic-regularity-ci.log 2>&1
```

Incremental exits 1,0. First failure: decode_sort requires the carrier
argument before the natural index. Corrected without changing the theorem.
All five module assumption reports are closed (three newly added), but
the printed theorem type explicitly includes the UNPROVED conversion
premise. This is not unconditional soundness or a first-order BZC proof.

Fresh build, source comparison, recursive kernel check and local CI exited
0. All 136 CI stages passed; fresh build printed 298 closed reports including
dependencies. Library-wide kernel summary lists the existing imported
functional_extensionality_dep; no unsafe settings. No timeouts.

```sh
cmp ZFC_model/RealizationInduction.v /tmp/pts-rk-semantic-regularity-fresh.ndBrvb/default/ZFC_model/RealizationInduction.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-semantic-regularity-fresh.ndBrvb/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-regularity-fresh.ndBrvb/default/theories PTSrk -Q /tmp/pts-rk-semantic-regularity-fresh.ndBrvb/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta PTSrkModel.BoundedFiniteCarriers PTSrkModel.RealizationInduction > /tmp/pts-rk-semantic-regularity-kernel.log 2>&1
```
