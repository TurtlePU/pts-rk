# Original-typing realization induction — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFiniteCarriers.vo > /tmp/pts-rk-bounded-finite-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RegularTyping.vo > /tmp/pts-rk-regular-typing-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RegularTyping.vo > /tmp/pts-rk-regular-typing-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RegularTyping.vo > /tmp/pts-rk-regular-typing-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RegularTyping.vo > /tmp/pts-rk-regular-typing-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo > /tmp/pts-rk-realization-induction-1.log 2>&1
```

Incremental exits: finite carriers 0; regular typing 1,1,1,0; realization
induction 0. Retained errors: variable-constructor context inference under
substitution, dependent-elimination binder name, and unresolved sort witness
in original context embedding. Fixed by explicit constructor instantiation,
an explicit elimination pattern, and eassumption. No weakened statements.

Seventeen new closed assumption reports (8 finite-carrier, 7 syntactic
regular-typing, 2 conditional realization). The printed final theorem type
EXPLICITLY includes typed decoded conversion. It is not proved here and
not an axiom. No unconditional soundness or first-order BZC claim follows.

Fresh isolated build, all three source comparisons, recursive kernel check
and full local CI exited 0. Fresh build printed 295 closed reports including
dependencies; all 136 CI stages passed. Library-wide kernel summary lists
imported functional_extensionality_dep and no unsafe settings. No timeouts.

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/realization-induction-final" bash tools/check-local-ci.sh > /tmp/pts-rk-realization-induction-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-realization-induction-fresh.a9Wifu --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo ZFC_model/BoundedFiniteCarriers.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-realization-induction-fresh.log 2>&1
for model_file in BoundedFiniteCarriers.v RegularTyping.v RealizationInduction.v; do cmp "ZFC_model/$model_file" "/tmp/pts-rk-realization-induction-fresh.a9Wifu/default/ZFC_model/$model_file" || exit; done
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-realization-induction-fresh.a9Wifu/default/vendor/zfc ZFC -Q /tmp/pts-rk-realization-induction-fresh.a9Wifu/default/theories PTSrk -Q /tmp/pts-rk-realization-induction-fresh.a9Wifu/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta PTSrkModel.BoundedFiniteCarriers PTSrkModel.RealizationInduction > /tmp/pts-rk-realization-induction-kernel.log 2>&1
```
