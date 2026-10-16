# Bounded model data and native typed equality — 2026-10-14

Parent: 3454c9f, unchanged. This continuation is uncommitted/unpushed.
Previous combined-decoder work and unrelated user logs/ are preserved.

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

## Baseline and bounded constructions

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo > /tmp/pts-rk-semantic-continuation-baseline.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedModelData.vo > /tmp/pts-rk-bounded-model-data-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedChoiceSequence.vo ZFC_model/CardinalClassification.vo > /tmp/pts-rk-choice-classification-1.log 2>&1
```

All three exited 0. The choice-sequence implementation attempts used the
following exact command templates (N is the retained logfile suffix):

```sh
# N=1,2,6
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedChoiceSequence.vo > /tmp/pts-rk-bounded-choice-sequence-N.log 2>&1
# N=3,4,5
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q _build/default/vendor/zfc ZFC -Q _build/default/theories PTSrk -Q _build/default/ZFC_model PTSrkModel -Q ZFC_model PTSrkModel ZFC_model/BoundedChoiceSequence.v > /tmp/pts-rk-bounded-choice-sequence-N.log 2>&1
```

Exits: 1,1,1,0,0,1. First two failures were module enumeration/in-progress
parallel files; third was a dependent transport simplification; sixth was
a generated source-tree glob collision. Direct compiler artifacts were
moved to /tmp/pts-rk-choice-direct-artifacts.VHCXUp before the successful
integrated Dune build. Failed logs are retained, not relabeled successes.

## Native equality iterations

Attempts 1–6 copied each revised source to the same temporary directory:

```sh
cp ZFC_model/TypedEquality.v /tmp/pts-rk-typed-equality.XDTjE0/TypedEquality.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq c -Q _build/default/theories PTSrk -Q _build/default/ZFC_model PTSrkModel -Q _build/default/vendor/zfc ZFC -Q /tmp/pts-rk-typed-equality.XDTjE0 PTSrkModel /tmp/pts-rk-typed-equality.XDTjE0/TypedEquality.v > /tmp/pts-rk-typed-equality-N.log 2>&1
```

All six exited 1. Attempts 1–5 were proof elaboration/tactic errors;
attempt 6 found inconsistent assumptions during concurrent rebuilding of
CardinalClassification. Attempt 7 used the previously completed isolated
snapshot, with the same final source copy:

```sh
opam exec --switch=pts-rk-ci -- timeout 120 rocq c -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/theories PTSrk -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/vendor/zfc ZFC -Q /tmp/pts-rk-typed-equality.XDTjE0 PTSrkModel /tmp/pts-rk-typed-equality.XDTjE0/TypedEquality.v > /tmp/pts-rk-typed-equality-7.log 2>&1
cmp ZFC_model/TypedEquality.v /tmp/pts-rk-typed-equality.XDTjE0/TypedEquality.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq check -silent -o -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/theories PTSrk -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-combined-decoder-fresh.CfP1CM/default/vendor/zfc ZFC -Q /tmp/pts-rk-typed-equality.XDTjE0 PTSrkModel PTSrkModel.TypedEquality > /tmp/pts-rk-typed-equality-kernel.log 2>&1
```

All three exited 0. Five closed assumption reports for the new module.

## Fresh combined verification

The fresh directory was allocated by mktemp -d; expanded path below.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-semantic-foundation-fresh.EU65sO --display=short --no-buffer ZFC_model/BoundedChoiceSequence.vo ZFC_model/BoundedModelData.vo ZFC_model/TypedEquality.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-semantic-foundation-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/semantic-foundation-final" bash tools/check-local-ci.sh > /tmp/pts-rk-semantic-foundation-ci.log 2>&1
cmp ZFC_model/BoundedChoiceSequence.v /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model/BoundedChoiceSequence.v
cmp ZFC_model/BoundedModelData.v /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model/BoundedModelData.v
cmp ZFC_model/TypedEquality.v /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model/TypedEquality.v
cmp ZFC_model/CardinalClassification.v /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model/CardinalClassification.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel PTSrkModel.BoundedChoiceSequence PTSrkModel.BoundedModelData PTSrkModel.TypedEquality PTSrkModel.RealizationInduction PTSrkModel.RootBeta > /tmp/pts-rk-semantic-foundation-kernel.log 2>&1
```

All exited 0. All 150 CI stages passed, including pristine upstream. Fresh
build printed 393 closed reports, including 29 new reports (16 bounded
choice sequence, 8 bounded model data, 5 native equality). Recursive kernel
audit lists only the existing functional_extensionality_dep; no unsafe
fixpoints, type-in-type or assumed positivity. No timeouts.

The actual classification path now uses the bounded countable injection;
selector and decoder set bounds are proved. Native equality projects to
original typing and beta equality, preserving lambda annotations. These
are not completeness of native equality, semantic conversion, unconditional
model soundness, or derivability in first-order BZC. Those remain open.
