# Finite fragment normalization worker verification

Working directory: `/Users/akuklev/air/pts-rk`.
Only repository edit: new
`theories/self_consistency/FiniteFragmentNormalization.v`.

All compile/check commands use:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

The module source is copied to this fresh isolated directory before each
compile. Exact final command:

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories PTSrk \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-fragment-normalization.mLwZIp PTSrk.SelfConsistency \
  /tmp/pts-rk-fragment-normalization.mLwZIp/FiniteFragmentNormalization.v
```

- Attempt 01: exit 0, eight reports (initial per-certificate bridge).
- Attempt 02: exit 1: applying `normalb_sound` required an explicit term.
- Attempt 03: exit 0, ten reports (shared syntactic-bound fragment).
- Attempt 04: exit 1: higher-order inference for the subject-node bound.
- Attempt 05: exit 1: decoder destruction had already rewritten the goal.
- Attempt 06: exit 0, fourteen closed reports, 2.081 seconds.

Complete recursive final check uses exactly the same six `-Q` mappings:

```sh
opam exec -- timeout 600 rocq check -silent -o [the mappings above] \
  PTSrk.SelfConsistency.FiniteFragmentNormalization
```

No admission or non-recursive flags. Final check exit 0,
2026-10-23T08:08:31Z through 2026-10-23T08:08:46Z.
Earlier initial-version recursive check also exited 0, 08:03:43Z--08:04:00Z.
Full final context inventory matches the freshly checked pristine inventory
from the quantified-model audit exactly: only inherited
`functional_extensionality_dep`; no unsafe entries.

The copied final source equals the repository source and agrees with
`source-final.sha256`. Every original kernel, normalization and combinatory
source equals the loaded quantified-model build snapshot; all six loaded
self-consistency source dependencies equal the replacement build snapshot.
These comparisons exit 0, recorded in `dependency-source-agreement.log`.
This is an isolated focused check, not full repository CI or a fresh rebuild
of every dependency. The root agent performs the integrated fresh Dune audit.

Before the configured builds, a diagnostic `opam exec --switch=pts-rk-ci --
rocq --version` omitted OPAMROOT and failed because the default root was not
initialized. No compiler was run by that diagnostic. The subsequent commands
all use the explicit pinned environment above.
