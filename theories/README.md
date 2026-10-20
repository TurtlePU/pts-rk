# Rocq developments

Run all commands below from the repository root in the
[documented toolchain](../docs/DirectR-CI.md).

## Original kernel

The files directly in this directory form library `PTSrk`:

- `Syntax`, `Context`: scoped, annotated terms and contexts.
- `AbstractRewriting`, `Congruence`, `Reduction`, `Confluence`, `DefEq`:
  beta reduction and conversion.
- `Typing`, `Inversions`, `Preservation`: original PTS typing and metatheory.
- `SN`, `Ranks`: strong normalization and the rank-sort instance.

These kernel files are unchanged by the directory reorganization.

## Separate developments

| Folder | Library | Audit target |
| --- | --- | --- |
| [Interpretation_of_R](Interpretation_of_R/README.md) | `Interpretation_of_R` (shared) | Used by both independent interpretation audits |
| [relational](Interpretation_of_R/relational/README.md) | `Interpretation_of_R.relational` | `@theories/Interpretation_of_R/relational/audit` |
| [functional](Interpretation_of_R/functional/README.md) | `Interpretation_of_R.functional` | `@theories/Interpretation_of_R/functional/audit` |
| [ZFC_model](ZFC_model/README.md) | `PTSrkModel` | `@theories/ZFC_model/audit` |
| [NormalizationComplexity](NormalizationComplexity/README.md) | `PTSrk.NormalizationComplexity` | `@theories/NormalizationComplexity/audit` |
| [self_interpreter](self_interpreter/README.md) | `PTSrk.SelfInterpreter` | `@theories/self_interpreter/audit` |

Each folder has its own Dune theory stanza. Both arithmetic interpretations
depend on the shared arithmetic library and kernel, not on one another or
the set model. The set model additionally uses normalization-complexity
infrastructure and the pinned vendored `ZFC` theory.

```sh
dune build theories/Ranks.vo
dune build
```

Import names are stable despite the physical moves, for example:

```coq
From PTSrk Require Import Syntax Typing Ranks.
From Interpretation_of_R.relational Require Import DirectRTheorem4.
From Interpretation_of_R.functional Require Import DirectRTheorem7.
From PTSrkModel Require Import ModelSoundness.
From PTSrk.NormalizationComplexity Require Import Normalization.
```

See the [repository README](../README.md) and
[live handoff](../docs/direct-r-handoff/STATE.md) for result boundaries and evidence.
