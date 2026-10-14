# PTS-rk set model

Library: `PTSrkModel`. Reference: the set-model section of
[paper.tex](../../latex/paper.tex). Dependency: the pinned LGPL subset of
[rocq-archive/zfc](../../vendor/zfc/README.md).

## Proved soundness and explicit parameters

`ModelSoundness.original_typing_sound` proves realization for every ORIGINAL
`Typing.typ` derivation in a well-formed context and every original valid
valuation. Its premises do not assume semantic conversion, coherence,
certificate totality, or normalization.

The set-theoretic parameters remain explicit:

- A transitive set W containing omega_codes and a supplied tower envelope H.
- Classical excluded middle, cardinal comparability, the infinite powerset
  gap (the GCH consequence used here), and ordinary set-indexed family choice.
- A global selector satisfying its witness-selection specification. The
  model-existence theorem constructs such a selector from family choice.

`original_membership_sound` handles arbitrary original denotation witnesses;
`RankedNormalization.original_typed_conversion_values` proves equality of their
actual values for typed beta-convertible terms. `sound_nontrivial_model_exists` combines soundness with
an empty interpretation of Bottom. These results concern the original
annotated syntax, denotation, and validity, not a replacement typing relation.

## Foundation-strength boundary — still open

The present Ens construction and soundness proof are not yet a formal
interpretation inside material BZC. Read [BZC_AUDIT.md](BZC_AUDIT.md) for the
precise GCH convention, rank bounds, relative-model obstruction, and next goal,
and [FOUNDATIONS.md](FOUNDATIONS.md) for the development history.

For this collected set-sized construction, BZC plus injection-gap GCH alone
does not guarantee the supplied envelope. Supplying the actual
V_(omega+omega) provides the required bounds, including finite powersets
above that envelope for global data. No additional collected hierarchy above
it has been identified as necessary. This mathematical audit is not a
completed Rocq derivation of the model in the weaker theory.

The first remaining formal obligation is an explicit bounded formula for
the original denotation-witness relation, with agreement on original typed
valid valuations. Native arbitrary-predicate separation is not certified
merely by bounding its output. Material cardinal-comparison/GCH and hierarchy
bridges also remain to be proved. Closed `Print Assumptions` reports for
parameterized Ens theorems do not discharge these obligations.

## Module map

| Group | Modules and purpose |
| --- | --- |
| Set operations and codes | `SetFunctions`, `SetApplication`, `CodeUniverses`, `SetBijections`, `CodedFunctions`, and product/cardinal modules construct actual functions, code universes, and ranked product witnesses |
| Supplied hierarchy | `HierarchyBounds`, `SuppliedHierarchy`, `CodeHierarchyBounds` bound the same construction inside a supplied envelope |
| Bounded constructions | `BoundedFormulas`, `BoundedGraphs`, `BoundedIteration`, `BoundedRecursion`, decoder and selection modules certify specific bounded predicates and agreement with existing operations |
| Material logic | `MaterialSetTheory` defines independent first-order syntax/deduction; `MaterialZermelo` gives the BZC axioms and proves their Ens satisfaction under explicit logic/choice |
| Original semantics | `Denotation`, `InterpretedContexts`, `GlobalOperations`, and rule/choice/transport modules retain original typing witnesses and values |
| Normalization bridge | `NeutralCutRank`, `RankedDenotation`, `RankedTransport`, `RankedSubstitution`, `RankedRootBeta`, `RankedHereditary`, `RankedNormalization` establish actual-value-preserving normalization and semantic conversion |
| Final theorems | `ModelSoundness` discharges the conversion premise of `RealizationInduction` and exports original typing soundness, coherence, membership, and nontrivial model existence |

The `Canonical*` and `TypedEquality*` modules retain useful auxiliary
certificates and restricted lemmas. Their local hypotheses are not extra
hypotheses of the final original-typing theorem. Historical descriptions of
open conversion/soundness in old handoff entries are superseded by
`ModelSoundness`; the material foundation reduction is not.

## Build, imports, and assumptions

From the repository root in the [pinned environment](../../docs/DirectR-CI.md):

```sh
dune build theories/ZFC_model/ModelSoundness.vo
dune build @theories/ZFC_model/audit
```

The audit alias compiles `ModelSoundness` and `MaterialZermelo`, including
their source-level assumption reports. For a fresh audit, use a new absolute
`--build-dir`; an incremental successful build can reuse cached output.

```coq
From PTSrkModel Require Import ModelSoundness RankedNormalization.
Check ModelSoundness.original_typing_sound.
Check ModelSoundness.original_membership_sound.
Check RankedNormalization.original_typed_conversion_values.
Check ModelSoundness.sound_nontrivial_model_exists.
Print Assumptions ModelSoundness.original_typing_sound.
Print Assumptions ModelSoundness.sound_nontrivial_model_exists.
```

The [live state](../../docs/direct-r-handoff/STATE.md) records exact commands,
versions, theorem types, logs, and the next proof obligation. This directory's
physical location does not change the `PTSrkModel` import namespace.
