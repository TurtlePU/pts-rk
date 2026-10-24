# Ground Horn consistency and concrete Hilbert models — 23 October 2026

This is the local incremental proof ledger for GroundHornConsistency.v,
HilbertGrounding.v and HilbertFiniteModels.v. Root performs the independent
fresh Dune audit; the local checks below do not claim a pristine rebuild.
No Dune, CI, documentation or pre-existing proof source was edited by this
worker. No staging, commit, push, cleanup or deletion was performed.

## Environment and exact commands

Working directory: `/Users/akuklev/air/pts-rk`.

```sh
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq -v
/Users/akuklev/.local/share/pts-rk-ci/bin/opam list --installed --columns=name,version rocq-core rocq-stdlib rocq-equations ocaml dune
```

Both exit 0. `versions.log` reports Rocq 9.2 and OCaml 4.14.2.
`packages.log` confirms Rocq core 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. The initial bare `command -v opam` probe
found nothing; the explicit documented local executable above was used for
every compiler/checker invocation.

`commands.log` contains EVERY exact proof command, including the historical
load-path variants. `status.tsv` retains their actual exit codes. Every named
log begins with its UTC start time; end timestamps were not separately
recorded. `check.sh` is the final driver, not an assertion that its final
load paths were already used by earlier attempts. Each command redirects
compiler output to its named log and propagates the actual compiler exit.
`packages.log` was produced separately by the exact package command above,
with its exit appended to `status.tsv`.

## Consumed objects and mapping

- GroundHorn.vo was compiled from the unchanged current GroundHorn.v into
  `/tmp/pts-rk-horn-denials.ab2F9f` (base.log, exit 0).
- NativeCanonicity.vo was copied from the root worker's newly compiled
  `theories/CombinatoryLogic-rk/NativeCanonicity.vo` into that same directory.
- Existing catalogue dependencies were copied, preserving already present
  files, by `cp -n _build/default/theories/CombinatoryLogic-rk/*.vo
  /tmp/pts-rk-horn-denials.ab2F9f/`.
- The native kernel and normalization dependencies were read from
  `_build/default/theories` and its `NormalizationComplexity` subdirectory.
- FiniteHorn.vo was freshly compiled from the other worker's current
  FiniteHorn.v into this local object directory (finite-base.log, exit 0).
- Shared DirectREval.vo was copied from
  `_build/default/theories/Interpretation_of_R/DirectREval.vo`. The final
  equality dependency location is `/tmp/pts-rk-horn-equality.hjwmlu/DirectREval.vo`.
  Earlier load-path attempts used the original directory, then a temporary
  nested `/tmp/pts-rk-horn-denials.ab2F9f/eval` copy. No arithmetic model was
  imported; DirectREval belongs to the shared Interpretation_of_R library.
- The new modules' .vo files are in `/tmp/pts-rk-horn-denials.ab2F9f`.
  These generated objects are disposable caches, not archive content.

## Attempts and corrections

GroundHornConsistency compilation:

- attempt-01: exit 1, an over-generalized list induction in
  model_implies_consistency; replaced by Forall_impl.
- attempt-02: exit 1, an incomplete dependent induction in all_true_rejected;
  replaced by Forall_forall and the direct proof of True.
- attempt-03: exit 0, initial interface, 21 closed assumption reports.
- kernel: exit 0, recursive complete dependency check of that checkpoint;
  empty axiom and unsafe inventory.
- attempt-04: exit 1 after adding finite support, an uninferred Atom type in
  fragment_derives_mono; explicit list types added.
- attempt-05 and attempt-06: exit 1, induction tactic invocation could not
  instantiate the exported mutual induction principle; replaced with an
  explicit application of GroundHorn.Derives_ind'.
- attempt-07: exit 1, a repeated local binder name; renamed the outer goal atom.
- attempt-08: exit 0, final finite-support/compactness interface, 26 closed
  reports. This final version is recursively included by the later successful
  HilbertGrounding and HilbertFiniteModels checks.

HilbertGrounding compilation:

- hilbert-01: exit 1, duplicate GroundHorn.vo under overlapping catalogue
  mappings; gathered the required existing catalogue objects in one mapping.
- hilbert-02: exit 1, failed inference of the catalogue scheme label; supplied
  its explicit subject/type functions. This attempt also emitted incompatible
  bracket-notation warnings; the source now uses nil/cons and imports no
  ListNotations alongside native lambda brackets.
- hilbert-03: exit 1, unfolding did not expose the forbidden type equation;
  changed explicitly to `A = NativeCanonicity.Void` before substitution.
- hilbert-04: exit 0, 16 closed reports, no warnings.
- hilbert-kernel: exit 0, full recursive check. Inventory contains only
  inherited functional_extensionality_dep; no unsafe entries.

HilbertFiniteModels compilation:

- model-01: exit 1, applying member_spec's iff to a reducible truth predicate;
  used its explicit forward projection. Existing shared-library mappings also
  generated load-path remapping warnings.
- model-02: exit 1, the same iff projection issue in the concrete native-typing
  regression; fixed explicitly. The same mapping warnings were present.
- model-03: exit 1, the nested equality-library map was overridden by the
  enclosing combinatory map, so DirectREval was not found.
- model-04: exit 0, 21 closed reports, with one benign logical-loadpath
  remapping warning from the nested temporary equality directory.
- model-05: exit 0, 21 closed reports, no warnings, using the separate final
  equality directory.
- finite-kernel: exit 0, full recursive check. Inventory contains only
  inherited functional_extensionality_dep; no unsafe entries.

All check commands are ordinary `rocq check -silent -o` over the complete
new dependency closure, without admission/skip flags or disabled checks.
No timeout or interrupted command occurred in this worker's proof attempts.

## Final sources and exact scope

After model-05/finite-kernel, one COMMENT was corrected: signed completion is
an explicit strengthening, not a conservative expansion. No declaration or
proof changed. Root's fresh integrated audit compiles this final source.

Final SHA-256:

```text
eb320388db81d0bbb9ad83c38118657e38103f53d4b2e73fedb37802fa2da436  GroundHornConsistency.v
38f5a91ceedba83b7b2aa0115514064f3ab113b236e67bfc6bf052e394d06266  HilbertGrounding.v
561b393e32fd113ad3b1c10cb95a9e0eebd6540578a776759e4a57e4cbf3b2e9  HilbertFiniteModels.v
```

The generic denial theory proves conditional consistency/model equivalence
without assuming a semantic model. The concrete Hilbert instance DISCHARGES
that condition using original catalogue soundness and proved native Void
exclusion. The finite saturation models satisfy all syntactic Void denials,
including subjects absent from the input fragment. Complete reflection is
for the selected finite clause theory; signed diagrams deliberately add
negative information. No MM0 adequacy, original-PTS-to-catalogue completeness,
finite ungrounded PTS algebra, or internal PTS reflection theorem is claimed.

Scoped `git diff --check` succeeded. Its output was empty and not separately
saved; source hashes were printed by the shell, as reproduced above.

## Independent read-only review

Read the complete current FiniteUniversalHorn.v, FiniteModelBoundary.v,
FiniteHornChurch.v, and the note's model-boundary/ground-model/candidate
subsections. No source edits resulted from this review.

- The universal candidate theorem proves satisfaction over EVERY enumerated
  semantic vector, with domain completeness a finite-carrier premise rather
  than a consistency/model premise. Checker acceptance is a computed Boolean
  condition; its equivalence to predicate-model existence is proved. Domain
  nonemptiness is explicit in fixed_finite_model. There is no hidden assumption
  that all candidates or all PTS fragments admit such an interpretation.
- Semantic templates are supplied functions, not a checked translation of
  the PTS/MM0 signature. The note correctly keeps that translation and
  suitable constructor tables open, and explicitly requires a fixed actual
  equality interpretation rather than arbitrary saturated equality atoms.
- The finite-K obstruction assumes one total untyped binary operation and
  an unguarded universal EQUATION. Its finite-injection/surjection proof is
  sound and needs no classical axiom. The note does not improperly transfer
  this obstruction to guarded/rank-indexed application or directed red.
- Church table compilation is externally specialized. Rank and beta-output
  correctness are proved for canonical query selectors; no internal universal
  reflection or general saturation algorithm is inferred. The note says this.
- Signed-diagram negatives are explicit strengthening and relative to the
  chosen finite rule list. The note distinguishes their complete propositional
  reflection from source-theory completeness and quantified PTS semantics.
