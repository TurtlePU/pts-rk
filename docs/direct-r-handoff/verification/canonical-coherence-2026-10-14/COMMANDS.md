# Native weakening and canonical-denotation coherence — 2026-10-14

HEAD 3454c9f unchanged. All existing work and user logs/ preserved.
This is proof progress, not completed model soundness; no commit or push.

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

## Native weakening

Each of attempts 1–3 copied the revised source into the same isolated
temporary directory. N denotes the actual retained logfile suffix:

```sh
cp ZFC_model/TypedEqualityRenaming.v /tmp/pts-rk-typed-renaming.IAL7nA/TypedEqualityRenaming.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq c -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-typed-renaming.IAL7nA PTSrkModel /tmp/pts-rk-typed-renaming.IAL7nA/TypedEqualityRenaming.v > /tmp/pts-rk-typed-renaming-N.log 2>&1
cmp ZFC_model/TypedEqualityRenaming.v /tmp/pts-rk-typed-renaming.IAL7nA/TypedEqualityRenaming.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq check -silent -o -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-typed-renaming.IAL7nA PTSrkModel PTSrkModel.TypedEqualityRenaming > /tmp/pts-rk-typed-renaming-kernel.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/TypedEqualityRenaming.vo > /tmp/pts-rk-typed-renaming-integrated.log 2>&1
```

Compilation exits 1,1,0; dependent-elimination names and implicit renamer
inference corrected. Final source comparison, recursive kernel check and
integrated Dune build all exited 0. Six closed reports. Kernel lists only
existing functional_extensionality_dep and no unsafe settings.

## Normal typing witnesses

All attempts compiled the repository source directly to a temporary output:

```sh
# Attempt 1, exit 0, but unqualified output library name:
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q ZFC_model PTSrkModel -o /tmp/pts-rk-canonical-types.4h21H9/CanonicalTypeWitnesses.vo ZFC_model/CanonicalTypeWitnesses.v > /tmp/pts-rk-canonical-type-witnesses-1.log 2>&1
# Attempts N=2,3,4, exits 0,1,0:
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q ZFC_model PTSrkModel -Q /tmp/pts-rk-canonical-types.4h21H9 PTSrkModel -o /tmp/pts-rk-canonical-types.4h21H9/CanonicalTypeWitnesses.vo ZFC_model/CanonicalTypeWitnesses.v > /tmp/pts-rk-canonical-type-witnesses-N.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-canonical-types.4h21H9 PTSrkModel PTSrkModel.CanonicalTypeWitnesses > /tmp/pts-rk-canonical-type-witnesses-kernel.log 2>&1
```

Attempt 2 repairs the output library namespace. Attempt 3 was an incomplete
normal-product proof using eauto; explicit elimination fixes it. Attempt 4
prints ten closed reports. Recursive kernel check exited 0. There was no
source-copy comparison in this isolated test because the compiler read
the repository source; the final fresh build comparisons below cover it.

## Canonical denotation

Attempt 1 (exit 1, helper library namespace mismatch):

```sh
cp ZFC_model/CanonicalDenotation.v /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalDenotation.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq compile -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-canonical-types.4h21H9 PTSrkModel -Q /tmp/pts-rk-canonical-denotation.fvg3US PTSrkModel /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalDenotation.v > /tmp/pts-rk-canonical-denotation-1.log 2>&1
```

Compile a correctly named helper in the same scratch directory (exit 0):

```sh
cp ZFC_model/CanonicalTypeWitnesses.v /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalTypeWitnesses.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq compile -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-canonical-denotation.fvg3US PTSrkModel /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalTypeWitnesses.v > /tmp/pts-rk-canonical-denotation-helper.log 2>&1
```

Attempts 2–3 copied each revised CanonicalDenotation source and ran:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq compile -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-canonical-denotation.fvg3US PTSrkModel /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalDenotation.v > /tmp/pts-rk-canonical-denotation-N.log 2>&1
```

Exits 1,124. Attempt 2 had a module/section name collision, fixed by fully
qualifying the original denotation. Attempt 3 hit the explicit 180-second
timeout and has an empty raw log. It is NOT a successful verification.
Before attempt 4 the final helper vo and source were copied to the same
scratch directory, and uncontrolled repeat split in set-valued inversion
proofs was replaced by explicit conjunction splitting. Attempts 4–5:

```sh
cp /tmp/pts-rk-canonical-types.4h21H9/CanonicalTypeWitnesses.vo /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalTypeWitnesses.vo
cp ZFC_model/CanonicalTypeWitnesses.v /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalTypeWitnesses.v
# Each attempt copied its revised CanonicalDenotation.v before compiling.
opam exec --switch=pts-rk-ci -- timeout 180 rocq compile -time -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-canonical-denotation.fvg3US PTSrkModel /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalDenotation.v > /tmp/pts-rk-canonical-denotation-N.log 2>&1
```

Attempt 4 exited 1 (extra destruct bracket); attempt 5 exited 0, three
closed reports. No theorem statement was weakened to resolve these failures.
Both final source comparisons and recursive kernel check exited 0:

```sh
cmp ZFC_model/CanonicalDenotation.v /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalDenotation.v
cmp ZFC_model/CanonicalTypeWitnesses.v /tmp/pts-rk-canonical-denotation.fvg3US/CanonicalTypeWitnesses.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/vendor/zfc ZFC -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/theories PTSrk -Q /tmp/pts-rk-semantic-foundation-fresh.EU65sO/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-canonical-denotation.fvg3US PTSrkModel PTSrkModel.CanonicalDenotation > /tmp/pts-rk-canonical-denotation-kernel.log 2>&1
```

## Final integrated and fresh verification

The isolated fresh directory was allocated by mktemp -d; expanded below.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CanonicalTypeWitnesses.vo ZFC_model/CanonicalDenotation.vo ZFC_model/TypedEqualityRenaming.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-canonical-coherence-integrated.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-canonical-coherence-fresh.KhkkaT --display=short --no-buffer ZFC_model/BoundedChoiceSequence.vo ZFC_model/BoundedModelData.vo ZFC_model/TypedEquality.vo ZFC_model/TypedEqualityRenaming.vo ZFC_model/CanonicalTypeWitnesses.vo ZFC_model/CanonicalDenotation.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-canonical-coherence-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/canonical-coherence-final" bash tools/check-local-ci.sh > /tmp/pts-rk-canonical-coherence-ci.log 2>&1
for model_module in BoundedChoiceSequence BoundedModelData TypedEquality TypedEqualityRenaming CanonicalTypeWitnesses CanonicalDenotation CardinalClassification; do
  cmp "ZFC_model/$model_module.v" "/tmp/pts-rk-canonical-coherence-fresh.KhkkaT/default/ZFC_model/$model_module.v" || exit "$?"
done
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-canonical-coherence-fresh.KhkkaT/default/vendor/zfc ZFC -Q /tmp/pts-rk-canonical-coherence-fresh.KhkkaT/default/theories PTSrk -Q /tmp/pts-rk-canonical-coherence-fresh.KhkkaT/default/ZFC_model PTSrkModel PTSrkModel.BoundedChoiceSequence PTSrkModel.BoundedModelData PTSrkModel.TypedEqualityRenaming PTSrkModel.CanonicalTypeWitnesses PTSrkModel.CanonicalDenotation PTSrkModel.RealizationInduction PTSrkModel.RootBeta > /tmp/pts-rk-canonical-coherence-kernel.log 2>&1
```

Integrated build, fresh build, all seven source comparisons and full CI
exited 0. All 153 stages passed, including pristine upstream. The fresh
build printed 412 closed reports (19 new: 6 weakening, 10 normal witnesses,
3 canonical denotation). Final combined kernel check exited 0: existing
functional_extensionality_dep only, no unsafe fixpoints, type-in-type or
assumed positivity. The earlier compiler timeout remains in the raw record;
none of the final verification commands timed out.

The central new theorem, printed by the fresh compiler, is:

```coq
CanonicalDenotation.coherent :
  forall (H s : Ens) (n : nat) (G : Ctx nat n)
    (rho : Fin n -> Ens) (t : Term nat n) (v : Ens),
  CanonicalDenotation.denotes H s n G rho t v ->
  forall v' : Ens,
    CanonicalDenotation.denotes H s n G rho t v' -> EQ v v'.
```

Its Print Assumptions report is closed. It is coherence of an AUXILIARY
relation, not totality or soundness for all original typings. Normalized
implicit type witnesses exist syntactically, but semantic normalization
after substitution and beta/type-conversion preservation remain open.
Unrestricted original denotes coherence/conversion and first-order BZC
certification remain unproved. The original PTS rules are unchanged.
