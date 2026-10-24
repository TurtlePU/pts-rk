#!/usr/bin/env bash
# Compile the note with the repository's LaTeX-Markdown runtime.
set -euo pipefail
note_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_dir=$(cd "$note_dir/../.." && pwd)
build_dir=$(mktemp -d /tmp/pts-rk-combinatory-note.XXXXXX)
printf 'Build directory: %s\n' "$build_dir"
ln -s "$note_dir/CombinatoryPTS-rk.tex" "$build_dir/CombinatoryPTS-rk.tex"
test -f "$note_dir/CombinatoryPTS-rk.mm0"
for marker in BEGINHILBERT ENDHILBERT; do
  if [[ $(rg -c "^-- $marker\$" "$note_dir/CombinatoryPTS-rk.mm0") != 1 ]]; then
    printf 'Expected exactly one MM0 excerpt marker: %s\n' "$marker" >&2
    exit 1
  fi
done
ln -s "$note_dir/CombinatoryPTS-rk.mm0" "$build_dir/CombinatoryPTS-rk.mm0"
extract_agda() {
  local source=$1 marker=$2 output=$3
  for boundary in BEGIN END; do
    if [[ $(rg -c "^[[:space:]]*-- ${boundary}${marker}\$" "$source") != 1 ]]; then
      printf 'Missing or repeated Agda excerpt marker: %s%s\n' "$boundary" "$marker" >&2
      exit 1
    fi
  done
  awk -v start="-- BEGIN$marker" -v stop="-- END$marker" '
    { markerLine=$0; sub(/^[[:space:]]*/, "", markerLine) }
    markerLine == start { printing=1; next }
    markerLine == stop { printing=0; next }
    printing { print }
  ' "$source" > "$build_dir/$output.agda"
  test -s "$build_dir/$output.agda"
}
extract_agda "$note_dir/agda/Combinatory.agda" HEADSIGNATURE agda-signature
extract_agda "$note_dir/agda/Combinatory.agda" APPSIGNATURE agda-application
extract_agda "$note_dir/agda/BinderFreeCore.agda" BINDERFREEAPPLY agda-binderfree-apply
extract_agda "$note_dir/agda/BinderFreeQuotient.agda" BINDERFREEQUOTIENT agda-binderfree-quotient
extract_agda "$note_dir/agda/SKCanonical.agda" SKCANONICAL agda-sk-canonical
extract_agda "$note_dir/agda/SKCanonical.agda" SKCANONICALAPPLY agda-sk-canonical-apply
extract_agda "$note_dir/agda/SKDirectGround.agda" SKDIRECTGROUND agda-sk-direct-ground
extract_agda "$note_dir/agda/CanonicalAlgebra.agda" CANONICALALGEBRA agda-canonical-algebra
extract_agda "$note_dir/agda/NormalizedSubstitution.agda" NORMALSUBCARRIER agda-normal-sub-carrier
extract_agda "$note_dir/agda/NormalizedFamilies.agda" NORMALFAMILIES agda-normal-families
extract_agda "$note_dir/agda/NormalizedContexts.agda" NORMALCONTEXTS agda-normal-contexts
extract_agda "$note_dir/agda/NormalizedProducts.agda" NORMALAPPLICATION agda-normal-application
extract_agda "$note_dir/agda/NativeBidirectional.agda" NATIVEINFERENCE agda-native-inference
extract_agda "$note_dir/agda/Exact.agda" EXACT agda-exact
extract_agda "$note_dir/agda/NormalForms.agda" NORMALIIR agda-normal-iir
extract_agda "$note_dir/agda/NormalForms.agda" NORMALFAMILY agda-normal-family
extract_agda "$note_dir/agda/TypedNormalFibres.agda" TYPEDNORMALFIBRE agda-typed-normal
extract_agda "$note_dir/agda/FiniteApplication.agda" FINITEAPPLICATIONTYPE agda-finite-result
extract_agda "$note_dir/agda/FiniteTrace.agda" FINITEWALK agda-finite-walk
extract_agda "$note_dir/agda/TypedApplication.agda" TYPEDAPPLICATION agda-typed-apply
extract_agda "$note_dir/agda/ChurchFinite.agda" CHURCHMACHINE agda-church-machine
extract_agda "$note_dir/agda/FragmentModelSoundness.agda" " FRAGMENTMODELINPUT" agda-model-input
extract_agda "$note_dir/agda/FragmentModelSoundness.agda" " FRAGMENTMODELSOUNDNESS" agda-model-soundness
shasum -a 256 "$note_dir"/agda/*.agda > "$build_dir/agda-source-sha256.txt"
ln -s "$note_dir/combinatory-preamble.tex" "$build_dir/combinatory-preamble.tex"
ln -s "$project_dir/latex/tex/development-preamble.tex" "$build_dir/development-preamble.tex"
for input in markdown.cls markdown.sty markdown verified-badges.sty badges; do
  ln -s "$project_dir/latex/$input" "$build_dir/$input"
done
for proof in Core.v Presentation.v FiniteBasis.v Hilbert.v ProductCatalogue.v \
  IdentityCatalogue.v ConstantCatalogue.v SubstitutionCatalogue.v CatalogueHilbert.v \
  CatalogueEconomy.v CatalogueShapes.v ContextualHilbert.v ContextualSubstitution.v \
  ProductExposure.v HilbertAbstraction.v HilbertReplay.v \
  QuantitativeNormalization.v FiniteNormalForms.v GroundHorn.v SK.v KnuthBounds.v \
  ChurchFinite.v GroundHornConsistency.v FiniteHorn.v HilbertGrounding.v \
  FiniteModelBoundary.v NativeCanonicity.v FiniteHornChurch.v \
  HilbertFiniteModels.v FiniteUniversalHorn.v FiniteNativeModelBoundary.v \
  FiniteAlgebraSearch.v FiniteOperationAlgebras.v FiniteModelRealization.v \
  MM0FiniteSignature.v MM0FiniteAxioms.v MM0FiniteSearch.v MM0ProjectionModel.v \
  FiniteModelSoundness.v MM0SyntaxSoundness.v MM0InternalSoundness.v \
  GuardedFiniteCarriers.v GuardedHornFragments.v GuardedHilbertModels.v \
  MM0GuardedQuantification.v GuardedBetaGraphs.v GuardedHilbertTables.v \
  GuardedHilbertCoverage.v MM0NativeSyntax.v MM0ComputationalAdequacy.v \
  MM0NativeReduction.v MM0CatalogueAdequacy.v MM0CatalogueRealization.v \
  MM0GuardedSyntaxAlgebra.v MM0GuardedReflection.v MM0HilbertAdequacy.v \
  HornProofEncoding.v HornProofRealization.v GuardedFiniteSupport.v \
  HornInternalSoundness.v MM0GuardedInternalReflection.v \
  FiniteTypeDispatch.v IndexedHornEncoding.v IndexedHornRealization.v \
  MM0GuardProvenance.v IndexedHornSoundness.v MM0IndexedReflection.v \
  IndexedHornTransport.v FiniteGeneratedCodes.v FiniteMapCoherence.v \
  MM0InternalDecoder.v MM0InternalGuard.v; do
  test -f "$note_dir/$proof"
done
cd "$build_dir"
printf '%s\n' 'latexmk -lualatex -interaction=nonstopmode -halt-on-error CombinatoryPTS-rk.tex' > command.txt
date -u '+%Y-%m-%d %H:%M:%S UTC' > started.txt
latexmk -v > versions.log
lualatex --version >> versions.log
latexminted --version >> versions.log
shasum -a 256 CombinatoryPTS-rk.mm0 > mm0-source-sha256.txt
if latexmk -lualatex -interaction=nonstopmode -halt-on-error CombinatoryPTS-rk.tex > build.log 2>&1; then
  printf '0\n' > build-exit-code.txt
else
  status=$?
  printf '%s\n' "$status" > build-exit-code.txt
  tail -60 build.log
  exit "$status"
fi
if rg 'LaTeX Warning: (Reference|There were undefined)|Missing character:|Overfull \\[hv]box|Package minted (Error|Warning)' CombinatoryPTS-rk.log; then
  printf 'Validation failed; existing PDF retained.\n' >&2
  printf '1\n' > validation-exit-code.txt
  exit 1
else
  status=$?
  if [[ "$status" != 1 ]]; then exit "$status"; fi
fi
# Verify that Pygments produced highlighted output, not a verbatim fallback.
if ! rg -l --glob '*.highlight.minted' '\\PYG' _minted* > pygments-output.txt; then
  printf 'Missing Pygments highlighting; existing PDF retained.\n' >&2
  printf '1\n' > validation-exit-code.txt
  exit 1
fi
printf '0\n' > validation-exit-code.txt
date -u '+%Y-%m-%d %H:%M:%S UTC' > finished.txt
cp CombinatoryPTS-rk.pdf "$note_dir/CombinatoryPTS-rk.pdf"
printf 'Build and validation exit code: 0\nPDF: %s\n' "$note_dir/CombinatoryPTS-rk.pdf"
