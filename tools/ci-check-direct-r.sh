#!/usr/bin/env bash
# Compile existing PTS-rk source, not a different PTS or an external model.
# Invoke from the repository root through: opam exec -- bash tools/ci-check-direct-r.sh
# This driver deliberately fails on the first unsuccessful stage. It does not
# turn admitted/unproved statements into theorems and is not a proof-completion test.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
[[ -f Interpretation_of_R/DirectRCheck.v && -f Interpretation_of_R/functional/DirectRTests.v ]] || {
  echo 'Install the restructured DirectR package before running this workflow.' >&2
  exit 2
}
for tool in dune rocq opam git tar timeout; do
  command -v "$tool" >/dev/null || { echo "Missing runner tool: $tool" >&2; exit 127; }
done
BASELINE_REF="${DIRECT_R_BASELINE_REF:-723cf2ec61c737ae82ba33d2e7db44f650122b0e}"
JOBS="${DIRECT_R_JOBS:-2}"
SECONDS_PER_STAGE="${DIRECT_R_STAGE_SECONDS:-1200}"
[[ "$JOBS" =~ ^[1-9][0-9]*$ && "$SECONDS_PER_STAGE" =~ ^[1-9][0-9]*$ ]] || {
  echo 'DIRECT_R_JOBS and DIRECT_R_STAGE_SECONDS must be positive integers.' >&2
  exit 2
}
LOG_DIR="${DIRECT_R_LOG_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/direct-r-ci-logs.XXXXXX")}"
mkdir -p "$LOG_DIR"
LOG_DIR="$(cd "$LOG_DIR" && pwd)"
BASELINE_DIR=''
CURRENT_STAGE='toolchain-inventory'
INTERRUPTED_BY=''
: > "$LOG_DIR/stages.tsv"
printf 'Stage\tResult\tExit code\n' > "$LOG_DIR/stages.tsv"
printf 'Diagnostic directory: %s\n' "$LOG_DIR"

finish() {
  local status=$?
  trap - EXIT
  set +e
  [[ ! -f "$ROOT/_build/log" ]] || cp "$ROOT/_build/log" "$LOG_DIR/direct-r-dune.log"
  if [[ -n "$BASELINE_DIR" && -f "$BASELINE_DIR/_build/log" ]]; then
    cp "$BASELINE_DIR/_build/log" "$LOG_DIR/upstream-dune.log"
  fi
  {
    printf 'Exit code: %s\nLast stage: %s\n' "$status" "$CURRENT_STAGE"
    if [[ -n "$INTERRUPTED_BY" ]]; then
      printf 'Interrupted by signal: %s\n' "$INTERRUPTED_BY"
    elif [[ "$status" -eq 143 || "$status" -eq 137 ]]; then
      printf 'A process was terminated by a signal; inspect the runner log.\n'
    elif [[ "$status" -eq 124 ]]; then
      printf 'The stage resource limit expired; this is not a compiler diagnostic.\n'
    fi
    printf '\nGreen means the supplied files compiled. It does NOT assert the missing\n'
    printf 'uniform GeneratorTotal/GeneratorSound or first-order soundness theorems.\n'
  } > "$LOG_DIR/result.txt"
  if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    {
      printf '## DirectR compiler run\n\n'
      printf '| Stage | Result | Exit code |\n|---|---|---|\n'
      tail -n +2 "$LOG_DIR/stages.tsv" | while IFS=$'\t' read -r stage result code; do
        printf '| %s | %s | %s |\n' "$stage" "$result" "$code"
      done
      printf '\nDriver exit code: `%s`. Last stage: `%s`.\n' "$status" "$CURRENT_STAGE"
      printf '\nA failed stage stops the sequence; later modules were not checked.\n'
      printf '\nDownload the **direct-r-logs** artifact for complete logs and toolchain versions.\n'
      printf '\n**Theorem 5 remains unfinished even if these builds succeed.**\n'
    } >> "$GITHUB_STEP_SUMMARY"
  fi
  # Do not erase the real failing code, even when log copying fails.
  exit "$status"
}
trap finish EXIT
# Preserve interruption evidence when the runner cancels the shell. SIGKILL or
# loss of the host cannot be trapped, and artifact upload is then not guaranteed.
interrupted() {
  INTERRUPTED_BY="$1"
  printf '%s\tINTERRUPTED\t%s\n' "$CURRENT_STAGE" "$2" >> "$LOG_DIR/stages.tsv"
  exit "$2"
}
trap 'interrupted TERM 143' TERM
trap 'interrupted INT 130' INT

{
  git rev-parse HEAD
  dune --version
  rocq -v
  ocamlc -version
  opam --version
  opam list --installed --columns=name,version
} 2>&1 | tee "$LOG_DIR/versions.log"
opam switch export "$LOG_DIR/opam-switch.export" \
  2>&1 | tee "$LOG_DIR/opam-switch-export.log"

stage() {
  local label="$1" work="$2"
  shift 2
  local command_status log_status
  local -a pipeline_status
  CURRENT_STAGE="$label"
  printf '\n=== %s ===\n' "$label"
  # The timeout is a diagnostic resource limit, not a proof of divergence.
  set +e
  (
    cd "$work"
    timeout --signal=TERM --kill-after=30s "$SECONDS_PER_STAGE" \
      dune build --display=short --no-buffer -j "$JOBS" "$@"
  ) 2>&1 | tee "$LOG_DIR/$label.log"
  pipeline_status=("${PIPESTATUS[@]}")
  set -e
  command_status="${pipeline_status[0]}"
  log_status="${pipeline_status[1]}"
  if [[ "$command_status" -eq 0 && "$log_status" -eq 0 ]]; then
    printf '%s\tPASS\t0\n' "$label" >> "$LOG_DIR/stages.tsv"
  else
    [[ "$command_status" -ne 0 ]] || command_status="$log_status"
    printf '%s\tFAIL\t%s\n' "$label" "$command_status" >> "$LOG_DIR/stages.tsv"
    printf '::error title=DirectR stage failed::%s failed (exit %s). See the diagnostic artifact.\n' \
      "$label" "$command_status"
    exit "$command_status"
  fi
}

# Build the ACTUAL unmodified upstream snapshot in a separate directory.
# A target in the patched working tree would not be an isolated baseline.
CURRENT_STAGE='prepare-pristine-upstream'
git cat-file -e "${BASELINE_REF}^{commit}"
BASELINE_DIR="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/direct-r-upstream.XXXXXX")"
git archive "$BASELINE_REF" | tar -x -C "$BASELINE_DIR"
printf '%s\n' "$BASELINE_REF" > "$LOG_DIR/upstream-commit.txt"
stage 01-upstream "$BASELINE_DIR" theories/Ranks.vo
stage 01-normalization-complexity "$ROOT" theories/NormalizationComplexity/Audit.vo

stage 02-kernel "$ROOT" Interpretation_of_R/DirectRKernel.vo
stage 02-common-codes "$ROOT" Interpretation_of_R/DirectRCommonCodes.vo
stage 03-evaluator "$ROOT" Interpretation_of_R/DirectREval.vo
stage 04-checker "$ROOT" Interpretation_of_R/DirectRCheck.vo
stage 05-codes "$ROOT" Interpretation_of_R/functional/DirectRCodes.vo
stage 06-symbolic "$ROOT" Interpretation_of_R/DirectRSymbolic.vo
stage 06a-structural "$ROOT" Interpretation_of_R/DirectRStructural.vo
stage 06a-negative-logic "$ROOT" Interpretation_of_R/DirectRLogic.vo
stage 06a-finite-tables "$ROOT" Interpretation_of_R/DirectRFiniteTables.vo
stage 06a-positive-telescopes "$ROOT" Interpretation_of_R/DirectRPositive.vo
stage 06a-finite-observations "$ROOT" Interpretation_of_R/DirectRFiniteObservations.vo
stage 06a-binary-tables "$ROOT" Interpretation_of_R/DirectRBinaryTables.vo
stage 06a-binary-observations "$ROOT" Interpretation_of_R/DirectRBinaryObservations.vo
stage 06a-relation-tables "$ROOT" Interpretation_of_R/DirectRRelationTables.vo
stage 06a-finite-law-elimination "$ROOT" Interpretation_of_R/DirectRFiniteLawElimination.vo
stage 06a-functional-finite-laws "$ROOT" Interpretation_of_R/functional/DirectRFunctionalFiniteLaws.vo
stage 06a-guarded-finite-laws "$ROOT" Interpretation_of_R/DirectRGuardedFiniteLaws.vo
stage 06a-finite-transitivity "$ROOT" Interpretation_of_R/functional/DirectRFiniteTransitivity.vo
stage 06a-finite-congruence "$ROOT" Interpretation_of_R/functional/DirectRFiniteCongruence.vo
stage 06a-finite-unary-congruence "$ROOT" Interpretation_of_R/functional/DirectRFiniteUnaryCongruence.vo
stage 06a-finite-binary-congruence "$ROOT" Interpretation_of_R/functional/DirectRFiniteBinaryCongruence.vo
stage 06a-finite-zero-laws "$ROOT" Interpretation_of_R/functional/DirectRFiniteZeroLaws.vo
stage 06a-finite-expressions "$ROOT" Interpretation_of_R/functional/DirectRFiniteExpressions.vo
stage 06a-finite-recursion-laws "$ROOT" Interpretation_of_R/functional/DirectRFiniteRecursionLaws.vo
stage 06a-finite-order-laws "$ROOT" Interpretation_of_R/functional/DirectRFiniteOrderLaws.vo
stage 06a-telescope-arguments "$ROOT" Interpretation_of_R/DirectRTelescopeArguments.vo
stage 06a-finite-data "$ROOT" Interpretation_of_R/functional/DirectRFiniteData.vo
stage 06a-finite-binary-domain "$ROOT" Interpretation_of_R/functional/DirectRFiniteBinaryDomain.vo
stage 06a-finite-domain-prefix "$ROOT" Interpretation_of_R/functional/DirectRFiniteDomainPrefix.vo
stage 06a-finite-specialization "$ROOT" Interpretation_of_R/functional/DirectRFiniteSpecialization.vo
stage 06a-functional-evaluation "$ROOT" Interpretation_of_R/functional/DirectRFunctionalEvaluation.vo
stage 06a-functional-separation "$ROOT" Interpretation_of_R/functional/DirectRFunctionalSeparation.vo
stage 06a-functional-bounded "$ROOT" Interpretation_of_R/functional/DirectRFunctionalBounded.vo
stage 06a-functional-addition "$ROOT" Interpretation_of_R/functional/DirectRFunctionalAddition.vo
stage 06a-functional-multiplication "$ROOT" Interpretation_of_R/functional/DirectRFunctionalMultiplication.vo
stage 06a-functional-cases "$ROOT" Interpretation_of_R/functional/DirectRFunctionalCases.vo
stage 06a-functional-axioms "$ROOT" Interpretation_of_R/functional/DirectRFunctionalAxioms.vo
stage 06b-foundations "$ROOT" Interpretation_of_R/functional/DirectRFoundations.vo
stage 06c-unary "$ROOT" Interpretation_of_R/relational/DirectRUnary.vo
stage 06c-finite-up "$ROOT" Interpretation_of_R/DirectRFiniteUp.vo
stage 06c-finite-certificates "$ROOT" Interpretation_of_R/DirectRFiniteCertificates.vo
stage 06c-iterations "$ROOT" Interpretation_of_R/DirectRIterations.vo
stage 06c-unary-evaluation "$ROOT" Interpretation_of_R/relational/DirectRUnaryEvaluation.vo
stage 06c-separation "$ROOT" Interpretation_of_R/relational/DirectRSeparation.vo
stage 06c-unary-axioms "$ROOT" Interpretation_of_R/relational/DirectRUnaryAxioms.vo
stage 06c-unary-bounded "$ROOT" Interpretation_of_R/relational/DirectRUnaryBounded.vo
stage 06c-unary-arithmetic "$ROOT" Interpretation_of_R/relational/DirectRUnaryArithmetic.vo
stage 06c-unary-assumptions "$ROOT" Interpretation_of_R/relational/DirectRUnaryAudit.vo
stage 06c-relational-syntax "$ROOT" Interpretation_of_R/relational/DirectRRelationalSyntax.vo
stage 06c-relational-translation "$ROOT" Interpretation_of_R/relational/DirectRRelationalTranslation.vo
stage 06c-relational-equality "$ROOT" Interpretation_of_R/relational/DirectRRelationalEquality.vo
stage 06c-relational-deduction "$ROOT" Interpretation_of_R/relational/DirectRRelationalDeduction.vo
stage 06c-relational-countermodel "$ROOT" Interpretation_of_R/relational/DirectRRelationalCountermodel.vo
stage 06c-relational-ground "$ROOT" Interpretation_of_R/relational/DirectRRelationalGround.vo
stage 06c-relational-axioms "$ROOT" Interpretation_of_R/relational/DirectRRelationalAxioms.vo
stage 06c-theorem4 "$ROOT" Interpretation_of_R/relational/DirectRTheorem4.vo
stage 06c-relational-audit "$ROOT" Interpretation_of_R/relational/DirectRRelationalAudit.vo
stage 06d-source-countermodel "$ROOT" Interpretation_of_R/DirectRCountermodel.vo
stage 06e-set-functions "$ROOT" ZFC_model/SetFunctions.vo
stage 06f-set-application "$ROOT" ZFC_model/SetApplication.vo
stage 06g-code-universes "$ROOT" ZFC_model/CodeUniverses.vo
stage 06h-set-bijections "$ROOT" ZFC_model/SetBijections.vo
stage 06i-coded-functions "$ROOT" ZFC_model/CodedFunctions.vo
stage 06j-product-embedding "$ROOT" ZFC_model/ProductEmbedding.vo
stage 06k-countable-codes "$ROOT" ZFC_model/CountableCodes.vo
stage 06l-cardinal-growth "$ROOT" ZFC_model/CardinalGrowth.vo
stage 06m-cardinal-hierarchy "$ROOT" ZFC_model/CardinalHierarchy.vo
stage 06n-powerset-embedding "$ROOT" ZFC_model/PowersetEmbedding.vo
stage 06o-subset-functions "$ROOT" ZFC_model/SubsetFunctions.vo
stage 06p-bounded-formulas "$ROOT" ZFC_model/BoundedFormulas.vo
stage 06pa-bounded-application "$ROOT" ZFC_model/BoundedApplication.vo
stage 06q-bounded-inverse "$ROOT" ZFC_model/BoundedInverse.vo
stage 06r-hierarchy-bounds "$ROOT" ZFC_model/HierarchyBounds.vo
stage 06s-bounded-families "$ROOT" ZFC_model/BoundedFamilies.vo
stage 06t-bounded-products "$ROOT" ZFC_model/BoundedProducts.vo
stage 06u-code-hierarchy "$ROOT" ZFC_model/CodeHierarchyBounds.vo
stage 06v-supplied-hierarchy "$ROOT" ZFC_model/SuppliedHierarchy.vo
stage 06w-bounded-bijections "$ROOT" ZFC_model/BoundedBijections.vo
stage 06x-countable-pairing "$ROOT" ZFC_model/CountablePairing.vo
stage 06y-cartesian-maps "$ROOT" ZFC_model/CartesianMaps.vo
stage 06z-powerset-squares "$ROOT" ZFC_model/PowersetSquares.vo
stage 06za-cantor-bernstein "$ROOT" ZFC_model/CantorBernstein.vo
stage 06zb-bounded-comparison "$ROOT" ZFC_model/BoundedComparison.vo
stage 06zd-finite-classification "$ROOT" ZFC_model/FiniteClassification.vo
stage 06ze-countable-dichotomy "$ROOT" ZFC_model/CountableDichotomy.vo
stage 06zbc-bounded-choice-sequence "$ROOT" ZFC_model/BoundedChoiceSequence.vo
stage 06zc-cardinal-classification "$ROOT" ZFC_model/CardinalClassification.vo
stage 06zf-product-witnesses "$ROOT" ZFC_model/ProductWitnesses.vo
stage 06zg-code-witnesses "$ROOT" ZFC_model/CodeWitnesses.vo
stage 06zh-product-extensionality "$ROOT" ZFC_model/ProductExtensionality.vo
stage 06zi-selected-codes "$ROOT" ZFC_model/SelectedCodes.vo
stage 06zj-global-code-choice "$ROOT" ZFC_model/GlobalCodeChoice.vo
stage 06zk-global-operations "$ROOT" ZFC_model/GlobalOperations.vo
stage 06zl-syntax-renaming "$ROOT" ZFC_model/SyntaxRenaming.vo
stage 06zm-syntax-substitution "$ROOT" ZFC_model/SyntaxSubstitution.vo
stage 06zn-denotation "$ROOT" ZFC_model/Denotation.vo
stage 06zo-denotation-beta "$ROOT" ZFC_model/DenotationBeta.vo
stage 06zp-interpreted-contexts "$ROOT" ZFC_model/InterpretedContexts.vo
stage 06zq-rule-realization "$ROOT" ZFC_model/RuleRealization.vo
stage 06zr-bounded-formula-transport "$ROOT" ZFC_model/BoundedFormulaTransport.vo
stage 06zr0-material-set-theory "$ROOT" ZFC_model/MaterialSetTheory.vo
stage 06zr1-material-zermelo "$ROOT" ZFC_model/MaterialZermelo.vo
stage 06zra-bounded-graphs "$ROOT" ZFC_model/BoundedGraphs.vo
stage 06zrb-bounded-finite-carriers "$ROOT" ZFC_model/BoundedFiniteCarriers.vo
stage 06zrc-bounded-powersets "$ROOT" ZFC_model/BoundedPowersets.vo
stage 06zrd-bounded-iteration "$ROOT" ZFC_model/BoundedIteration.vo
stage 06zre-bounded-recursion "$ROOT" ZFC_model/BoundedRecursion.vo
stage 06zrf-bounded-code-arithmetic "$ROOT" ZFC_model/BoundedCodeArithmetic.vo
stage 06zrg-bounded-infinite-decoder "$ROOT" ZFC_model/BoundedInfiniteDecoder.vo
stage 06zrh-bounded-universes "$ROOT" ZFC_model/BoundedUniverses.vo
stage 06zri-bounded-sort-decoder "$ROOT" ZFC_model/BoundedSortDecoder.vo
stage 06zrj-bounded-decoder "$ROOT" ZFC_model/BoundedDecoder.vo
stage 06zs-bounded-choice "$ROOT" ZFC_model/BoundedChoice.vo
stage 06zsa-bounded-formula-selection "$ROOT" ZFC_model/BoundedFormulaSelection.vo
stage 06zsb-bounded-code-selection "$ROOT" ZFC_model/BoundedCodeSelection.vo
stage 06zsc-bounded-decoded-selection "$ROOT" ZFC_model/BoundedDecodedSelection.vo
stage 06zsd-bounded-model-data "$ROOT" ZFC_model/BoundedModelData.vo
stage 06zt-denotation-choice "$ROOT" ZFC_model/DenotationChoice.vo
stage 06zu-paired-choice "$ROOT" ZFC_model/PairedChoice.vo
stage 06zv-lambda-realization "$ROOT" ZFC_model/LambdaRealization.vo
stage 06zw-denotation-inversion "$ROOT" ZFC_model/DenotationInversion.vo
stage 06zx-application-realization "$ROOT" ZFC_model/ApplicationRealization.vo
stage 06zy-context-transport "$ROOT" ZFC_model/ContextTransport.vo
stage 06zz-denotation-congruence "$ROOT" ZFC_model/DenotationCongruence.vo
stage 06zza-beta-witness-transport "$ROOT" ZFC_model/BetaWitnessTransport.vo
stage 06zzb-type-head-normalization "$ROOT" ZFC_model/TypeHeadNormalization.vo
stage 06zzba-canonical-type-witnesses "$ROOT" ZFC_model/CanonicalTypeWitnesses.vo
stage 06zzbb-canonical-denotation "$ROOT" ZFC_model/CanonicalDenotation.vo
stage 06zzbc-canonical-renaming "$ROOT" ZFC_model/CanonicalRenaming.vo
stage 06zzbd-canonical-realization "$ROOT" ZFC_model/CanonicalRealization.vo
stage 06zzbe-canonical-substitution "$ROOT" ZFC_model/CanonicalSubstitution.vo
stage 06zzbf-canonical-root-beta "$ROOT" ZFC_model/CanonicalRootBeta.vo
stage 06zzbg-canonical-context "$ROOT" ZFC_model/CanonicalContext.vo
stage 06zzbh-canonical-application "$ROOT" ZFC_model/CanonicalApplication.vo
stage 06zzbi-canonical-hereditary "$ROOT" ZFC_model/CanonicalHereditary.vo
stage 06zzbj-canonical-valuation-transport "$ROOT" ZFC_model/CanonicalValuationTransport.vo
stage 06zzbk-neutral-cut-rank "$ROOT" ZFC_model/NeutralCutRank.vo
stage 06zzbl-ranked-denotation "$ROOT" ZFC_model/RankedDenotation.vo
stage 06zzbm-ranked-transport "$ROOT" ZFC_model/RankedTransport.vo
stage 06zzbn-ranked-substitution "$ROOT" ZFC_model/RankedSubstitution.vo
stage 06zzbo-ranked-root-beta "$ROOT" ZFC_model/RankedRootBeta.vo
stage 06zzbp-ranked-hereditary "$ROOT" ZFC_model/RankedHereditary.vo
stage 06zzbq-ranked-normalization "$ROOT" ZFC_model/RankedNormalization.vo
stage 06zzbr-model-soundness "$ROOT" ZFC_model/ModelSoundness.vo
stage 06zzc-root-beta "$ROOT" ZFC_model/RootBeta.vo
stage 06zzd-regular-typing "$ROOT" ZFC_model/RegularTyping.vo
stage 06zzda-typed-equality "$ROOT" ZFC_model/TypedEquality.vo
stage 06zzdb-typed-equality-renaming "$ROOT" ZFC_model/TypedEqualityRenaming.vo
stage 06zze-realization-induction "$ROOT" ZFC_model/RealizationInduction.vo
stage 07-proof-families "$ROOT" Interpretation_of_R/functional/DirectRProofs.vo
stage 08-generators "$ROOT" Interpretation_of_R/functional/DirectRGenerated.vo
stage 09-first-order "$ROOT" Interpretation_of_R/functional/DirectRFirstOrder.vo
stage 09a-functional-terms "$ROOT" Interpretation_of_R/functional/DirectRFunctionalTerms.vo
stage 09a-functional-logic "$ROOT" Interpretation_of_R/functional/DirectRFunctionalLogic.vo
stage 09b-functional-syntax "$ROOT" Interpretation_of_R/functional/DirectRFunctionalSyntax.vo
stage 09b-functional-translation "$ROOT" Interpretation_of_R/functional/DirectRFunctionalTranslation.vo
stage 09b-functional-formula-logic "$ROOT" Interpretation_of_R/functional/DirectRFunctionalFormulaLogic.vo
stage 09b-functional-source-axioms "$ROOT" Interpretation_of_R/functional/DirectRFunctionalSourceAxioms.vo
stage 09c-functional-equality "$ROOT" Interpretation_of_R/functional/DirectRFunctionalEquality.vo
stage 09c-functional-deduction "$ROOT" Interpretation_of_R/functional/DirectRFunctionalDeduction.vo
stage 09d-derivation-certificates "$ROOT" Interpretation_of_R/DirectRDerivationCertificates.vo
stage 09d-witness-search "$ROOT" Interpretation_of_R/DirectRWitnessSearch.vo
stage 09d-functional-countermodel "$ROOT" Interpretation_of_R/functional/DirectRFunctionalCountermodel.vo
stage 09d-theorem7 "$ROOT" Interpretation_of_R/functional/DirectRTheorem7.vo
stage 09a-functional-audit "$ROOT" Interpretation_of_R/functional/DirectRFunctionalAudit.vo
stage 10-obligations "$ROOT" Interpretation_of_R/functional/DirectRObligations.vo
stage 11-entry-point "$ROOT" Interpretation_of_R/functional/DirectR.vo
stage 12-arithmetic "$ROOT" Interpretation_of_R/functional/DirectRArithmetic.vo
# On a fresh checkout this compilation also emits the file's Print Assumptions.
stage 13-examples-and-assumptions "$ROOT" Interpretation_of_R/functional/DirectRTests.vo
CURRENT_STAGE='complete'
printf '\nAll requested builds passed; inspect the assumption report.\n'
printf 'Theorem 7 and its effective target are audited; legacy bounded-generator contracts remain separate.\n'
