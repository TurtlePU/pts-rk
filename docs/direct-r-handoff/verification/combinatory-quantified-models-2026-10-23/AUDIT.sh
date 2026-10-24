#!/usr/bin/env bash
# Fresh focused audit: quantified finite constructors and native proof realization.
set -euo pipefail
MODEL_ROOT="$(git rev-parse --show-toplevel)"
cd "$MODEL_ROOT"
MODEL_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$MODEL_LOCAL/bin:$PATH"
export OPAMROOT="$MODEL_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
MODEL_LOG="$(mktemp -d "$MODEL_ROOT/_build/combinatory-quantified-models-audit.XXXXXX")"
MODEL_BUILD="$(mktemp -d /tmp/pts-rk-quantified-models.XXXXXX)"
MODEL_UPSTREAM="$(mktemp -d /tmp/pts-rk-quantified-pristine.XXXXXX)"
MODEL_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
MODEL_DIR=theories/CombinatoryLogic-rk
MODEL_MODULES=(Core Presentation FiniteBasis ProductCatalogue Hilbert
  ProductHilbert IdentityCatalogue ConstantCatalogue SubstitutionCatalogue
  CatalogueHilbert CatalogueEconomy ContextualHilbert ProductExposure
  ContextualSubstitution HilbertAbstraction CatalogueShapes HilbertReplay
  AffineDuplication QuantitativeNormalization FiniteNormalForms GroundHorn
  BCKW KnuthBounds ChurchFinite NativeCanonicity GroundHornConsistency
  FiniteHorn HilbertGrounding HilbertFiniteModels FiniteHornChurch
  FiniteModelBoundary FiniteUniversalHorn FiniteNativeModelBoundary
  FiniteAlgebraSearch FiniteOperationAlgebras FiniteModelRealization
  MM0FiniteSignature MM0FiniteAxioms MM0FiniteSearch MM0ProjectionModel
  FiniteModelSoundness MM0SyntaxSoundness MM0InternalSoundness)
MODEL_SOURCES=()
MODEL_ROOTS=()
for model_module in "${MODEL_MODULES[@]}"; do
  MODEL_SOURCES+=("$MODEL_DIR/$model_module.v")
  MODEL_ROOTS+=("PTSrk.Combinatory.$model_module")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' "$MODEL_LOG" "$MODEL_BUILD" "$MODEL_UPSTREAM" | tee "$MODEL_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$MODEL_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$MODEL_LOG/commands.txt"
  printf '\n' >> "$MODEL_LOG/commands.txt"
  set +e
  "$@" > "$MODEL_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$MODEL_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$MODEL_LOG/$label.log"; exit "$result"; fi
}
check_reports() {
  local expected actual
  expected="$(rg --no-filename '^Print Assumptions ' "${MODEL_SOURCES[@]}" | wc -l | tr -d ' ')"
  actual="$(rg -c '^Closed under the global context$' "$MODEL_LOG/fresh-build.log")"
  printf 'Modules: %s\nOwn reports: %s\nNew reports: %s\nAggregate closed reports: %s\n' "${#MODEL_MODULES[@]}" "$expected" "$((expected - 358))" "$actual"
  [[ "${#MODEL_MODULES[@]}" -eq 43 && "$expected" -gt 358 ]]
  # Ranks is the only imported module printing one extra report.
  [[ "$actual" -eq "$((expected + 1))" ]]
  if rg -n '^Axioms:|^Assumptions:' "$MODEL_LOG/fresh-build.log"; then return 1; fi
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${MODEL_SOURCES[@]}"; then return 1; fi
}
compare_inventory() {
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$MODEL_LOG/upstream-kernel.log")" -eq 1 ]]
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$MODEL_LOG/kernel.log")" -eq 1 ]]
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$MODEL_LOG/upstream-kernel.log" > "$MODEL_LOG/upstream-inventory.txt"
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$MODEL_LOG/kernel.log" > "$MODEL_LOG/inventory.txt"
  cmp "$MODEL_LOG/upstream-inventory.txt" "$MODEL_LOG/inventory.txt"
}
previous_sources() {
  # Registration adds modules; every preceding proof and equality source stays fixed.
  awk '$2 != "theories/CombinatoryLogic-rk/dune"' \
    docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23/audit-final/source-before.log |
    shasum -a 256 -c -
}
run head git rev-parse HEAD
run dune-version opam exec -- dune --version
run rocq-version opam exec -- rocq -v
run packages opam list --installed --columns=name,version
run source-before shasum -a 256 "${MODEL_SOURCES[@]}" "$MODEL_DIR/dune" theories/Interpretation_of_R/DirectREval.v "$MODEL_DIR/CombinatoryPTS-rk.mm0"
run upstream-archive git archive --output="$MODEL_LOG/upstream.tar" "$MODEL_BASE"
run upstream-extract tar -xf "$MODEL_LOG/upstream.tar" -C "$MODEL_UPSTREAM"
run upstream-build opam exec -- timeout 600 dune build --root "$MODEL_UPSTREAM" --display=short --no-buffer -j 2 theories/Ranks.vo
run upstream-kernel opam exec -- timeout 600 rocq check -silent -o -Q "$MODEL_UPSTREAM/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 900 dune build --build-dir "$MODEL_BUILD" --display=short --no-buffer -j 2 @theories/CombinatoryLogic-rk/audit
run closed-reports check_reports
run kernel opam exec -- timeout 900 rocq check -silent -o \
  -Q "$MODEL_BUILD/default/theories" PTSrk \
  -Q "$MODEL_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$MODEL_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$MODEL_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory "${MODEL_ROOTS[@]}"
run inventory-compare compare_inventory
run original-kernel-unchanged git diff --exit-code "$MODEL_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run previous-sources-unchanged previous_sources
run mm0-unchanged git diff --exit-code HEAD -- "$MODEL_DIR/CombinatoryPTS-rk.mm0"
run literal-axioms-crosscheck python3 docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/crosscheck-mm0.py
run agda-unchanged shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/agda-sources.sha256
run source-after shasum -a 256 "${MODEL_SOURCES[@]}" "$MODEL_DIR/dune" theories/Interpretation_of_R/DirectREval.v "$MODEL_DIR/CombinatoryPTS-rk.mm0"
run source-stable cmp "$MODEL_LOG/source-before.log" "$MODEL_LOG/source-after.log"
run safety-scan safety_scan
run whitespace git diff --check -- "$MODEL_DIR" \
  docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23 \
  docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md
printf 'PASS: fresh 43-module quantified-model audit. Logs: %s\n' "$MODEL_LOG"
