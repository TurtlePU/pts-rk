#!/usr/bin/env bash
# Fresh focused audit: literal MM0/native adequacy and guarded model existence.
set -euo pipefail
MODEL_ROOT="$(git rev-parse --show-toplevel)"
cd "$MODEL_ROOT"
MODEL_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$MODEL_LOCAL/bin:$PATH"
export OPAMROOT="$MODEL_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
MODEL_LOG="$(mktemp -d "$MODEL_ROOT/_build/combinatory-mm0-bridge-audit.XXXXXX")"
MODEL_BUILD="$(mktemp -d /tmp/pts-rk-mm0-bridge.XXXXXX)"
MODEL_UPSTREAM="$(mktemp -d /tmp/pts-rk-mm0-bridge-pristine.XXXXXX)"
MODEL_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
MODEL_DIR=theories/CombinatoryLogic-rk
MODEL_EVIDENCE=docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23
MODEL_ARCHIVE="$(mktemp -d "$MODEL_ROOT/$MODEL_EVIDENCE/audit.XXXXXX")"
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
  FiniteModelSoundness MM0SyntaxSoundness MM0InternalSoundness
  GuardedFiniteCarriers GuardedHornFragments MM0GuardedQuantification
  GuardedHilbertModels GuardedBetaGraphs GuardedHilbertTables
  GuardedHilbertCoverage MM0NativeSyntax MM0ComputationalAdequacy
  MM0NativeReduction MM0CatalogueAdequacy MM0CatalogueRealization
  MM0GuardedSyntaxAlgebra MM0GuardedReflection MM0HilbertAdequacy)
MODEL_SOURCES=()
MODEL_ROOTS=()
for model_module in "${MODEL_MODULES[@]}"; do
  MODEL_SOURCES+=("$MODEL_DIR/$model_module.v")
  MODEL_ROOTS+=("PTSrk.Combinatory.$model_module")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' "$MODEL_LOG" "$MODEL_BUILD" "$MODEL_UPSTREAM" | tee "$MODEL_LOG/paths.txt"
printf 'Archive: %s\n' "$MODEL_ARCHIVE" | tee -a "$MODEL_LOG/paths.txt"
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
  printf 'Modules: %s\nOwn reports: %s\nNew reports: %s\nAggregate closed reports: %s\n' "${#MODEL_MODULES[@]}" "$expected" "$((expected - 693))" "$actual"
  [[ "${#MODEL_MODULES[@]}" -eq 58 && "$expected" -eq 885 ]] || return 1
  # Ranks is the only imported module printing one extra report.
  [[ "$actual" -eq 886 && "$actual" -eq "$((expected + 1))" ]] || return 1
  if rg -n '^Axioms:|^Assumptions:' "$MODEL_LOG/fresh-build.log"; then return 1; fi
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${MODEL_SOURCES[@]}"; then return 1; fi
}
compare_inventory() {
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$MODEL_LOG/upstream-kernel.log")" -eq 1 ]] || return 1
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$MODEL_LOG/kernel.log")" -eq 1 ]] || return 1
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$MODEL_LOG/upstream-kernel.log" > "$MODEL_LOG/upstream-inventory.txt" || return 1
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$MODEL_LOG/kernel.log" > "$MODEL_LOG/inventory.txt" || return 1
  cmp "$MODEL_LOG/upstream-inventory.txt" "$MODEL_LOG/inventory.txt"
}
previous_sources() {
  # Registration adds modules; every preceding proof and equality source stays fixed.
  awk '$2 != "theories/CombinatoryLogic-rk/dune"' \
    docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/audit-02/source-before.log |
    shasum -a 256 -c -
}
registration_only() {
  # Remove precisely the eight new module names and eight alias entries.
  # All other bytes must have the previous registration file's hash.
  local expected actual
  expected="$(awk '$2 == "theories/CombinatoryLogic-rk/dune" {print $1}' \
    docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/audit-02/source-before.log)"
  actual="$(perl -0777 -pe '
    s/GuardedHilbertCoverage MM0NativeSyntax MM0ComputationalAdequacy\n   MM0NativeReduction MM0CatalogueAdequacy MM0CatalogueRealization\n   MM0GuardedSyntaxAlgebra MM0GuardedReflection MM0HilbertAdequacy/GuardedHilbertCoverage/g;
    s/GuardedHilbertCoverage\.vo MM0NativeSyntax\.vo MM0ComputationalAdequacy\.vo\n   MM0NativeReduction\.vo MM0CatalogueAdequacy\.vo MM0CatalogueRealization\.vo\n   MM0GuardedSyntaxAlgebra\.vo MM0GuardedReflection\.vo MM0HilbertAdequacy\.vo/GuardedHilbertCoverage.vo/g;
    ' "$MODEL_DIR/dune" | shasum -a 256 | awk '{print $1}')"
  printf 'Previous Dune: %s\nNormalized current Dune: %s\n' "$expected" "$actual"
  [[ -n "$expected" && "$expected" == "$actual" ]]
}
archive_logs() {
  local source target
  for source in "$MODEL_LOG"/*.log "$MODEL_LOG"/*.txt "$MODEL_LOG"/*.tsv; do
    [[ -f "$source" ]] || continue
    target="$MODEL_ARCHIVE/$(basename "$source")"
    gzip -c "$source" > "$target.raw.gz" || return 1
    cp "$source" "$target" || return 1
    perl -0pi -e 's/[ \t]+$//mg; s/\n+\z/\n/' "$target" || return 1
  done
}
check_new_file_whitespace() {
  local source="$1" diagnostic result
  [[ -f "$source" ]] || { printf 'Missing whitespace target: %s\n' "$source"; return 1; }
  # --no-index implies --exit-code: a clean new-file diff returns 1.
  # Whitespace has status 3 here; reject EVERY diagnostic as well, so an
  # unexpected file/access error cannot be mistaken for a clean diff.
  if diagnostic="$(git diff --no-index --check /dev/null "$source" 2>&1)"; then
    result=0
  else
    result=$?
  fi
  if [[ "$result" -gt 1 || -n "$diagnostic" ]]; then
    printf '%s\n' "$diagnostic"
    return 1
  fi
  return 0
}
audit_whitespace() {
  local source
  git diff --check -- "$MODEL_DIR" "$MODEL_EVIDENCE" \
    docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md || return 1
  # --no-index also checks new, deliberately UNSTAGED proof/evidence files.
  for source in "${MODEL_SOURCES[@]}" "$MODEL_DIR/dune" "$MODEL_EVIDENCE/AUDIT.sh" \
    "$MODEL_ARCHIVE"/*.log "$MODEL_ARCHIVE"/*.txt "$MODEL_ARCHIVE"/*.tsv; do
    [[ -f "$source" ]] || continue
    check_new_file_whitespace "$source" || return 1
  done
}
trap 'model_result=$?; archive_logs || model_result=$?; exit "$model_result"' EXIT
run audit-driver shasum -a 256 "$MODEL_EVIDENCE/AUDIT.sh"
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
run registration-only registration_only
run mm0-unchanged git diff --exit-code HEAD -- "$MODEL_DIR/CombinatoryPTS-rk.mm0"
run literal-axioms-crosscheck python3 docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/crosscheck-mm0.py
run agda-unchanged shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/agda-sources.sha256
run source-after shasum -a 256 "${MODEL_SOURCES[@]}" "$MODEL_DIR/dune" theories/Interpretation_of_R/DirectREval.v "$MODEL_DIR/CombinatoryPTS-rk.mm0"
run source-stable cmp "$MODEL_LOG/source-before.log" "$MODEL_LOG/source-after.log"
run safety-scan safety_scan
archive_logs
run whitespace audit_whitespace
printf 'PASS: fresh 58-module MM0/native bridge audit. Logs: %s\n' "$MODEL_LOG"
