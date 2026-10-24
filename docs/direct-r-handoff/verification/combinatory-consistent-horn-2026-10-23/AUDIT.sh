#!/usr/bin/env bash
# Fresh focused audit of the consistent grounded-Horn extension.
set -euo pipefail
HORN_ROOT="$(git rev-parse --show-toplevel)"
cd "$HORN_ROOT"
HORN_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$HORN_LOCAL/bin:$PATH"
export OPAMROOT="$HORN_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
HORN_LOG="$(mktemp -d "$HORN_ROOT/_build/combinatory-consistent-horn-audit.XXXXXX")"
HORN_BUILD="$(mktemp -d /tmp/pts-rk-consistent-horn.XXXXXX)"
HORN_UPSTREAM="$(mktemp -d /tmp/pts-rk-consistent-horn-pristine.XXXXXX)"
HORN_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
HORN_DIR=theories/CombinatoryLogic-rk
HORN_MODULES=(Core Presentation FiniteBasis ProductCatalogue Hilbert
  ProductHilbert IdentityCatalogue ConstantCatalogue SubstitutionCatalogue
  CatalogueHilbert CatalogueEconomy ContextualHilbert ProductExposure
  ContextualSubstitution HilbertAbstraction CatalogueShapes HilbertReplay
  AffineDuplication QuantitativeNormalization FiniteNormalForms GroundHorn
  BCKW KnuthBounds ChurchFinite NativeCanonicity GroundHornConsistency
  FiniteHorn HilbertGrounding HilbertFiniteModels FiniteHornChurch
  FiniteModelBoundary FiniteUniversalHorn)
HORN_SOURCES=()
HORN_ROOTS=()
for horn_module in "${HORN_MODULES[@]}"; do
  HORN_SOURCES+=("$HORN_DIR/$horn_module.v")
  HORN_ROOTS+=("PTSrk.Combinatory.$horn_module")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' "$HORN_LOG" "$HORN_BUILD" "$HORN_UPSTREAM" | tee "$HORN_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$HORN_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$HORN_LOG/commands.txt"
  printf '\n' >> "$HORN_LOG/commands.txt"
  set +e
  "$@" > "$HORN_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$HORN_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$HORN_LOG/$label.log"; exit "$result"; fi
}
check_reports() {
  local expected actual
  expected="$(rg --no-filename '^Print Assumptions ' "${HORN_SOURCES[@]}" | wc -l | tr -d ' ')"
  actual="$(rg -c '^Closed under the global context$' "$HORN_LOG/fresh-build.log")"
  printf 'Modules: %s\nOwn reports: %s\nAggregate closed reports: %s\n' "${#HORN_MODULES[@]}" "$expected" "$actual"
  [[ "${#HORN_MODULES[@]}" -eq 32 && "$expected" -gt 241 ]]
  # Ranks is the only imported module printing an additional report.
  [[ "$actual" -eq "$((expected + 1))" ]]
  if rg -n '^Axioms:|^Assumptions:' "$HORN_LOG/fresh-build.log"; then return 1; fi
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${HORN_SOURCES[@]}"; then return 1; fi
}
compare_inventory() {
  # Keep diagnostics in the raw logs. Compare the COMPLETE context reports,
  # not load-path warnings caused by overlapping established library roots.
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$HORN_LOG/upstream-kernel.log")" -eq 1 ]]
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$HORN_LOG/kernel.log")" -eq 1 ]]
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$HORN_LOG/upstream-kernel.log" > "$HORN_LOG/upstream-inventory.txt"
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$HORN_LOG/kernel.log" > "$HORN_LOG/inventory.txt"
  cmp "$HORN_LOG/upstream-inventory.txt" "$HORN_LOG/inventory.txt"
}
run head git rev-parse HEAD
run dune-version opam exec -- dune --version
run rocq-version opam exec -- rocq -v
run packages opam list --installed --columns=name,version
run source-before shasum -a 256 "${HORN_SOURCES[@]}" "$HORN_DIR/dune" theories/Interpretation_of_R/DirectREval.v
run upstream-archive git archive --output="$HORN_LOG/upstream.tar" "$HORN_BASE"
run upstream-extract tar -xf "$HORN_LOG/upstream.tar" -C "$HORN_UPSTREAM"
run upstream-build opam exec -- timeout 600 dune build --root "$HORN_UPSTREAM" --display=short --no-buffer -j 2 theories/Ranks.vo
run upstream-kernel opam exec -- timeout 600 rocq check -silent -o -Q "$HORN_UPSTREAM/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 900 dune build --build-dir "$HORN_BUILD" --display=short --no-buffer -j 2 @theories/CombinatoryLogic-rk/audit
run closed-reports check_reports
run kernel opam exec -- timeout 900 rocq check -silent -o \
  -Q "$HORN_BUILD/default/theories" PTSrk \
  -Q "$HORN_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$HORN_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$HORN_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory "${HORN_ROOTS[@]}"
run inventory-compare compare_inventory
run original-kernel-unchanged git diff --exit-code "$HORN_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run agda-unchanged shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/agda-sources.sha256
run source-after shasum -a 256 "${HORN_SOURCES[@]}" "$HORN_DIR/dune" theories/Interpretation_of_R/DirectREval.v
run source-stable cmp "$HORN_LOG/source-before.log" "$HORN_LOG/source-after.log"
run safety-scan safety_scan
run whitespace git diff --check -- "$HORN_DIR" \
  docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23 \
  docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md
printf 'PASS: fresh 32-module focused consistent-Horn audit. Logs: %s\n' "$HORN_LOG"
