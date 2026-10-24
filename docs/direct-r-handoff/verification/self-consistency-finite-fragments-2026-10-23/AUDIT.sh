#!/usr/bin/env bash
# Fresh complete closure check for the finite-fragment normalization route.
set -euo pipefail
FRAGMENT_ROOT="$(git rev-parse --show-toplevel)"
cd "$FRAGMENT_ROOT"
FRAGMENT_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$FRAGMENT_LOCAL/bin:$PATH"
export OPAMROOT="$FRAGMENT_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
FRAGMENT_LOG="$(mktemp -d "$FRAGMENT_ROOT/_build/self-consistency-fragments-audit.XXXXXX")"
FRAGMENT_BUILD="$(mktemp -d /tmp/pts-rk-fragments-fresh.XXXXXX)"
FRAGMENT_PRISTINE="$(mktemp -d /tmp/pts-rk-fragments-pristine.XXXXXX)"
FRAGMENT_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
FRAGMENT_DIR=theories/self_consistency
FRAGMENT_MODULES=(FiniteCodeFragments FiniteSelectorSeparation FiniteCaseGuards
  FiniteFragmentNormalization FiniteFragmentTables FiniteFragmentRejection FiniteFragmentAudit)
FRAGMENT_SOURCES=()
for fragment_module in "${FRAGMENT_MODULES[@]}"; do
  FRAGMENT_SOURCES+=("$FRAGMENT_DIR/$fragment_module.v")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' "$FRAGMENT_LOG" "$FRAGMENT_BUILD" "$FRAGMENT_PRISTINE" | tee "$FRAGMENT_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$FRAGMENT_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$FRAGMENT_LOG/commands.txt"
  printf '\n' >> "$FRAGMENT_LOG/commands.txt"
  set +e
  "$@" > "$FRAGMENT_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$FRAGMENT_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$FRAGMENT_LOG/$label.log"; exit "$result"; fi
}
source_manifest() {
  rg --files theories -g '*.v' -g dune | LC_ALL=C sort | while IFS= read -r fragment_file; do
    shasum -a 256 "$fragment_file"
  done
}
reports() {
  local expected actual
  expected="$(rg -c '^Print Assumptions ' "$FRAGMENT_DIR/FiniteFragmentAudit.v")"
  actual="$(rg -c '^Closed under the global context$' "$FRAGMENT_LOG/fresh-build.log")"
  printf 'New public endpoints: %s\nAggregate fresh closed reports: %s\n' "$expected" "$actual"
  [[ "$expected" -eq 95 && "$actual" -ge "$expected" ]]
  if rg -n '^Axioms:|^Assumptions:' "$FRAGMENT_LOG/fresh-build.log"; then return 1; fi
}
compare_inventory() {
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$FRAGMENT_LOG/pristine-kernel.log")" -eq 1 ]]
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$FRAGMENT_LOG/kernel.log")" -eq 1 ]]
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$FRAGMENT_LOG/pristine-kernel.log" > "$FRAGMENT_LOG/pristine-inventory.txt"
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$FRAGMENT_LOG/kernel.log" > "$FRAGMENT_LOG/inventory.txt"
  cmp "$FRAGMENT_LOG/pristine-inventory.txt" "$FRAGMENT_LOG/inventory.txt"
}
previous_sources() {
  shasum -a 256 -c docs/direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23/previous-sources.sha256
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${FRAGMENT_SOURCES[@]}"; then return 1; fi
}
run head git rev-parse HEAD
run versions opam exec -- rocq -v
run dune-version opam exec -- dune --version
run packages opam list --installed --columns=name,version
run source-before source_manifest
run pristine-archive git archive --output="$FRAGMENT_LOG/pristine.tar" "$FRAGMENT_BASE"
run pristine-extract tar -xf "$FRAGMENT_LOG/pristine.tar" -C "$FRAGMENT_PRISTINE"
run pristine-build opam exec -- timeout 600 dune build --root "$FRAGMENT_PRISTINE" --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 600 rocq check -silent -o -Q "$FRAGMENT_PRISTINE/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 900 dune build --build-dir "$FRAGMENT_BUILD" --display=short --no-buffer -j 2 @theories/self_consistency/finite-fragment-audit
run closed-reports reports
run kernel opam exec -- timeout 900 rocq check -silent -o -bytecode-compiler yes \
  -Q "$FRAGMENT_BUILD/default/theories" PTSrk \
  -Q "$FRAGMENT_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$FRAGMENT_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$FRAGMENT_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  -Q "$FRAGMENT_BUILD/default/theories/self_consistency" PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.FiniteFragmentAudit
run inventory-compare compare_inventory
run original-kernel-unchanged git diff --exit-code "$FRAGMENT_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run combinatory-unchanged shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/audit-final/source-before.log
run previous-self-consistency-unchanged previous_sources
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run safety-scan safety_scan
run source-after source_manifest
run source-stable cmp "$FRAGMENT_LOG/source-before.log" "$FRAGMENT_LOG/source-after.log"
run whitespace git diff --check -- "${FRAGMENT_SOURCES[@]}" "$FRAGMENT_DIR/dune" \
  "$FRAGMENT_DIR/Audit.v" "$FRAGMENT_DIR/README.md" "$FRAGMENT_DIR/EVIDENCE.md" \
  "$FRAGMENT_DIR/DIRECT_ROADMAP.tex" \
  docs/direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23
printf 'PASS: fresh finite-fragment closure. Logs: %s\n' "$FRAGMENT_LOG"
