#!/usr/bin/env bash
# Fresh complete closure check for comparison-preserving checker execution.
set -euo pipefail
COMPARISON_ROOT="$(git rev-parse --show-toplevel)"
cd "$COMPARISON_ROOT"
COMPARISON_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$COMPARISON_LOCAL/bin:$PATH"
export OPAMROOT="$COMPARISON_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
COMPARISON_LOG="$(mktemp -d "$COMPARISON_ROOT/_build/self-consistency-comparisons-audit.XXXXXX")"
COMPARISON_BUILD="$(mktemp -d /tmp/pts-rk-comparisons-fresh.XXXXXX)"
COMPARISON_PRISTINE="$(mktemp -d /tmp/pts-rk-comparisons-pristine.XXXXXX)"
COMPARISON_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
COMPARISON_DIR=theories/self_consistency
COMPARISON_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23
COMPARISON_PREVIOUS=docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/audit-final/source-after.log
COMPARISON_MODULES=(InternalCodeComparison CheckerComparisons CodeComparisonRealization
  InternalComparisonFolds CheckerExecution)
COMPARISON_SOURCES=("$COMPARISON_DIR/ComparisonExecutionAudit.v")
for comparison_module in "${COMPARISON_MODULES[@]}"; do
  COMPARISON_SOURCES+=("$COMPARISON_DIR/$comparison_module.v")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' "$COMPARISON_LOG" "$COMPARISON_BUILD" "$COMPARISON_PRISTINE" | tee "$COMPARISON_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$COMPARISON_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$COMPARISON_LOG/commands.txt"
  printf '\n' >> "$COMPARISON_LOG/commands.txt"
  set +e
  "$@" > "$COMPARISON_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$COMPARISON_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$COMPARISON_LOG/$label.log"; exit "$result"; fi
}
source_manifest() {
  rg --files theories -g '*.v' -g dune | LC_ALL=C sort | while IFS= read -r comparison_file; do
    shasum -a 256 "$comparison_file"
  done
}
declaration_coverage() {
  local comparison_module
  for comparison_module in "${COMPARISON_MODULES[@]}"; do
    awk -v module="$comparison_module" \
      '/^(Theorem|Lemma|Example|Corollary|Fact|Proposition) / {name=$2; sub(/:$/, "", name); print module "." module "." name}' \
      "$COMPARISON_DIR/$comparison_module.v"
  done | LC_ALL=C sort > "$COMPARISON_LOG/expected-declarations.txt"
  awk '$1 == "Print" && $2 == "Assumptions" {name=$3; sub(/\.$/, "", name); print name}' \
    "$COMPARISON_DIR/ComparisonExecutionAudit.v" | LC_ALL=C sort > "$COMPARISON_LOG/audited-declarations.txt"
  cmp "$COMPARISON_LOG/expected-declarations.txt" "$COMPARISON_LOG/audited-declarations.txt"
}
reports() {
  local expected actual
  expected="$(wc -l < "$COMPARISON_LOG/expected-declarations.txt")"
  actual="$(rg -c '^Closed under the global context$' "$COMPARISON_LOG/fresh-build.log")"
  printf 'New public endpoints: %s\nAggregate fresh closed reports: %s\n' "$expected" "$actual"
  [[ "$expected" -gt 0 && "$actual" -ge "$expected" ]] || return 1
  if rg -n '^Axioms:|^Assumptions:' "$COMPARISON_LOG/fresh-build.log"; then return 1; fi
}
compare_inventory() {
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$COMPARISON_LOG/pristine-kernel.log")" -eq 1 ]] || return 1
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$COMPARISON_LOG/kernel.log")" -eq 1 ]] || return 1
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$COMPARISON_LOG/pristine-kernel.log" > "$COMPARISON_LOG/pristine-inventory.txt"
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$COMPARISON_LOG/kernel.log" > "$COMPARISON_LOG/inventory.txt"
  cmp "$COMPARISON_LOG/pristine-inventory.txt" "$COMPARISON_LOG/inventory.txt"
}
previous_sources() {
  # Only audit registration and the Dune module/alias list may change.
  awk '$2 != "theories/self_consistency/Audit.v" && $2 != "theories/self_consistency/dune"' \
    "$COMPARISON_PREVIOUS" > "$COMPARISON_LOG/previous-sources.sha256"
  shasum -a 256 -c "$COMPARISON_LOG/previous-sources.sha256"
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${COMPARISON_SOURCES[@]}"; then return 1; fi
}
whitespace() {
  local comparison_file comparison_result
  local comparison_files=("${COMPARISON_SOURCES[@]}" "$COMPARISON_DIR/dune"
    "$COMPARISON_DIR/Audit.v" "$COMPARISON_DIR/README.md" "$COMPARISON_DIR/EVIDENCE.md"
    "$COMPARISON_DIR/DIRECT_ROADMAP.tex" docs/direct-r-handoff/STATE.md
    docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  while IFS= read -r comparison_file; do
    comparison_files+=("$comparison_file")
  done < <(rg --files "$COMPARISON_EVIDENCE" -g '*.sh' -g '*.md' -g '*.v' | LC_ALL=C sort)
  git diff --check -- "${comparison_files[@]}" || return "$?"
  for comparison_file in "${comparison_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$comparison_file" >/dev/null 2>&1; then
      if git diff --no-index --check -- /dev/null "$comparison_file"; then
        comparison_result=0
      else
        comparison_result=$?
      fi
      if [[ "$comparison_result" -gt 1 ]]; then return "$comparison_result"; fi
    fi
  done
}
run head git rev-parse HEAD
run versions opam exec -- rocq -v
run dune-version opam exec -- dune --version
run packages opam list --installed --columns=name,version
run disk df -h . /tmp
run source-before source_manifest
run previous-proofs-unchanged previous_sources
run declaration-coverage declaration_coverage
run pristine-archive git archive --output="$COMPARISON_LOG/pristine.tar" "$COMPARISON_BASE"
run pristine-extract tar -xf "$COMPARISON_LOG/pristine.tar" -C "$COMPARISON_PRISTINE"
run pristine-build opam exec -- timeout 600 dune build --root "$COMPARISON_PRISTINE" --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 600 rocq check -silent -o -Q "$COMPARISON_PRISTINE/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 1800 dune build --build-dir "$COMPARISON_BUILD" --display=short --no-buffer -j 2 @theories/self_consistency/comparison-execution-audit
run closed-reports reports
run kernel opam exec -- timeout 1800 rocq check -silent -o -bytecode-compiler yes \
  -Q "$COMPARISON_BUILD/default/theories" PTSrk \
  -Q "$COMPARISON_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$COMPARISON_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$COMPARISON_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  -Q "$COMPARISON_BUILD/default/theories/self_consistency" PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.ComparisonExecutionAudit
run inventory-compare compare_inventory
run original-kernel-unchanged git diff --exit-code "$COMPARISON_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run safety-scan safety_scan
run source-after source_manifest
run source-stable cmp "$COMPARISON_LOG/source-before.log" "$COMPARISON_LOG/source-after.log"
run previous-proofs-still-unchanged previous_sources
run whitespace whitespace
printf 'PASS: fresh comparison-execution closure. Logs: %s\n' "$COMPARISON_LOG"
