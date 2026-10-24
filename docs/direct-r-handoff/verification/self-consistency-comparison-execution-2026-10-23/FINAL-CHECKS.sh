#!/usr/bin/env bash
# Post-documentation source checks, not a second proof compilation.
set -euo pipefail
COMPARISON_FINAL_ROOT="$(git rev-parse --show-toplevel)"
cd "$COMPARISON_FINAL_ROOT"
COMPARISON_FINAL_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23
COMPARISON_FINAL_LOG="$(mktemp -d "$COMPARISON_FINAL_ROOT/_build/self-consistency-comparisons-final.XXXXXX")"
printf 'Logs: %s\n' "$COMPARISON_FINAL_LOG" | tee "$COMPARISON_FINAL_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$COMPARISON_FINAL_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$COMPARISON_FINAL_LOG/commands.txt"
  printf '\n' >> "$COMPARISON_FINAL_LOG/commands.txt"
  set +e
  "$@" > "$COMPARISON_FINAL_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$COMPARISON_FINAL_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$COMPARISON_FINAL_LOG/$label.log"; exit "$result"; fi
}
source_manifest() {
  rg --files theories -g '*.v' -g dune | LC_ALL=C sort | while IFS= read -r comparison_final_file; do
    shasum -a 256 "$comparison_final_file"
  done
}
note_hashes() {
  shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.tex theories/self_consistency/DIRECT_ROADMAP.pdf
  [[ "$(shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.tex | awk '{print $1}')" = c1a0a46279efcdf8e7a567006416807b6d2cf34569ec99e20519a374d43ae30f ]] || return 1
  [[ "$(shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.pdf | awk '{print $1}')" = 147e7a7824a499c742d3f8aabf77a230d604b38899f34c9c1d6e3ef70cb9a01a ]]
}
whitespace() {
  local comparison_final_file comparison_final_result
  local comparison_final_files=(theories/self_consistency/InternalCodeComparison.v
    theories/self_consistency/CheckerComparisons.v theories/self_consistency/CodeComparisonRealization.v
    theories/self_consistency/InternalComparisonFolds.v theories/self_consistency/CheckerExecution.v
    theories/self_consistency/ComparisonExecutionAudit.v theories/self_consistency/Audit.v
    theories/self_consistency/dune theories/self_consistency/README.md
    theories/self_consistency/EVIDENCE.md theories/self_consistency/DIRECT_ROADMAP.tex
    docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  while IFS= read -r comparison_final_file; do
    comparison_final_files+=("$comparison_final_file")
  done < <(rg --files "$COMPARISON_FINAL_EVIDENCE" -g '*.sh' -g '*.md' -g '*.v' | LC_ALL=C sort)
  git diff --check -- "${comparison_final_files[@]}" || return "$?"
  for comparison_final_file in "${comparison_final_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$comparison_final_file" >/dev/null 2>&1; then
      if git diff --no-index --check -- /dev/null "$comparison_final_file"; then
        comparison_final_result=0
      else
        comparison_final_result=$?
      fi
      if [[ "$comparison_final_result" -gt 1 ]]; then return "$comparison_final_result"; fi
    fi
  done
}
no_cache_artifacts() {
  if rg --files "$COMPARISON_FINAL_EVIDENCE" -g '*.vo' -g '*.vos' -g '*.vok' \
    -g '*.glob' -g '*.aux' -g '*.tar' -g '*.png' -g '*.jpg' -g '*.pdf'; then return 1; fi
}
run head git rev-parse HEAD
run head-stable cmp "$COMPARISON_FINAL_LOG/head.log" "$COMPARISON_FINAL_EVIDENCE/audit-final/head.log"
run current-sources source_manifest
run source-stable cmp "$COMPARISON_FINAL_LOG/current-sources.log" "$COMPARISON_FINAL_EVIDENCE/audit-final/source-after.log"
run previous-proofs shasum -a 256 -c "$COMPARISON_FINAL_EVIDENCE/audit-final/previous-sources.sha256"
run original-kernel git diff --exit-code 723cf2ec61c737ae82ba33d2e7db44f650122b0e -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run note-hashes note_hashes
run whitespace whitespace
run archive-scope no_cache_artifacts
printf 'PASS: final comparison documentation/source checks. Logs: %s\n' "$COMPARISON_FINAL_LOG"
