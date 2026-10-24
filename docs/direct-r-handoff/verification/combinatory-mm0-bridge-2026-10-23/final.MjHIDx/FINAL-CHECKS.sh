#!/usr/bin/env bash
# Validate final sources against the successful fresh attempt-03 proof run.
# This reruns the repaired whitespace gate; it is NOT a cached compilation.
set -euo pipefail
MODEL_ROOT="$(git rev-parse --show-toplevel)"
cd "$MODEL_ROOT"
MODEL_DIR=theories/CombinatoryLogic-rk
MODEL_EVIDENCE=docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23
MODEL_FRESH="$MODEL_ROOT/_build/combinatory-mm0-bridge-audit.BLPblO"
MODEL_LOG="$(mktemp -d "$MODEL_ROOT/_build/combinatory-mm0-bridge-final.XXXXXX")"
MODEL_ARCHIVE="$(mktemp -d "$MODEL_ROOT/$MODEL_EVIDENCE/final.XXXXXX")"
MODEL_MODULES=()
MODEL_SOURCES=()
while read -r model_hash model_source; do
  case "$model_source" in
    "$MODEL_DIR"/*.v)
      MODEL_SOURCES+=("$model_source")
      MODEL_MODULES+=("$model_source") ;;
  esac
done < "$MODEL_FRESH/source-before.log"
for model_function in run archive_logs check_reports safety_scan \
  check_new_file_whitespace audit_whitespace; do
  eval "$(sed -n "/^$model_function()/,/^}/p" "$MODEL_EVIDENCE/AUDIT.sh")"
done
trap 'model_result=$?; archive_logs || model_result=$?; exit "$model_result"' EXIT
printf 'stage\texit\tstart_utc\tend_utc\n' > "$MODEL_LOG/status.tsv"
printf 'Fresh evidence: %s\nFinal logs: %s\nArchive: %s\n' \
  "$MODEL_FRESH" "$MODEL_LOG" "$MODEL_ARCHIVE" | tee "$MODEL_LOG/paths.txt"

fresh_reports() { local MODEL_LOG="$MODEL_FRESH"; check_reports; }
fresh_inventory() {
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$MODEL_FRESH/kernel.log")" -eq 1 ]] || return 1
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$MODEL_FRESH/upstream-kernel.log")" -eq 1 ]] || return 1
  cmp <(sed -n '/^CONTEXT SUMMARY$/,$p' "$MODEL_FRESH/kernel.log") \
    <(sed -n '/^CONTEXT SUMMARY$/,$p' "$MODEL_FRESH/upstream-kernel.log")
}
gate_fixtures() {
  local result
  check_new_file_whitespace "$MODEL_EVIDENCE/AUDIT.sh" || return 1
  printf 'Clean new file: accepted\n'
  if check_new_file_whitespace "$MODEL_ROOT/_build/combinatory-mm0-bridge-audit.KjFF55/kernel.log"; then
    return 1
  fi
  printf 'Whitespace fixture: rejected\n'
  if check_new_file_whitespace "$MODEL_LOG/not-created.whitespace-input"; then
    return 1
  fi
  printf 'Missing-file fixture: rejected\n'
  local MODEL_LOG="$MODEL_ROOT/_build/combinatory-mm0-bridge-audit.KjFF55"
  if check_reports; then return 1; fi
  printf 'Wrong-count fixture: rejected\n'
}
final_whitespace() {
  audit_whitespace || return 1
  check_new_file_whitespace "$MODEL_EVIDENCE/FINAL-CHECKS.sh" || return 1
  check_new_file_whitespace "$MODEL_EVIDENCE/COMMANDS.md" || return 1
  check_new_file_whitespace "$MODEL_EVIDENCE/syntax-algebra/COMMANDS.md"
}

run shell-syntax bash -n "$MODEL_EVIDENCE/AUDIT.sh" "$MODEL_EVIDENCE/FINAL-CHECKS.sh"
run driver-hashes shasum -a 256 "$MODEL_EVIDENCE/AUDIT.sh" "$MODEL_EVIDENCE/FINAL-CHECKS.sh"
run fresh-source-stable cmp "$MODEL_FRESH/source-before.log" "$MODEL_FRESH/source-after.log"
run current-source-hashes shasum -a 256 -c "$MODEL_FRESH/source-after.log"
run fresh-report-counts fresh_reports
run fresh-pristine-inventory fresh_inventory
run safety-scan safety_scan
run gate-fixtures gate_fixtures
run note-manifest shasum -a 256 -c "$MODEL_EVIDENCE/note.rQGnBx/final-manifest.log"
archive_logs
run whitespace final_whitespace
printf 'PASS: final MM0 bridge checks. Logs: %s\n' "$MODEL_LOG"
