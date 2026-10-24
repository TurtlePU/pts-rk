#!/usr/bin/env bash
# Test coverage in the same set +e context as run(), including a missing Print.
set -euo pipefail
REGRESSION_ROOT="$(git rev-parse --show-toplevel)"
cd "$REGRESSION_ROOT"
REGRESSION_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23
source "$REGRESSION_EVIDENCE/SCOPE.sh"
REGRESSION_WORK="$(mktemp -d /tmp/pts-rk-operation-coverage.XXXXXX)"
printf 'Regression logs: %s\n' "$REGRESSION_WORK"
mkdir -p "$REGRESSION_WORK/fixture"
for module in "${OPERATION_MODULES[@]}"; do
  ln -s "$REGRESSION_ROOT/theories/self_consistency/$module.v" "$REGRESSION_WORK/fixture/$module.v"
done
ln -s "$REGRESSION_ROOT/$REGRESSION_EVIDENCE/coverage-regression/missing-print.v" "$REGRESSION_WORK/fixture/$OPERATION_AUDIT.v"
for script in AUDIT.sh FINAL-CHECKS.sh; do
  eval "$(sed -n '/^declaration_coverage()/,/^}/p' "$REGRESSION_EVIDENCE/$script")"
  for kind in positive negative; do
    OPERATION_LOG="$REGRESSION_WORK/$script-$kind"
    OPERATION_FINAL_LOG="$OPERATION_LOG"
    mkdir -p "$OPERATION_LOG"
    if [[ "$kind" = positive ]]; then
      OPERATION_DIR=theories/self_consistency
    else
      OPERATION_DIR="$REGRESSION_WORK/fixture"
    fi
    OPERATION_FINAL_DIR="$OPERATION_DIR"
    set +e
    declaration_coverage > "$OPERATION_LOG/result.log" 2>&1
    result=$?
    set -e
    printf '%s %s exit %s\n' "$script" "$kind" "$result"
    if [[ "$kind" = positive ]]; then
      [[ "$result" -eq 0 ]]
      [[ "$(wc -l < "$OPERATION_LOG/expected-declarations.txt")" -eq 80 ]]
    else
      [[ "$result" -ne 0 ]]
      [[ "$(awk '$1 == "Check" {n++} END {print n}' "$OPERATION_DIR/$OPERATION_AUDIT.v")" -eq 80 ]]
      [[ "$(wc -l < "$OPERATION_LOG/audited-declarations.txt")" -eq 79 ]]
    fi
  done
done
