#!/usr/bin/env bash
# Final gates after the fresh proof audit; no compilation is claimed here.
set -euo pipefail
GUARD_ROOT="$(git rev-parse --show-toplevel)"
cd "$GUARD_ROOT"
GUARD_EVIDENCE=docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23
GUARD_RUN="$GUARD_ROOT/_build/combinatory-guarded-fragments-audit.ACxpVa"
GUARD_LOG="$(mktemp -d "$GUARD_ROOT/_build/combinatory-guarded-final.XXXXXX")"
printf 'Final log directory: %s\n' "$GUARD_LOG"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$GUARD_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$GUARD_LOG/commands.txt"
  printf '\n' >> "$GUARD_LOG/commands.txt"
  set +e
  "$@" > "$GUARD_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$GUARD_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -40 "$GUARD_LOG/$label.log"; exit "$result"; fi
}
reports() {
  [[ "$(rg -c '^Closed under the global context$' "$GUARD_RUN/fresh-build.log")" -eq 694 ]]
  [[ "$(rg --no-filename '^Print Assumptions ' theories/CombinatoryLogic-rk/*.v | wc -l | tr -d ' ')" -eq 693 ]]
  if rg -n '^Axioms:|^Assumptions:' "$GUARD_RUN/fresh-build.log"; then return 1; fi
}
run shell-syntax bash -n "$GUARD_EVIDENCE/AUDIT.sh" "$GUARD_EVIDENCE/FINAL-CHECKS.sh" theories/CombinatoryLogic-rk/build-note.sh
run proof-sources shasum -a 256 -c "$GUARD_RUN/source-after.log"
run audit-source-stability cmp "$GUARD_RUN/source-before.log" "$GUARD_RUN/source-after.log"
run pristine-inventory cmp "$GUARD_RUN/inventory.txt" "$GUARD_RUN/upstream-inventory.txt"
run reports reports
run original-kernel git diff --exit-code 723cf2ec61c737ae82ba33d2e7db44f650122b0e -- theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run unchanged-agda shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/agda-sources.sha256
run note-manifest shasum -a 256 -c "$GUARD_EVIDENCE/note-final.sha256"
run whitespace git diff --check -- theories/CombinatoryLogic-rk "$GUARD_EVIDENCE" docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md
printf 'PASS: final gates; fresh proof results remain unchanged.\n'
