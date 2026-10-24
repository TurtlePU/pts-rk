#!/usr/bin/env bash
# Post-documentation checks; not a second proof compilation.
set -euo pipefail
JOINT_FINAL_ROOT="$(git rev-parse --show-toplevel)"
cd "$JOINT_FINAL_ROOT"
JOINT_FINAL_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-joint-resources-2026-10-23
JOINT_FINAL_LOG="$(mktemp -d "$JOINT_FINAL_ROOT/_build/self-consistency-joint-resources-final.XXXXXX")"
printf 'Logs: %s\n' "$JOINT_FINAL_LOG" | tee "$JOINT_FINAL_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$JOINT_FINAL_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$JOINT_FINAL_LOG/commands.txt"
  printf '\n' >> "$JOINT_FINAL_LOG/commands.txt"
  set +e
  "$@" > "$JOINT_FINAL_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$JOINT_FINAL_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$JOINT_FINAL_LOG/$label.log"; exit "$result"; fi
}
source_manifest() {
  rg --files theories -g '*.v' -g dune | LC_ALL=C sort | while IFS= read -r joint_final_file; do
    shasum -a 256 "$joint_final_file"
  done
}
note_hashes() {
  test -s "$JOINT_FINAL_EVIDENCE/note-final/source.sha256" || return 1
  shasum -a 256 -c "$JOINT_FINAL_EVIDENCE/note-final/source.sha256"
}
whitespace() {
  local joint_final_file joint_final_result
  local joint_final_files=(theories/self_consistency/InternalJointTraversal.v
    theories/self_consistency/CheckerResourceBounds.v
    theories/self_consistency/ComputationBoundary.v
    theories/self_consistency/JointResourceAudit.v theories/self_consistency/Audit.v
    theories/self_consistency/dune theories/self_consistency/README.md
    theories/self_consistency/EVIDENCE.md theories/self_consistency/DIRECT_ROADMAP.tex
    docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  if [[ -f theories/self_consistency/JointTraversalRealization.v ]]; then
    joint_final_files+=(theories/self_consistency/JointTraversalRealization.v)
  fi
  while IFS= read -r joint_final_file; do
    joint_final_files+=("$joint_final_file")
  done < <(rg --files "$JOINT_FINAL_EVIDENCE" -g '*.sh' -g '*.md' -g '*.v' -g '*.draft' | LC_ALL=C sort)
  git diff --check -- "${joint_final_files[@]}" || return "$?"
  for joint_final_file in "${joint_final_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$joint_final_file" >/dev/null 2>&1; then
      if git diff --no-index --check -- /dev/null "$joint_final_file"; then
        joint_final_result=0
      else
        joint_final_result=$?
      fi
      if [[ "$joint_final_result" -gt 1 ]]; then return "$joint_final_result"; fi
    fi
  done
}
no_cache_artifacts() {
  if rg --files --hidden "$JOINT_FINAL_EVIDENCE" -g '*.vo' -g '*.vos' -g '*.vok' \
    -g '*.glob' -g '*.aux' -g '*.tar' -g '*.png' -g '*.jpg' -g '*.pdf'; then return 1; fi
}
run head git rev-parse HEAD
run head-stable cmp "$JOINT_FINAL_LOG/head.log" "$JOINT_FINAL_EVIDENCE/audit-final/head.log"
run current-sources source_manifest
run source-stable cmp "$JOINT_FINAL_LOG/current-sources.log" "$JOINT_FINAL_EVIDENCE/audit-final/source-after.log"
run previous-proofs shasum -a 256 -c "$JOINT_FINAL_EVIDENCE/audit-final/previous-sources.sha256"
run original-kernel git diff --exit-code 723cf2ec61c737ae82ba33d2e7db44f650122b0e -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run note-hashes note_hashes
run whitespace whitespace
run archive-scope no_cache_artifacts
printf 'PASS: final joint-resource documentation/source checks. Logs: %s\n' "$JOINT_FINAL_LOG"
