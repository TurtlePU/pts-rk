#!/usr/bin/env bash
# Post-documentation checks; not a second proof compilation.
set -euo pipefail
SOURCE_FINAL_ROOT="$(git rev-parse --show-toplevel)"
cd "$SOURCE_FINAL_ROOT"
SOURCE_FINAL_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-source-provenance-2026-10-23
SOURCE_FINAL_LOG="$(mktemp -d "$SOURCE_FINAL_ROOT/_build/self-consistency-source-provenance-final.XXXXXX")"
printf 'Logs: %s\n' "$SOURCE_FINAL_LOG" | tee "$SOURCE_FINAL_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$SOURCE_FINAL_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$SOURCE_FINAL_LOG/commands.txt"
  printf '\n' >> "$SOURCE_FINAL_LOG/commands.txt"
  set +e
  "$@" > "$SOURCE_FINAL_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$SOURCE_FINAL_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$SOURCE_FINAL_LOG/$label.log"; exit "$result"; fi
}
source_manifest() {
  awk '{print $2}' "$SOURCE_FINAL_EVIDENCE/audit-02/source-after.log" | while IFS= read -r source_final_file; do
    shasum -a 256 "$source_final_file"
  done
}
registration_normalization() {
  local source_actual
  source_actual="$(sed '/^From PTSrk.SelfConsistency Require Import SourceProvenanceAudit\.$/d' \
    theories/self_consistency/Audit.v | shasum -a 256 | awk '{print $1}')"
  printf '%s  normalized theories/self_consistency/Audit.v\n' "$source_actual"
  [[ "$source_actual" = da5cd5e01d62ce9b8fecbdff4da255d86f6e5bc1ad066accb79722db09434127 ]] || return 1
  source_actual="$(perl -0pe \
    's/   CheckerSourceGraph InternalExecutionGraph CheckerGraphRealization SourceProvenanceAudit\n//; s/\n\(alias\n \(name source-provenance-audit\)\n \(deps SourceProvenanceAudit.vo\)\)\n//' \
    theories/self_consistency/dune | shasum -a 256 | awk '{print $1}')"
  printf '%s  normalized theories/self_consistency/dune\n' "$source_actual"
  [[ "$source_actual" = 5f6ef9d73ff3d26b93b3c25cf37b459bd2c31979519572ccacb0eae35029dec9 ]] || return 1
  source_actual="$(perl -0pe \
    's/   FiniteModelSoundness MM0SyntaxSoundness MM0InternalSoundness\n   GuardedFiniteCarriers GuardedHornFragments MM0GuardedQuantification\n   GuardedHilbertModels GuardedBetaGraphs GuardedHilbertTables\n   GuardedHilbertCoverage\)/   FiniteModelSoundness MM0SyntaxSoundness MM0InternalSoundness\)/; s/   FiniteModelSoundness.vo MM0SyntaxSoundness.vo MM0InternalSoundness.vo\n   GuardedFiniteCarriers.vo GuardedHornFragments.vo MM0GuardedQuantification.vo\n   GuardedHilbertModels.vo GuardedBetaGraphs.vo GuardedHilbertTables.vo\n   GuardedHilbertCoverage.vo\)\)/   FiniteModelSoundness.vo MM0SyntaxSoundness.vo MM0InternalSoundness.vo\)\)/' \
    theories/CombinatoryLogic-rk/dune | shasum -a 256 | awk '{print $1}')"
  printf '%s  normalized theories/CombinatoryLogic-rk/dune\n' "$source_actual"
  [[ "$source_actual" = b09b748ec0da0da4980558d6d778df950918fb77ef1c4ce9273e68c04642d2a8 ]]
}
source_stability() {
  local source_manifest
  for source_manifest in source-before source-after; do
    awk '$2 != "theories/CombinatoryLogic-rk/dune"' \
      "$SOURCE_FINAL_EVIDENCE/audit-02/$source_manifest.log" > "$SOURCE_FINAL_LOG/$source_manifest-proof-scope.txt"
  done
  awk '$2 != "theories/CombinatoryLogic-rk/dune"' \
    "$SOURCE_FINAL_LOG/current-sources.log" > "$SOURCE_FINAL_LOG/current-proof-scope.txt"
  cmp "$SOURCE_FINAL_LOG/source-before-proof-scope.txt" "$SOURCE_FINAL_LOG/source-after-proof-scope.txt"
  cmp "$SOURCE_FINAL_LOG/source-before-proof-scope.txt" "$SOURCE_FINAL_LOG/current-proof-scope.txt"
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' \
    theories/self_consistency/CheckerSourceGraph.v \
    theories/self_consistency/InternalExecutionGraph.v \
    theories/self_consistency/CheckerGraphRealization.v \
    theories/self_consistency/SourceProvenanceAudit.v; then return 1; fi
}
note_hashes() {
  test -s "$SOURCE_FINAL_EVIDENCE/note-final/source.sha256" || return 1
  shasum -a 256 -c "$SOURCE_FINAL_EVIDENCE/note-final/source.sha256"
}
whitespace() {
  local source_final_file source_final_result
  local source_final_files=(theories/self_consistency/CheckerSourceGraph.v
    theories/self_consistency/InternalExecutionGraph.v
    theories/self_consistency/CheckerGraphRealization.v
    theories/self_consistency/SourceProvenanceAudit.v theories/self_consistency/Audit.v
    theories/self_consistency/dune theories/self_consistency/README.md
    theories/self_consistency/EVIDENCE.md theories/self_consistency/DIRECT_ROADMAP.tex
    docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  while IFS= read -r source_final_file; do
    source_final_files+=("$source_final_file")
  done < <(rg --files "$SOURCE_FINAL_EVIDENCE" -g '*.sh' -g '*.md' -g '*.v' -g '*.draft' | LC_ALL=C sort)
  git diff --check -- "${source_final_files[@]}" || return "$?"
  for source_final_file in "${source_final_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$source_final_file" >/dev/null 2>&1; then
      if git diff --no-index --check -- /dev/null "$source_final_file"; then
        source_final_result=0
      else
        source_final_result=$?
      fi
      if [[ "$source_final_result" -gt 1 ]]; then return "$source_final_result"; fi
    fi
  done
}
no_cache_artifacts() {
  if rg --files --hidden "$SOURCE_FINAL_EVIDENCE" -g '*.vo' -g '*.vos' -g '*.vok' \
    -g '*.glob' -g '*.aux' -g '*.tar' -g '*.png' -g '*.jpg' -g '*.pdf'; then return 1; fi
}
run head git rev-parse HEAD
run head-stable cmp "$SOURCE_FINAL_LOG/head.log" "$SOURCE_FINAL_EVIDENCE/audit-02/head.log"
run current-sources source_manifest
run source-stable source_stability
run previous-proofs shasum -a 256 -c "$SOURCE_FINAL_EVIDENCE/audit-02/previous-sources.sha256"
run registration-normalization registration_normalization
run inventory-compare cmp "$SOURCE_FINAL_EVIDENCE/audit-02/pristine-inventory.txt" "$SOURCE_FINAL_EVIDENCE/audit-02/inventory.txt"
run safety-scan safety_scan
run original-kernel git diff --exit-code 723cf2ec61c737ae82ba33d2e7db44f650122b0e -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run note-hashes note_hashes
run whitespace whitespace
run archive-scope no_cache_artifacts
printf 'PASS: final source-provenance documentation/source checks. Logs: %s\n' "$SOURCE_FINAL_LOG"
