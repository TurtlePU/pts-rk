#!/usr/bin/env bash
# Post-documentation checks; not another fresh proof compilation.
set -euo pipefail
DICTIONARY_FINAL_ROOT="$(git rev-parse --show-toplevel)"
cd "$DICTIONARY_FINAL_ROOT"
DICTIONARY_FINAL_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23
DICTIONARY_FINAL_LOG="$(mktemp -d "$DICTIONARY_FINAL_ROOT/_build/self-consistency-dictionaries-final.XXXXXX")"
printf 'Logs: %s\n' "$DICTIONARY_FINAL_LOG" | tee "$DICTIONARY_FINAL_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$DICTIONARY_FINAL_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$DICTIONARY_FINAL_LOG/commands.txt"
  printf '\n' >> "$DICTIONARY_FINAL_LOG/commands.txt"
  set +e
  "$@" > "$DICTIONARY_FINAL_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$DICTIONARY_FINAL_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$DICTIONARY_FINAL_LOG/$label.log"; exit "$result"; fi
}
source_manifest() {
  rg --files theories -g '*.v' -g dune | LC_ALL=C sort | while IFS= read -r dictionary_final_file; do
    shasum -a 256 "$dictionary_final_file"
  done
}
note_hashes() {
  shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.tex theories/self_consistency/DIRECT_ROADMAP.pdf
  [[ "$(shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.tex | awk '{print $1}')" = 9c8a4020621e700aeb6339e86bee8f64b73f96b8a13efb3f186bdfc0a1c7fbe3 ]] || return 1
  [[ "$(shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.pdf | awk '{print $1}')" = c2aa306d7ebe8b60ac1c6cb0e0d38e9e662a06665d6094c22e16910378ce20e6 ]]
}
whitespace() {
  local dictionary_final_file dictionary_final_result
  local dictionary_final_files=(theories/self_consistency/InternalFiniteDictionaries.v
    theories/self_consistency/FiniteDictionaryRealization.v
    theories/self_consistency/DictionaryRejection.v theories/self_consistency/FiniteDictionaryAudit.v
    theories/self_consistency/Audit.v theories/self_consistency/dune
    theories/self_consistency/README.md theories/self_consistency/EVIDENCE.md
    theories/self_consistency/DIRECT_ROADMAP.tex docs/direct-r-handoff/STATE.md
    docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  while IFS= read -r dictionary_final_file; do
    dictionary_final_files+=("$dictionary_final_file")
  done < <(rg --files "$DICTIONARY_FINAL_EVIDENCE" -g '*.sh' -g '*.md' -g '*.v' | LC_ALL=C sort)
  git diff --check -- "${dictionary_final_files[@]}" || return "$?"
  for dictionary_final_file in "${dictionary_final_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$dictionary_final_file" >/dev/null 2>&1; then
      if git diff --no-index --check -- /dev/null "$dictionary_final_file"; then
        dictionary_final_result=0
      else
        dictionary_final_result=$?
      fi
      if [[ "$dictionary_final_result" -gt 1 ]]; then return "$dictionary_final_result"; fi
    fi
  done
}
no_cache_artifacts() {
  if rg --files "$DICTIONARY_FINAL_EVIDENCE" -g '*.vo' -g '*.vos' -g '*.vok' \
    -g '*.glob' -g '*.aux' -g '*.tar' -g '*.png' -g '*.jpg' -g '*.pdf'; then return 1; fi
}
run head git rev-parse HEAD
run head-stable cmp "$DICTIONARY_FINAL_LOG/head.log" "$DICTIONARY_FINAL_EVIDENCE/audit-final/head.log"
run current-sources source_manifest
run source-stable cmp "$DICTIONARY_FINAL_LOG/current-sources.log" "$DICTIONARY_FINAL_EVIDENCE/audit-final/source-after.log"
run previous-proofs shasum -a 256 -c "$DICTIONARY_FINAL_EVIDENCE/audit-final/previous-sources.sha256"
run original-kernel git diff --exit-code 723cf2ec61c737ae82ba33d2e7db44f650122b0e -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run note-hashes note_hashes
run whitespace whitespace
run archive-scope no_cache_artifacts
printf 'PASS: final documentation/source checks. Logs: %s\n' "$DICTIONARY_FINAL_LOG"
