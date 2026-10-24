#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
IP_EVIDENCE=docs/direct-r-handoff/verification/combinatory-indexed-provenance-2026-10-23
IP_FINAL="$(mktemp -d "$IP_EVIDENCE/final.XXXXXX")"
printf 'Final evidence: %s\n' "$IP_FINAL"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$IP_FINAL/status.tsv"
run() {
  local name="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$IP_FINAL/commands.txt"
  printf '\n' >> "$IP_FINAL/commands.txt"
  set +e
  "$@" > "$IP_FINAL/$name.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$name" "$result" "$started" "$finished" | tee -a "$IP_FINAL/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -60 "$IP_FINAL/$name.log"; return "$result"; fi
}
check_new_file() {
  local file="$1" diagnostic result
  [[ -f "$file" ]] || return 1
  if diagnostic="$(git diff --no-index --check /dev/null "$file" 2>&1)"; then result=0; else result=$?; fi
  [[ "$result" -le 1 && -z "$diagnostic" ]] || { printf '%s\n' "$diagnostic"; return 1; }
}
new_file_whitespace() {
  local source
  for source in FiniteTypeDispatch IndexedHornEncoding IndexedHornRealization MM0GuardProvenance IndexedHornSoundness MM0IndexedReflection; do
    check_new_file "theories/CombinatoryLogic-rk/$source.v" || return 1
  done
  for source in AUDIT.sh NOTE-CHECK.sh ARCHIVE-ISOLATED.sh FINAL-CHECKS.sh COMMANDS.md inspect.swift; do
    check_new_file "$IP_EVIDENCE/$source" || return 1
  done
}
normalize_logs() {
  local file
  for file in "$IP_FINAL"/*.log "$IP_FINAL"/*.txt "$IP_FINAL"/*.tsv; do
    [[ -f "$file" ]] || continue
    gzip -c "$file" > "$file.raw.gz" || return 1
    perl -0pi -e 's/[ \t]+$//mg; s/\n+\z/\n/' "$file" || return 1
  done
}
trap 'ip_result=$?; normalize_logs || ip_result=$?; exit "$ip_result"' EXIT
run proof-stable shasum -a 256 -c "$IP_EVIDENCE/audit.emobKi/source-after.log"
run note-stable shasum -a 256 -c "$IP_EVIDENCE/note.5KCYYS/final-manifest.log"
run whitespace git diff --check -- theories/CombinatoryLogic-rk docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md "$IP_EVIDENCE"
run new-file-whitespace new_file_whitespace
run handoff-manifest shasum -a 256 docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md theories/CombinatoryLogic-rk/EVIDENCE.md theories/CombinatoryLogic-rk/README.md "$IP_EVIDENCE/COMMANDS.md"
printf 'PASS: final source/note stability and documentation whitespace.\n'
