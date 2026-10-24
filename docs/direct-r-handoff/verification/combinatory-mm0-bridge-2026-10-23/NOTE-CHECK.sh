#!/usr/bin/env bash
set -euo pipefail
NOTE_ROOT="$(git rev-parse --show-toplevel)"
cd "$NOTE_ROOT"
NOTE_EVIDENCE=docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23
NOTE_LOG="$(mktemp -d "$NOTE_ROOT/_build/combinatory-mm0-note.XXXXXX")"
NOTE_RENDER="$(mktemp -d /tmp/pts-rk-mm0-note-final.XXXXXX)"
NOTE_ARCHIVE="$(mktemp -d "$NOTE_EVIDENCE/note.XXXXXX")"
printf 'Log: %s\nRender: %s\nArchive: %s\n' "$NOTE_LOG" "$NOTE_RENDER" "$NOTE_ARCHIVE" | tee "$NOTE_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$NOTE_LOG/status.tsv"
run() {
  local name="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$NOTE_LOG/commands.txt"
  printf '\n' >> "$NOTE_LOG/commands.txt"
  set +e
  "$@" > "$NOTE_LOG/$name.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$name" "$result" "$started" "$finished" | tee -a "$NOTE_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -60 "$NOTE_LOG/$name.log"; return "$result"; fi
}
run note-build bash theories/CombinatoryLogic-rk/build-note.sh
run pdf-inspect swift "$NOTE_EVIDENCE/inspect.swift" theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf "$NOTE_RENDER"
run final-manifest shasum -a 256 theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf theories/CombinatoryLogic-rk/build-note.sh \
  "$NOTE_EVIDENCE/inspect.swift"
cp "$NOTE_LOG"/* "$NOTE_ARCHIVE/"
cp "$NOTE_RENDER/pdf-text.txt" "$NOTE_RENDER/pdf-links.txt" "$NOTE_ARCHIVE/"
printf 'PASS: note build and full PDF inspection.\n'
