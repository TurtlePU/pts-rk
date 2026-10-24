#!/usr/bin/env bash
# Run only a snapshot of this driver; retain failed runs as well as successes.
set -euo pipefail
NOTE_ROOT=/Users/akuklev/air/pts-rk
NOTE_EVIDENCE="$NOTE_ROOT/docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24"
cd "$NOTE_ROOT"
if [[ "${1:-}" != --snapshot ]]; then
  NOTE_DRIVER=$(mktemp -d /tmp/pts-rk-uniform-horn-note-driver.XXXXXX)
  cp "$NOTE_EVIDENCE/NOTE-CHECK.sh" "$NOTE_DRIVER/NOTE-CHECK.sh"
  chmod a-w "$NOTE_DRIVER/NOTE-CHECK.sh"
  exec bash "$NOTE_DRIVER/NOTE-CHECK.sh" --snapshot
fi
NOTE_LOG=$(mktemp -d "$NOTE_ROOT/_build/self-consistency-uniform-horn-note.XXXXXX")
NOTE_ARCHIVE=$(mktemp -d "$NOTE_EVIDENCE/note.XXXXXX")
NOTE_RENDER=$(mktemp -d /tmp/pts-rk-uniform-horn-note-render.XXXXXX)
printf 'Logs: %s\nArchive: %s\nRender: %s\n' "$NOTE_LOG" "$NOTE_ARCHIVE" "$NOTE_RENDER" | tee "$NOTE_LOG/paths.txt"
cp "$0" "$NOTE_LOG/driver.sh"
cp theories/self_consistency/DIRECT_ROADMAP.tex "$NOTE_LOG/source.tex"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$NOTE_LOG/status.tsv"
finish() {
  local note_result=$? note_file
  trap - EXIT
  printf '%s\n' "$note_result" > "$NOTE_LOG/result.txt"
  for note_file in "$NOTE_LOG"/*; do
    [[ -f "$note_file" ]] || continue
    gzip -c "$note_file" > "$NOTE_ARCHIVE/$(basename "$note_file").raw.gz"
    cmp "$note_file" <(gzip -dc "$NOTE_ARCHIVE/$(basename "$note_file").raw.gz")
  done
  cp "$NOTE_LOG/status.tsv" "$NOTE_LOG/paths.txt" "$NOTE_LOG/result.txt" "$NOTE_ARCHIVE/"
  printf 'Note check exit: %s\n' "$note_result"
  exit "$note_result"
}
trap finish EXIT
run() {
  local note_stage=$1 note_start note_end note_exit
  shift
  note_start=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
  printf '%q ' "$@" >> "$NOTE_LOG/commands.txt"
  printf '\n' >> "$NOTE_LOG/commands.txt"
  set +e
  "$@" > "$NOTE_LOG/$note_stage.log" 2>&1
  note_exit=$?
  set -e
  note_end=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
  printf '%s\t%s\t%s\t%s\n' "$note_stage" "$note_exit" "$note_start" "$note_end" | tee -a "$NOTE_LOG/status.tsv"
  if [[ "$note_exit" -ne 0 ]]; then tail -60 "$NOTE_LOG/$note_stage.log"; exit "$note_exit"; fi
}
run build bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
NOTE_BUILD=$(sed -n 's/^Build directory: //p' "$NOTE_LOG/build.log")
for note_name in build.log versions.log DIRECT_ROADMAP.log build-exit-code.txt; do
  cp "$NOTE_BUILD/$note_name" "$NOTE_LOG/latex-$note_name"
done
run inspect swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift \
  theories/self_consistency/DIRECT_ROADMAP.pdf "$NOTE_RENDER"
run source-stable cmp "$NOTE_LOG/source.tex" theories/self_consistency/DIRECT_ROADMAP.tex
run hashes shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.tex theories/self_consistency/DIRECT_ROADMAP.pdf
cp "$NOTE_RENDER/text.txt" "$NOTE_LOG/pdf-text.txt"
