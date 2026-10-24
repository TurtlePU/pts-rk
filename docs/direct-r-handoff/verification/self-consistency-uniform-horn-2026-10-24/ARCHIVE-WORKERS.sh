#!/usr/bin/env bash
# Separate source/evidence archival, never copied compiled objects or caches.
set -euo pipefail
HORN_ROOT="$(git rev-parse --show-toplevel)"
cd "$HORN_ROOT"
HORN_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24
source "$HORN_EVIDENCE/SCOPE.sh"
source "$HORN_EVIDENCE/WORKERS.sh"
[[ "$HORN_FROZEN" == yes ]] || { printf 'Workers are not frozen; no archive created.\n' >&2; exit 2; }
[[ "${#HORN_WORKERS[@]}" -eq "${#HORN_WORKER_ROOTS[@]}" ]] || exit 2
for horn_source in "${HORN_WORKER_ROOTS[@]}"; do
  case "$horn_source" in /tmp/pts-rk-*) ;; *) printf 'Unreviewed worker path: %s\n' "$horn_source" >&2; exit 2 ;; esac
  [[ -d "$horn_source" && ! -L "$horn_source" ]] || exit 2
done
HORN_ARCHIVE="$(mktemp -d "$HORN_EVIDENCE/workers.XXXXXX")"
cp "$HORN_EVIDENCE/ARCHIVE-WORKERS.sh" "$HORN_EVIDENCE/WORKERS.sh" "$HORN_EVIDENCE/SCOPE.sh" "$HORN_ARCHIVE/"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HORN_ARCHIVE/start.txt"
printf 'label\toriginal_root\n' > "$HORN_ARCHIVE/paths.tsv"
printf 'label\tstage\texit_or_incomplete\tstart_utc\tend_utc\n' > "$HORN_ARCHIVE/status.tsv"
worker_files() {
  rg --files "$1" -g '*.sh' -g '*.v' -g '*.log' -g '*.command' -g '*.start' \
    -g '*.end' -g '*.exit' -g '*.source' -g '*.txt' -g '*.tsv' -g '*.sha256' | LC_ALL=C sort
}
for ((horn_index=0; horn_index<${#HORN_WORKERS[@]}; horn_index++)); do
  horn_label="${HORN_WORKERS[$horn_index]}"
  horn_source="${HORN_WORKER_ROOTS[$horn_index]}"
  horn_target="$HORN_ARCHIVE/$horn_label"
  mkdir "$horn_target"
  printf '%s\t%s\n' "$horn_label" "$horn_source" >> "$HORN_ARCHIVE/paths.tsv"
  worker_files "$horn_source" > "$horn_target/source-files-before.txt"
  [[ -s "$horn_target/source-files-before.txt" ]] || exit 1
  while IFS= read -r horn_file; do
    shasum -a 256 "$horn_file"
  done < "$horn_target/source-files-before.txt" > "$horn_target/source-before.sha256"
  while IFS= read -r horn_file; do
    horn_relative="${horn_file#"$horn_source"/}"
    [[ "$horn_relative" != "$horn_file" ]] || exit 1
    horn_copy="$horn_target/$horn_relative"
    mkdir -p "$(dirname "$horn_copy")"
    gzip -c "$horn_file" > "$horn_copy.raw.gz"
    cmp "$horn_file" <(gzip -dc "$horn_copy.raw.gz")
    # Exact bytes, including exact source snapshots, live in checked raw.gz.
    # The adjacent text is a whitespace-normalized reading copy only.
    perl -0pe 's/[ \t]+$//mg; s/\n+\z/\n/' "$horn_file" > "$horn_copy"
  done < "$horn_target/source-files-before.txt"
  worker_files "$horn_source" > "$horn_target/source-files-after.txt"
  cmp "$horn_target/source-files-before.txt" "$horn_target/source-files-after.txt"
  shasum -a 256 -c "$horn_target/source-before.sha256" > "$horn_target/source-stability.log"
  while IFS= read -r horn_file; do
    [[ "$horn_file" == *.start ]] || continue
    horn_stem="${horn_file%.start}"
    horn_stage="${horn_stem#"$horn_source"/}"
    horn_start="$(<"$horn_file")"
    horn_end=incomplete
    horn_exit=incomplete
    [[ ! -f "$horn_stem.end" ]] || horn_end="$(<"$horn_stem.end")"
    [[ ! -f "$horn_stem.exit" ]] || horn_exit="$(<"$horn_stem.exit")"
    printf '%s\t%s\t%s\t%s\t%s\n' "$horn_label" "$horn_stage" "$horn_exit" "$horn_start" "$horn_end"
  done < "$horn_target/source-files-before.txt" >> "$HORN_ARCHIVE/status.tsv"
done
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HORN_ARCHIVE/end.txt"
printf 'PASS: exact compressed worker evidence and source snapshots: %s\n' "$HORN_ARCHIVE"
