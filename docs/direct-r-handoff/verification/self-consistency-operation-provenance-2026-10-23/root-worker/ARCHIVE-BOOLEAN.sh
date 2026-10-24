#!/usr/bin/env bash
set -euo pipefail
cd /Users/akuklev/air/pts-rk
BOOLEAN_SOURCE=/tmp/pts-rk-context-provenance.pPeQ4L
BOOLEAN_ARCHIVE=docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/root-worker
for label in boolean-01 boolean-02 boolean-03 boolean-04; do
  for ext in command start end exit source log; do
    file="$label.$ext"
    gzip -n -c "$BOOLEAN_SOURCE/$file" > "$BOOLEAN_ARCHIVE/raw/$file.gz"
    raw_hash="$(gzip -cd "$BOOLEAN_ARCHIVE/raw/$file.gz" | shasum -a 256 | awk '{print $1}')"
    source_hash="$(shasum -a 256 "$BOOLEAN_SOURCE/$file" | awk '{print $1}')"
    [[ "$raw_hash" = "$source_hash" ]]
    printf '%s  %s\n' "$raw_hash" "$file"
  done
done
