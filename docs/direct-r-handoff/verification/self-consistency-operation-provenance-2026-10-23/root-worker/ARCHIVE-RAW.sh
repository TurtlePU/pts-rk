#!/usr/bin/env bash
# Preserve exact original text separately from whitespace-clean readable copies.
set -euo pipefail
cd /Users/akuklev/air/pts-rk
ROOT_SOURCE=/tmp/pts-rk-context-provenance.pPeQ4L
ROOT_ARCHIVE=docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/root-worker
mkdir -p "$ROOT_ARCHIVE/raw"
ROOT_FILES=(CHECK.sh)
for label in codes-01 codes-02 codes-03 codes-04 beta-01 beta-02 beta-03 beta-04 beta-05 beta-06 beta-07 symbolic-01; do
  for ext in command start end exit source log; do ROOT_FILES+=("$label.$ext"); done
done
for file in "${ROOT_FILES[@]}"; do
  gzip -n -c "$ROOT_SOURCE/$file" > "$ROOT_ARCHIVE/raw/$file.gz"
  raw_hash="$(gzip -cd "$ROOT_ARCHIVE/raw/$file.gz" | shasum -a 256 | awk '{print $1}')"
  source_hash="$(shasum -a 256 "$ROOT_SOURCE/$file" | awk '{print $1}')"
  [[ "$raw_hash" = "$source_hash" ]]
  printf '%s  %s\n' "$raw_hash" "$file"
done
