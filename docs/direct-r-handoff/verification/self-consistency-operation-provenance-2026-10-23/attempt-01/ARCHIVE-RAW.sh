#!/usr/bin/env bash
set -euo pipefail
cd /Users/akuklev/air/pts-rk
FAILED_SOURCE=_build/self-consistency-operation-provenance-audit.EssWLn
FAILED_ARCHIVE=docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/attempt-01
mkdir -p "$FAILED_ARCHIVE/raw"
for file in commands.txt disk.log dune-version.log head.log packages.log paths.txt previous-proofs-unchanged.log previous-sources.sha256 source-before.log status.tsv versions.log working-tree-before.log; do
  gzip -n -c "$FAILED_SOURCE/$file" > "$FAILED_ARCHIVE/raw/$file.gz"
  raw_hash="$(gzip -cd "$FAILED_ARCHIVE/raw/$file.gz" | shasum -a 256 | awk '{print $1}')"
  source_hash="$(shasum -a 256 "$FAILED_SOURCE/$file" | awk '{print $1}')"
  [[ "$raw_hash" = "$source_hash" ]]
  printf '%s  %s\n' "$raw_hash" "$file"
done
