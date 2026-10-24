#!/usr/bin/env bash
# Preserve PDF inspection evidence, excluding generated page images and PDF.
set -euo pipefail
archive=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
scratch=/tmp/pts-rk-dependent-normal-pdf.Mz2e0Y
pdf=/Users/akuklev/air/pts-rk/theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf
inspector=/Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/combinatory-dependent-normal-2026-10-24/inspect.swift
expected=48b8c969c743acc281b0bf8943d826cf719d4f209594f07ac5293f7ce45753b7

copy_text() {
  local source=$1 target=$2
  if LC_ALL=C rg -q '[ \t]+$' "$source"; then
    gzip -n -c "$source" > "$target.raw.gz"
    sed 's/[[:blank:]]*$//' "$source" > "$target"
  else
    cp "$source" "$target"
  fi
}

for name in RUN.sh command.txt started.txt finished.txt exit-code.txt \
  inspection.log pdf-text.txt pdf-links.txt VISUAL.md; do
  copy_text "$scratch/$name" "$archive/$name"
done

actual=$(shasum -a 256 "$pdf" | awk '{print $1}')
[[ "$actual" == "$expected" ]]
shasum -a 256 "$pdf" > "$archive/live-pdf.sha256"
shasum -a 256 "$inspector" > "$archive/inspector.sha256"
{
  date -u '+%Y-%m-%d %H:%M:%S UTC'
  printf 'Live PDF unchanged from successful inspection: %s\n' "$expected"
  shasum -a 256 -c "$archive/live-pdf.sha256"
  shasum -a 256 -c "$archive/inspector.sha256"
} > "$archive/live-stability.log"

cd "$archive"
rg --files -uu . | LC_ALL=C sort | rg -v '^\./archive\.sha256$' |
  while IFS= read -r name; do shasum -a 256 "$name"; done > archive.sha256
