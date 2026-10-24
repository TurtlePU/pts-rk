#!/usr/bin/env bash
# Evidence collection only; no compiler or proof-source mutations.
set -eu
archive=/Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/combinatory-normal-first-2026-10-24/workers
direct=/tmp/pts-rk-sk-direct.pmQ7rC
algebra=/tmp/pts-rk-canonical-algebra.pAIEvR
rank=/tmp/pts-rk-skfast.TSEzs7
size=/tmp/pts-rk-sksize.flfBIE
collection=${1:-all}
case "$collection" in all|size) ;; *) exit 2 ;; esac

copy_top() {
  local origin=$1 destination=$2 item
  mkdir -p "$destination"
  for item in "$origin"/*; do
    if test -f "$item"; then
      case "$item" in
        *.md|*.txt|*.log|*.sha256|*.sh|*.agda)
          cp -p "$item" "$destination/" ;;
      esac
    fi
  done
}

if test "$collection" = all; then
copy_top "$direct" "$archive/direct"
copy_top "$algebra" "$archive/algebra"
copy_top "$rank" "$archive/rank"
copy_top "$rank/fresh" "$archive/rank/fresh"
copy_top "$rank/consolidated" "$archive/rank/consolidated"
copy_top "$rank/consolidation-baseline" "$archive/rank/consolidation-baseline"
for attempt in 01 02 03 04; do
  copy_top "$rank/snapshots/$attempt" "$archive/rank/snapshots/$attempt"
done

mkdir -p "$archive/direct/final-source" "$archive/algebra/final-source"
mkdir -p "$archive/rank/fresh/owned-source" "$archive/rank/consolidated/owned-source"
for module in SKDirectSoundness SKDirectGround SKDirectBoundary SKDirectEverything; do
  cp -p "$direct/source/$module.agda" "$archive/direct/final-source/"
done
cp -p "$algebra/source/CanonicalAlgebra.agda" "$archive/algebra/final-source/"
for module in SKSourceFast SKFastCanonical; do
  cp -p "$rank/fresh/source/$module.agda" "$archive/rank/fresh/owned-source/"
done
for module in SKSourceRank SKSourceNormal SKCanonicalExamples; do
  cp -p "$rank/consolidated/source/$module.agda" "$archive/rank/consolidated/owned-source/"
done
fi

# `bash COLLECT.sh size` extends the original archive without recopying it.
copy_top "$size" "$archive/size"
copy_top "$size/fresh" "$archive/size/fresh"
for attempt in 01 02 03 04 05 06; do
  copy_top "$size/snapshots/$attempt" "$archive/size/snapshots/$attempt"
done
mkdir -p "$archive/size/fresh/owned-source"
cp -p "$size/fresh/source/SKBracketSize.agda" "$archive/size/fresh/owned-source/"
normalize_dirs=("$archive/size")
if test "$collection" = all; then
  normalize_dirs+=("$archive/direct" "$archive/algebra" "$archive/rank")
fi

# Preserve original bytes before removing trailing horizontal whitespace.
# Historical source snapshots are never rewritten, so their hashes remain exact.
find "${normalize_dirs[@]}" -type f \
  \( -name '*.md' -o -name '*.txt' -o -name '*.log' -o -name '*.sha256' -o -name '*.sh' \) \
  -print | while IFS= read -r item; do
    if LC_ALL=C rg -q '[\t ]+$' "$item"; then
      gzip -n -c "$item" > "$item.raw.gz"
      perl -pi -e 's/[\t ]+$//' "$item"
    fi
  done

cd "$archive"
find . -type f ! -name archive.sha256 -print | LC_ALL=C sort \
  | while IFS= read -r item; do shasum -a 256 "$item"; done > archive.sha256
shasum -a 256 -c archive.sha256
