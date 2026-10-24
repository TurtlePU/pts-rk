#!/usr/bin/env bash
# Retain root product diagnostics and the final fresh successful run.
set -euo pipefail
archive=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
scratch=/tmp/pts-rk-normal-products.5ZaaRR
test "$(cat "$scratch/check-12.exit.txt")" = 0

copy_text() {
  local source=$1 target=$2
  if LC_ALL=C rg -q '[ \t]+$' "$source"; then
    gzip -n -c "$source" > "$target.raw.gz"
    sed 's/[[:blank:]]*$//' "$source" > "$target"
  else
    cp "$source" "$target"
  fi
}

copy_text "$scratch/check.sh" "$archive/check.sh"
for attempt in 01 02 03 04 05 06 07 08 09 10 11 12; do
  for suffix in command.txt log exit.txt finished.txt sources.sha256 started.txt; do
    copy_text "$scratch/check-$attempt.$suffix" "$archive/check-$attempt.$suffix"
  done
  cp "$scratch/attempt-$attempt.agda" "$archive/attempt-$attempt.agda"
  cmp "$scratch/attempt-$attempt.agda" "$archive/attempt-$attempt.agda"
done
for name in probe-core.agda probe-type.agda; do
  cp "$scratch/$name" "$archive/$name"
  cmp "$scratch/$name" "$archive/$name"
done

{
  printf 'Recorded during archive collection, not a fresh proof check.\n'
  date -u '+%Y-%m-%d %H:%M:%S UTC'
  /tmp/pts-rk-agda-2.8.0.MvVO53/agda --version
  git -C /tmp/pts-rk-agda-2.8.0.MvVO53/cubical rev-parse HEAD
} > "$archive/toolchain.txt"

cd "$archive"
find . -type f ! -name archive.sha256 -print | LC_ALL=C sort |
  while IFS= read -r name; do shasum -a 256 "$name"; done > archive.sha256
shasum -a 256 -c archive.sha256
