#!/usr/bin/env bash
# Collect this worker's evidence without importing interfaces or whole trees.
set -euo pipefail
archive=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
scratch=/tmp/pts-rk-normal-contexts.KPvTCg

copy_text() {
  local source=$1 target=$2
  mkdir -p "$(dirname "$target")"
  if LC_ALL=C rg -q '[ \t]+$' "$source"; then
    gzip -n -c "$source" > "$target.raw.gz"
    sed 's/[[:blank:]]*$//' "$source" > "$target"
  else
    cp "$source" "$target"
  fi
}

for name in COMMANDS.md check.sh probe-check.sh; do
  copy_text "$scratch/$name" "$archive/$name"
done

for run in check-01 check-02 check-03 check-04-core check-05 check-06 check-07-final \
  probe-01-normalizer probe-02-full probe-03-tyaction probe-04-tyonly \
  probe-05-tyagrees probe-06-explicit probe-07-inference; do
  mkdir -p "$archive/$run"
  for name in check.log command.txt started.txt finished.txt exit-code.txt driver-error.txt; do
    if [[ -f "$scratch/$run/$name" ]]; then
      copy_text "$scratch/$run/$name" "$archive/$run/$name"
    fi
  done
done

# These fresh-run source copies were never reused as cached workspaces.
for run in check-01 check-02 check-03 check-05 check-06 check-07-final; do
  for name in NormalizedContexts.agda NormalizedFamilies.agda; do
    cp "$scratch/$run/source/$name" "$archive/$run/$name"
    cmp "$scratch/$run/source/$name" "$archive/$run/$name"
  done
done
cp "$scratch/check-07-final/source/NormalizedInference.agda" \
  "$archive/check-07-final/NormalizedInference.agda"

# The original core probe itself stayed unchanged. Other cached probes share
# a mutable working tree; archive their FINAL versions, not invented snapshots.
cp "$scratch/ContextIRProbe.agda" "$archive/check-04-core/ContextIRProbe.agda"
mkdir -p "$archive/final-probes"
for name in ContextIRProbe.agda ContextNormalizeProbe.agda ContextActionProbe.agda \
  ContextTyOnlyProbe.agda; do
  cp "$scratch/check-04-core/source/$name" "$archive/final-probes/$name"
done

{
  printf 'Recorded during archive collection, not a fresh proof check.\n'
  date -u '+%Y-%m-%d %H:%M:%S UTC'
  /tmp/pts-rk-agda-2.8.0.MvVO53/agda --version
  git -C /tmp/pts-rk-agda-2.8.0.MvVO53/cubical rev-parse HEAD
} > "$archive/toolchain.txt"

cd "$archive"
rg --files -uu . | LC_ALL=C sort | rg -v '^\./archive\.sha256$' |
  while IFS= read -r name; do shasum -a 256 "$name"; done > archive.sha256
