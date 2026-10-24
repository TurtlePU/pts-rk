#!/usr/bin/env bash
# Archive finished proof-worker evidence, never Agda interfaces or caches.
set -euo pipefail
archive=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

copy_text() {
  local source=$1 target=$2
  mkdir -p "$(dirname "$target")"
  if LC_ALL=C rg -q '[ \t]+$' "$source"; then
    # Preserve exact bytes as well as a whitespace-clean readable copy.
    gzip -n -c "$source" > "$target.raw.gz"
    sed 's/[[:blank:]]*$//' "$source" > "$target"
  else
    cp "$source" "$target"
  fi
}

collect_run() {
  local scratch=$1 group=$2 run=$3
  shift 3
  local target="$archive/$group/$run"
  mkdir -p "$target"
  for name in check.log command.txt exit-code.txt started.txt finished.txt; do
    copy_text "$scratch/$run/$name" "$target/$name"
  done
  for name in sources.sha256 source.sha256; do
    if [[ -f "$scratch/$run/$name" ]]; then
      copy_text "$scratch/$run/$name" "$target/$name"
    fi
  done
  for name in "$@"; do
    cp "$scratch/$run/source/$name" "$target/$name"
    cmp "$scratch/$run/source/$name" "$target/$name"
  done
}

inference=/tmp/pts-rk-normal-inference.DmOPAJ
native=/tmp/pts-rk-native-inference.MkNbTu
comprehension=/tmp/pts-rk-normal-comprehension.xFZ3o4
families=/tmp/pts-rk-normal-families.0vT95x

for group in inference native comprehension families; do
  case "$group" in
    inference) scratch=$inference; driver=CHECK.sh ;;
    native) scratch=$native; driver=CHECK.sh ;;
    comprehension) scratch=$comprehension; driver=check.sh ;;
    families) scratch=$families; driver=check.sh ;;
  esac
  copy_text "$scratch/COMMANDS.md" "$archive/$group/COMMANDS.md"
  copy_text "$scratch/$driver" "$archive/$group/$driver"
done

for run in check01 check02 check03 check04; do
  collect_run "$inference" inference "$run" NormalizedInference.agda NormalizedFamilies.agda
done
for run in check01 check02 check03; do
  collect_run "$native" native "$run" NativeBidirectional.agda
done
for run in check01 check02 check03 check04 check05 check06 check07; do
  # The first three comprehension checks precede the families dependency.
  if [[ -f "$comprehension/$run/source/NormalizedFamilies.agda" ]]; then
    collect_run "$comprehension" comprehension "$run" NormalizedComprehension.agda NormalizedFamilies.agda
  else
    collect_run "$comprehension" comprehension "$run" NormalizedComprehension.agda
  fi
done
for run in check-01 check-02 check-03 check-04 check-05-cast; do
  collect_run "$families" families "$run" NormalizedFamilies.agda
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
