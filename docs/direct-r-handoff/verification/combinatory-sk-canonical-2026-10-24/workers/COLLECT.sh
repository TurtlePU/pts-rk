#!/usr/bin/env bash
# Collect worker evidence, excluding caches and unrelated source copies.
set -euo pipefail
archive_root=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

copy_top_level() {
  local worker_original=$1 worker_archive=$2 worker_file
  mkdir -p "$worker_archive"
  for worker_file in "$worker_original"/*; do
    [[ -f "$worker_file" ]] || continue
    case "$worker_file" in
      *.md|*.txt|*.log|*.sha256|*.sh|*.agda)
        cp -p "$worker_file" "$worker_archive/"
        ;;
    esac
  done
}

copy_top_level /tmp/pts-rk-sk-source.caRvqq "$archive_root/source"
copy_top_level /tmp/pts-rk-sk-canonical-normal.7ItOho "$archive_root/weak-normal"
copy_top_level /tmp/pts-rk-skbracket.Cjke1Y "$archive_root/bracket"
copy_top_level /tmp/pts-rk-skbracket.Cjke1Y/fresh "$archive_root/bracket/fresh"
copy_top_level /tmp/pts-rk-sk-source-normal.OEpsnr "$archive_root/source-normal"
copy_top_level /tmp/pts-rk-sk-source-final.yWoN0X "$archive_root/source-normal/final"

# Retain only the changed proof sources, including small per-attempt snapshots.
mkdir -p "$archive_root/source/final-source" "$archive_root/weak-normal/final-source"
mkdir -p "$archive_root/bracket/fresh/final-source" "$archive_root/source-normal/final/final-source"
cp -p /tmp/pts-rk-sk-source.caRvqq/source/SKSource.agda "$archive_root/source/final-source/"
cp -p /tmp/pts-rk-sk-canonical-normal.7ItOho/source/SKCanonicalNormal.agda "$archive_root/weak-normal/final-source/"
cp -p /tmp/pts-rk-skbracket.Cjke1Y/fresh/source/SKBracket.agda "$archive_root/bracket/fresh/final-source/"
cp -p /tmp/pts-rk-sk-source-final.yWoN0X/source/SKSourceEquality.agda "$archive_root/source-normal/final/final-source/"
cp -p /tmp/pts-rk-sk-source-final.yWoN0X/source/SKSourceNormal.agda "$archive_root/source-normal/final/final-source/"
for worker_attempt in /tmp/pts-rk-skbracket.Cjke1Y/snapshots/*; do
  [[ -d "$worker_attempt" ]] || continue
  worker_attempt_name=$(basename "$worker_attempt")
  mkdir -p "$archive_root/bracket/snapshots/$worker_attempt_name"
  cp -p "$worker_attempt"/*.agda "$archive_root/bracket/snapshots/$worker_attempt_name/"
done

# Keep exact raw text bytes when trimming trailing whitespace for Git review.
while IFS= read -r worker_log; do
  if LC_ALL=C grep -Eq '[[:blank:]]+$' "$worker_log"; then
    gzip -n -c "$worker_log" > "$worker_log.raw.gz"
    perl -pi -e 's/[\t ]+(?=\r?$)//' "$worker_log"
  fi
done < <(rg --files "$archive_root" -g '*.log' -g '*.txt')

cd "$archive_root"
rg --files -g '!archive.sha256' | LC_ALL=C sort | while IFS= read -r worker_file; do
  shasum -a 256 "$worker_file"
done > archive.sha256
