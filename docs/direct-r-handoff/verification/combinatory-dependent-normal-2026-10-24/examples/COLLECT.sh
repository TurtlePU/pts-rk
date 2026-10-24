#!/usr/bin/env bash
# Preserve exact diagnostics and selected source snapshots, not generated caches.
set -euo pipefail
source_dir=/tmp/pts-rk-normal-examples.LRVW14
archive_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
cp "$source_dir/check.sh" "$archive_dir/check.sh"
cp "$source_dir/COMMANDS.md" "$archive_dir/COMMANDS.md"
cp "$source_dir/QIIRT-review.md" "$archive_dir/QIIRT-review.md"
cp "$source_dir/NeutralProbe.agda" "$archive_dir/NeutralProbe.agda"
for run in "$source_dir"/check[0-9][0-9]; do
  run_name=$(basename "$run")
  mkdir -p "$archive_dir/$run_name/source"
  for artifact in started.txt finished.txt exit-code.txt check.log source.sha256; do
    if [[ -f "$run/$artifact" ]]; then
      cp "$run/$artifact" "$archive_dir/$run_name/$artifact"
    fi
  done
  gzip -c "$run/command.txt" > "$archive_dir/$run_name/command.raw.txt.gz"
  sed 's/[[:blank:]]*$//' "$run/command.txt" > "$archive_dir/$run_name/command.txt"
  for module in NormalizedExamples NeutralProbe NormalizedFamilies NormalizedComprehension NormalizedProducts NormalizedInference NormalizedContexts; do
    if [[ -f "$run/source/$module.agda" ]]; then
      cp "$run/source/$module.agda" "$archive_dir/$run_name/source/$module.agda"
    fi
  done
done
cd "$archive_dir"
find . -type f ! -name archive.sha256 -print | LC_ALL=C sort | while IFS= read -r file; do
  shasum -a 256 "$file"
done > archive.sha256
shasum -a 256 -c archive.sha256
