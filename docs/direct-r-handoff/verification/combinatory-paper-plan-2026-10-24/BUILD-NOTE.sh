#!/usr/bin/env bash
# Documentation-only build; no proof sources or proof-development commands.
set -euo pipefail
evidence_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_dir=$(cd "$evidence_dir/../../../.." && pwd)
cd "$project_dir"
baseline=docs/direct-r-handoff/verification/combinatory-dependent-normal-2026-10-24/final-sources.sha256
awk '$2 ~ /\.v$/ || $2 ~ /\.agda$/ || $2 ~ /\/dune$/ || $2 ~ /\.mm0$/ || $2 ~ /\/check-agda.sh$/ || $2 ~ /\/build-note.sh$/' \
  "$baseline" > "$evidence_dir/unchanged-proof-sources.sha256"
shasum -a 256 -c "$evidence_dir/unchanged-proof-sources.sha256" \
  > "$evidence_dir/unchanged-proof-sources.log"
printf '%s\n' 'bash theories/CombinatoryLogic-rk/build-note.sh' > "$evidence_dir/command.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence_dir/started.txt"
set +e
bash theories/CombinatoryLogic-rk/build-note.sh > "$evidence_dir/driver.log" 2>&1
status=$?
set -e
printf '%s\n' "$status" > "$evidence_dir/exit.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence_dir/finished.txt"
cat "$evidence_dir/driver.log"
if [[ "$status" != 0 ]]; then exit "$status"; fi
build_dir=$(sed -n 's/^Build directory: //p' "$evidence_dir/driver.log")
for item in build.log CombinatoryPTS-rk.log versions.log command.txt \
  started.txt finished.txt build-exit-code.txt validation-exit-code.txt; do
  cp "$build_dir/$item" "$evidence_dir/build-$item"
done
printf '%s\n' "$build_dir" > "$evidence_dir/build-directory.txt"
shasum -a 256 -c "$evidence_dir/unchanged-proof-sources.sha256" \
  > "$evidence_dir/final-proof-source-stability.log"
