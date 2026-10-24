#!/usr/bin/env bash
set -uo pipefail
attempt=$1
task_dir=/tmp/pts-rk-normal-products.5ZaaRR
project_dir=/Users/akuklev/air/pts-rk
mkdir -p "$task_dir/source" "$task_dir/config" "$task_dir/data"
cp "$project_dir"/theories/CombinatoryLogic-rk/agda/*.agda "$task_dir/source/"
if [[ ${3:-} == probe ]]; then
  cp "$task_dir/probe-core.agda" "$task_dir/source/NormalizedProducts.agda"
fi
if [[ ${3:-} == probe-type ]]; then
  cp "$task_dir/probe-type.agda" "$task_dir/source/NormalizedProducts.agda"
fi
cp "$task_dir/source/NormalizedProducts.agda" "$task_dir/attempt-$attempt.agda"
shasum -a 256 "$task_dir/source"/*.agda > "$task_dir/check-$attempt.sources.sha256"
args=(/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i "$task_dir/source"
  "$task_dir/source/NormalizedProducts.agda" +RTS -M2G -RTS)
if [[ ${2:-} == fresh ]]; then
  args=(/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces
    -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i "$task_dir/source"
    "$task_dir/source/NormalizedProducts.agda" +RTS -M2G -RTS)
fi
printf '%q ' "${args[@]}" > "$task_dir/check-$attempt.command.txt"
printf '\n' >> "$task_dir/check-$attempt.command.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$task_dir/check-$attempt.started.txt"
AGDA_DIR="$task_dir/config" XDG_DATA_HOME="$task_dir/data" \
  "${args[@]}" > "$task_dir/check-$attempt.log" 2>&1
status=$?
printf '%s\n' "$status" > "$task_dir/check-$attempt.exit.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$task_dir/check-$attempt.finished.txt"
tail -35 "$task_dir/check-$attempt.log"
exit "$status"
