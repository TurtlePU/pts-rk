#!/usr/bin/env bash
set -uo pipefail
root=/Users/akuklev/air/pts-rk
evidence=/tmp/pts-rk-normal-comprehension.xFZ3o4
run="$evidence/$1"
mkdir -p "$run/source" "$run/config" "$run/data"
cp "$root"/theories/CombinatoryLogic-rk/agda/*.agda "$run/source/"
shasum -a 256 "$run/source"/*.agda > "$run/source.sha256"
export AGDA_DIR="$run/config" XDG_DATA_HOME="$run/data"
args=(/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces
 -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i "$run/source"
 "$run/source/NormalizedComprehension.agda" +RTS -M2G -RTS)
printf '%q ' "${args[@]}" > "$run/command.txt"
printf '\n' >> "$run/command.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$run/started.txt"
"${args[@]}" > "$run/check.log" 2>&1
code=$?
printf '%s\n' "$code" > "$run/exit-code.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$run/finished.txt"
tail -60 "$run/check.log"
exit "$code"
