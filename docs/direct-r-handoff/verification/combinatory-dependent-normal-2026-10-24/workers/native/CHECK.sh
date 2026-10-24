#!/usr/bin/env bash
set -u
root=/Users/akuklev/air/pts-rk
evidence=/tmp/pts-rk-native-inference.MkNbTu
attempt=$1
run="$evidence/$attempt"
mkdir -p "$run/source" "$run/config" "$run/data"
cp "$root"/theories/CombinatoryLogic-rk/agda/*.agda "$run/source/"
shasum -a 256 "$run"/source/*.agda > "$run/sources.sha256"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$run/started.txt"
export AGDA_DIR="$run/config"
export XDG_DATA_HOME="$run/data"
args=(/tmp/pts-rk-agda-2.8.0.MvVO53/agda +RTS -M2G -RTS --safe --no-default-libraries --ignore-interfaces
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i "$run/source" "$run/source/NativeBidirectional.agda")
printf '%q ' "${args[@]}" > "$run/command.txt"
printf '\n' >> "$run/command.txt"
"${args[@]}" > "$run/check.log" 2>&1
status=$?
printf '%s\n' "$status" > "$run/exit-code.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$run/finished.txt"
tail -60 "$run/check.log"
exit "$status"
