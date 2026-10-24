#!/usr/bin/env bash
set -u
build=/tmp/pts-rk-normal-families.0vT95x
trial="$build/check-$1"
mkdir -p "$trial/source" "$trial/data" "$trial/config"
cp /Users/akuklev/air/pts-rk/theories/CombinatoryLogic-rk/agda/*.agda "$trial/source/"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$trial/started.txt"
command_args=(/tmp/pts-rk-agda-2.8.0.MvVO53/agda +RTS -M2G -RTS --safe --no-default-libraries --ignore-interfaces -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i "$trial/source" "$trial/source/NormalizedFamilies.agda")
printf 'AGDA_DIR=%q XDG_DATA_HOME=%q ' "$trial/config" "$trial/data" > "$trial/command.txt"
printf '%q ' "${command_args[@]}" >> "$trial/command.txt"
printf '\n' >> "$trial/command.txt"
AGDA_DIR="$trial/config" XDG_DATA_HOME="$trial/data" "${command_args[@]}" > "$trial/check.log" 2>&1
status=$?
printf '%s\n' "$status" > "$trial/exit-code.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$trial/finished.txt"
tail -55 "$trial/check.log"
exit "$status"
