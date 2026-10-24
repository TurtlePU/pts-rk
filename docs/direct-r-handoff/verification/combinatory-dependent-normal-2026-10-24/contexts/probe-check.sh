#!/usr/bin/env bash
set -u
build=/tmp/pts-rk-normal-contexts.KPvTCg
trial="$build/probe-$1"
mkdir -p "$trial"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$trial/started.txt"
command_args=(/tmp/pts-rk-agda-2.8.0.MvVO53/agda +RTS -M2G -RTS --safe --no-default-libraries -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i "$build/check-04-core/source" "$build/check-04-core/source/$2.agda")
printf 'AGDA_DIR=%q XDG_DATA_HOME=%q ' "$build/check-04-core/config" "$build/check-04-core/data" > "$trial/command.txt"
printf '%q ' "${command_args[@]}" >> "$trial/command.txt"
printf '\n' >> "$trial/command.txt"
AGDA_DIR="$build/check-04-core/config" XDG_DATA_HOME="$build/check-04-core/data" "${command_args[@]}" > "$trial/check.log" 2>&1
status=$?
printf '%s\n' "$status" > "$trial/exit-code.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$trial/finished.txt"
tail -55 "$trial/check.log"
exit "$status"
