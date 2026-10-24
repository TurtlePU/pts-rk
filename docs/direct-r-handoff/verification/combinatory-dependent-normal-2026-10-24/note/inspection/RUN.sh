#!/usr/bin/env bash
set -u
out=/tmp/pts-rk-dependent-normal-pdf.Mz2e0Y
inspector=/Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/combinatory-dependent-normal-2026-10-24/inspect.swift
pdf=/Users/akuklev/air/pts-rk/theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$out/started.txt"
command_args=(swift "$inspector" "$pdf" "$out")
printf '%q ' "${command_args[@]}" > "$out/command.txt"
printf '\n' >> "$out/command.txt"
"${command_args[@]}" > "$out/inspection.log" 2>&1
status=$?
printf '%s\n' "$status" > "$out/exit-code.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$out/finished.txt"
tail -35 "$out/inspection.log"
exit "$status"
