#!/usr/bin/env bash
set -u
evidence=/Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/combinatory-paper-plan-2026-10-24/inspection
inspector=/Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/combinatory-dependent-normal-2026-10-24/inspect.swift
pdf=/Users/akuklev/air/pts-rk/theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf
images=$(mktemp -d /tmp/pts-rk-paper-plan-pdf.XXXXXX)
printf '%s\n' "$images" > "$evidence/image-directory.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence/started.txt"
shasum -a 256 "$pdf" > "$evidence/pdf-before.sha256"
shasum -a 256 "$inspector" > "$evidence/inspector.sha256"
command_args=(swift "$inspector" "$pdf" "$images")
printf '%q' "${command_args[0]}" > "$evidence/command.txt"
printf ' %q' "${command_args[@]:1}" >> "$evidence/command.txt"
printf '\n' >> "$evidence/command.txt"
"${command_args[@]}" > "$evidence/inspection.log" 2>&1
status=$?
printf '%s\n' "$status" > "$evidence/exit-code.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence/finished.txt"
shasum -a 256 -c "$evidence/pdf-before.sha256" > "$evidence/pdf-stability.log" 2>&1
for item in pdf-text.txt pdf-links.txt; do
  if test -f "$images/$item"; then
    cp "$images/$item" "$evidence/$item"
  fi
done
tail -35 "$evidence/inspection.log"
exit "$status"
