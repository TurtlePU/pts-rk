#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
FG_LOG=docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/generated
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$FG_LOG/inventory-raw.start"
FG_ARGS=(diff -u _build/combinatory-indexed-provenance-audit.rya6B6/upstream-inventory.txt "$FG_LOG/inventory.txt")
printf '%q ' "${FG_ARGS[@]}" > "$FG_LOG/inventory-raw.command"
printf '\n' >> "$FG_LOG/inventory-raw.command"
"${FG_ARGS[@]}" > "$FG_LOG/inventory-raw.log"
FG_RESULT=$?
printf '%s\n' "$FG_RESULT" > "$FG_LOG/inventory-raw.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$FG_LOG/inventory-raw.end"
exit "$FG_RESULT"
