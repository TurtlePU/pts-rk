#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
FG_LOG=docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/generated
FG_TMP=/tmp/pts-rk-generated-codes.gGpVFd
FG_BASE=/tmp/pts-rk-indexed-provenance.cjt8S0/default/theories
FG_ARGS=(rocq check -silent -o -Q "$FG_BASE" PTSrk -Q "$FG_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$FG_BASE/Interpretation_of_R" Interpretation_of_R -Q "$FG_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q "$FG_TMP" PTSrk.Combinatory PTSrk.Combinatory.FiniteGeneratedCodes)
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$FG_LOG/kernel.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${FG_ARGS[@]}" > "$FG_LOG/kernel.command"
printf '\n' >> "$FG_LOG/kernel.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${FG_ARGS[@]}" > "$FG_LOG/kernel.log" 2>&1
FG_RESULT=$?
printf '%s\n' "$FG_RESULT" > "$FG_LOG/kernel.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$FG_LOG/kernel.end"
cat "$FG_LOG/kernel.log"
if [ "$FG_RESULT" -ne 0 ]; then exit "$FG_RESULT"; fi
awk '/^CONTEXT SUMMARY$/ {report=1} report' "$FG_LOG/kernel.log" > "$FG_LOG/inventory.txt"
diff -u docs/direct-r-handoff/verification/combinatory-indexed-provenance-2026-10-23/audit.emobKi/upstream-inventory.txt "$FG_LOG/inventory.txt" > "$FG_LOG/inventory-compare.log"
FG_RESULT=$?
printf '%s\n' "$FG_RESULT" > "$FG_LOG/inventory-compare.exit"
shasum -a 256 theories/CombinatoryLogic-rk/FiniteGeneratedCodes.v > "$FG_LOG/source.sha256"
exit "$FG_RESULT"
