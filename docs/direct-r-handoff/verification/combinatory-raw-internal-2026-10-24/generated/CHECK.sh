#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
FG_LOG=docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/generated
FG_TMP=/tmp/pts-rk-generated-codes.gGpVFd
FG_BASE=/tmp/pts-rk-indexed-provenance.cjt8S0/default/theories
FG_ATTEMPT="$1"
cp theories/CombinatoryLogic-rk/FiniteGeneratedCodes.v "$FG_TMP/FiniteGeneratedCodes.v"
FG_ARGS=(rocq compile -Q "$FG_BASE" PTSrk -Q "$FG_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$FG_BASE/Interpretation_of_R" Interpretation_of_R -Q "$FG_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q "$FG_TMP" PTSrk.Combinatory "$FG_TMP/FiniteGeneratedCodes.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$FG_LOG/$FG_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${FG_ARGS[@]}" > "$FG_LOG/$FG_ATTEMPT.command"
printf '\n' >> "$FG_LOG/$FG_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${FG_ARGS[@]}" > "$FG_LOG/$FG_ATTEMPT.log" 2>&1
FG_RESULT=$?
printf '%s\n' "$FG_RESULT" > "$FG_LOG/$FG_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$FG_LOG/$FG_ATTEMPT.end"
cat "$FG_LOG/$FG_ATTEMPT.log"
exit "$FG_RESULT"
