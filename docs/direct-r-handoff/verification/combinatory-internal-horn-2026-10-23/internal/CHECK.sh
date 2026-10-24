#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
HI_LOG=docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/internal
HI_TMP=/tmp/pts-rk-horn-internal.VBqV4a
HI_BASE=/tmp/pts-rk-mm0-bridge.IH9mrh/default/theories
HI_ATTEMPT="$1"
HI_MODULE="${2:-HornInternalSoundness}"
cp "theories/CombinatoryLogic-rk/$HI_MODULE.v" "$HI_TMP/$HI_MODULE.v"
HI_ARGS=(rocq compile -Q "$HI_BASE" PTSrk -Q "$HI_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$HI_BASE/Interpretation_of_R" Interpretation_of_R -Q "$HI_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-horn-encoding.vF7hVq PTSrk.Combinatory -Q /tmp/pts-rk-horn-realization.GMs4GF PTSrk.Combinatory -Q /tmp/pts-rk-finite-support.Q1zQ9S PTSrk.Combinatory -Q "$HI_TMP" PTSrk.Combinatory "$HI_TMP/$HI_MODULE.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HI_LOG/$HI_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${HI_ARGS[@]}" > "$HI_LOG/$HI_ATTEMPT.command"
printf '\n' >> "$HI_LOG/$HI_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${HI_ARGS[@]}" > "$HI_LOG/$HI_ATTEMPT.log" 2>&1
HI_RESULT=$?
printf '%s\n' "$HI_RESULT" > "$HI_LOG/$HI_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HI_LOG/$HI_ATTEMPT.end"
cat "$HI_LOG/$HI_ATTEMPT.log"
exit "$HI_RESULT"
