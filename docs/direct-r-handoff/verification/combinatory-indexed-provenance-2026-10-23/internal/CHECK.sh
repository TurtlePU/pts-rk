#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
IP_LOG=docs/direct-r-handoff/verification/combinatory-indexed-provenance-2026-10-23/internal
IP_TMP=/tmp/pts-rk-indexed-soundness.wHrIDF
IP_BASE=/tmp/pts-rk-internal-horn.6x5cr6/default/theories
IP_ATTEMPT="$1"
IP_MODULE="${2:-FiniteTypeDispatch}"
cp "theories/CombinatoryLogic-rk/$IP_MODULE.v" "$IP_TMP/$IP_MODULE.v"
IP_ARGS=(rocq compile -Q "$IP_BASE" PTSrk -Q "$IP_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$IP_BASE/Interpretation_of_R" Interpretation_of_R -Q "$IP_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-indexed-horn.MHrkIn PTSrk.Combinatory -Q /tmp/pts-rk-indexed-realization.jvWMAx PTSrk.Combinatory -Q "$IP_TMP" PTSrk.Combinatory "$IP_TMP/$IP_MODULE.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$IP_LOG/$IP_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${IP_ARGS[@]}" > "$IP_LOG/$IP_ATTEMPT.command"
printf '\n' >> "$IP_LOG/$IP_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${IP_ARGS[@]}" > "$IP_LOG/$IP_ATTEMPT.log" 2>&1
IP_RESULT=$?
printf '%s\n' "$IP_RESULT" > "$IP_LOG/$IP_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$IP_LOG/$IP_ATTEMPT.end"
cat "$IP_LOG/$IP_ATTEMPT.log"
exit "$IP_RESULT"
