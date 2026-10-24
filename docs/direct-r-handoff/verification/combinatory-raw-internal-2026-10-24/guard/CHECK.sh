#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
IG_LOG=docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/guard
IG_TMP=/tmp/pts-rk-internal-guard.9aN6Rk
IG_BASE=/tmp/pts-rk-indexed-provenance.cjt8S0/default/theories
IG_ATTEMPT="$1"
cp theories/CombinatoryLogic-rk/MM0InternalGuard.v "$IG_TMP/MM0InternalGuard.v"
IG_ARGS=(rocq compile -Q "$IG_BASE" PTSrk -Q "$IG_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$IG_BASE/Interpretation_of_R" Interpretation_of_R -Q "$IG_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-indexed-transport.rdQzB4 PTSrk.Combinatory -Q /tmp/pts-rk-generated-codes.gGpVFd PTSrk.Combinatory -Q /tmp/pts-rk-finite-map-coherence.yhY8kT PTSrk.Combinatory -Q "$IG_TMP" PTSrk.Combinatory "$IG_TMP/MM0InternalGuard.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$IG_LOG/$IG_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${IG_ARGS[@]}" > "$IG_LOG/$IG_ATTEMPT.command"
printf '\n' >> "$IG_LOG/$IG_ATTEMPT.command"
shasum -a 256 "$IG_TMP/MM0InternalGuard.v" > "$IG_LOG/$IG_ATTEMPT.sha256"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${IG_ARGS[@]}" > "$IG_LOG/$IG_ATTEMPT.log" 2>&1
IG_RESULT=$?
printf '%s\n' "$IG_RESULT" > "$IG_LOG/$IG_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$IG_LOG/$IG_ATTEMPT.end"
cat "$IG_LOG/$IG_ATTEMPT.log"
exit "$IG_RESULT"
