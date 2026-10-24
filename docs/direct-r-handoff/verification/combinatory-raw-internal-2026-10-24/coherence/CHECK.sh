#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
MC_LOG=docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/coherence
MC_TMP=/tmp/pts-rk-finite-map-coherence.yhY8kT
MC_BASE=/tmp/pts-rk-indexed-provenance.cjt8S0/default/theories
MC_ATTEMPT="$1"
cp theories/CombinatoryLogic-rk/FiniteMapCoherence.v "$MC_TMP/FiniteMapCoherence.v"
MC_ARGS=(rocq compile -Q "$MC_BASE" PTSrk -Q "$MC_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$MC_BASE/Interpretation_of_R" Interpretation_of_R -Q "$MC_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-indexed-transport.rdQzB4 PTSrk.Combinatory -Q /tmp/pts-rk-generated-codes.gGpVFd PTSrk.Combinatory -Q "$MC_TMP" PTSrk.Combinatory "$MC_TMP/FiniteMapCoherence.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$MC_LOG/$MC_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${MC_ARGS[@]}" > "$MC_LOG/$MC_ATTEMPT.command"
printf '\n' >> "$MC_LOG/$MC_ATTEMPT.command"
cp theories/CombinatoryLogic-rk/FiniteMapCoherence.v "$MC_LOG/$MC_ATTEMPT.source"
shasum -a 256 theories/CombinatoryLogic-rk/FiniteMapCoherence.v > "$MC_LOG/$MC_ATTEMPT.sha256"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${MC_ARGS[@]}" > "$MC_LOG/$MC_ATTEMPT.log" 2>&1
MC_RESULT=$?
printf '%s\n' "$MC_RESULT" > "$MC_LOG/$MC_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$MC_LOG/$MC_ATTEMPT.end"
cat "$MC_LOG/$MC_ATTEMPT.log"
exit "$MC_RESULT"
