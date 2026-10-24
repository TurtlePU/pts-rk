#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
MC_LOG=docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/coherence
MC_TMP=/tmp/pts-rk-finite-map-coherence.yhY8kT
MC_BASE=/tmp/pts-rk-indexed-provenance.cjt8S0/default/theories
MC_ARGS=(rocq check -silent -o -Q "$MC_BASE" PTSrk -Q "$MC_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$MC_BASE/Interpretation_of_R" Interpretation_of_R -Q "$MC_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-indexed-transport.rdQzB4 PTSrk.Combinatory -Q /tmp/pts-rk-generated-codes.gGpVFd PTSrk.Combinatory -Q "$MC_TMP" PTSrk.Combinatory PTSrk.Combinatory.FiniteMapCoherence)
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$MC_LOG/kernel.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${MC_ARGS[@]}" > "$MC_LOG/kernel.command"
printf '\n' >> "$MC_LOG/kernel.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${MC_ARGS[@]}" > "$MC_LOG/kernel.log" 2>&1
MC_RESULT=$?
printf '%s\n' "$MC_RESULT" > "$MC_LOG/kernel.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$MC_LOG/kernel.end"
cat "$MC_LOG/kernel.log"
exit "$MC_RESULT"
