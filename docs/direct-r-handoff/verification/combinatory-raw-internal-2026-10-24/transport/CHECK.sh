#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
TR_LOG=docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/transport
TR_TMP=/tmp/pts-rk-indexed-transport.rdQzB4
TR_BASE=/tmp/pts-rk-indexed-provenance.cjt8S0/default/theories
TR_ATTEMPT="$1"
cp theories/CombinatoryLogic-rk/IndexedHornTransport.v "$TR_TMP/IndexedHornTransport.v"
TR_ARGS=(rocq compile -Q "$TR_BASE" PTSrk -Q "$TR_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$TR_BASE/Interpretation_of_R" Interpretation_of_R -Q "$TR_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q "$TR_TMP" PTSrk.Combinatory "$TR_TMP/IndexedHornTransport.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$TR_LOG/$TR_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${TR_ARGS[@]}" > "$TR_LOG/$TR_ATTEMPT.command"
printf '\n' >> "$TR_LOG/$TR_ATTEMPT.command"
cp theories/CombinatoryLogic-rk/IndexedHornTransport.v "$TR_LOG/$TR_ATTEMPT.source"
shasum -a 256 theories/CombinatoryLogic-rk/IndexedHornTransport.v > "$TR_LOG/$TR_ATTEMPT.sha256"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${TR_ARGS[@]}" > "$TR_LOG/$TR_ATTEMPT.log" 2>&1
TR_RESULT=$?
printf '%s\n' "$TR_RESULT" > "$TR_LOG/$TR_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$TR_LOG/$TR_ATTEMPT.end"
cat "$TR_LOG/$TR_ATTEMPT.log"
exit "$TR_RESULT"
