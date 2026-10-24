#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
DEC_LOG=docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/decoder
DEC_TMP=/tmp/pts-rk-mm0-internal-decoder.3D2W4B
DEC_BASE=/tmp/pts-rk-indexed-provenance.cjt8S0/default/theories
DEC_ATTEMPT="$1"
cp theories/CombinatoryLogic-rk/MM0InternalDecoder.v "$DEC_TMP/MM0InternalDecoder.v"
DEC_ARGS=(rocq compile -Q "$DEC_BASE" PTSrk -Q "$DEC_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$DEC_BASE/Interpretation_of_R" Interpretation_of_R -Q "$DEC_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-indexed-transport.rdQzB4 PTSrk.Combinatory -Q "$DEC_TMP" PTSrk.Combinatory "$DEC_TMP/MM0InternalDecoder.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$DEC_LOG/$DEC_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${DEC_ARGS[@]}" > "$DEC_LOG/$DEC_ATTEMPT.command"
printf '\n' >> "$DEC_LOG/$DEC_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${DEC_ARGS[@]}" > "$DEC_LOG/$DEC_ATTEMPT.log" 2>&1
DEC_RESULT=$?
printf '%s\n' "$DEC_RESULT" > "$DEC_LOG/$DEC_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$DEC_LOG/$DEC_ATTEMPT.end"
cat "$DEC_LOG/$DEC_ATTEMPT.log"
exit "$DEC_RESULT"
