#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
HE_LOG=docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/encoding
HE_TMP=/tmp/pts-rk-horn-encoding.vF7hVq
HE_BASE=/tmp/pts-rk-mm0-bridge.IH9mrh/default/theories
HE_ATTEMPT="${1:-kernel-final}"
HE_ARGS=(rocq check -silent -o -Q "$HE_BASE" PTSrk -Q "$HE_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$HE_BASE/Interpretation_of_R" Interpretation_of_R -Q "$HE_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q "$HE_TMP" PTSrk.Combinatory PTSrk.Combinatory.HornProofEncoding)
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HE_LOG/$HE_ATTEMPT.start"
printf '%q' /Users/akuklev/.local/share/pts-rk-ci/bin/opam > "$HE_LOG/$HE_ATTEMPT.command"
printf ' %q' exec -- "${HE_ARGS[@]}" >> "$HE_LOG/$HE_ATTEMPT.command"
printf '\n' >> "$HE_LOG/$HE_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${HE_ARGS[@]}" > "$HE_LOG/$HE_ATTEMPT.log" 2>&1
HE_RESULT=$?
printf '%s\n' "$HE_RESULT" > "$HE_LOG/$HE_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HE_LOG/$HE_ATTEMPT.end"
cat "$HE_LOG/$HE_ATTEMPT.log"
exit "$HE_RESULT"
