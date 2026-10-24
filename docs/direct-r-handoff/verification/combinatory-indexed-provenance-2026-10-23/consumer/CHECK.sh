#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
IC_LOG=/tmp/pts-rk-indexed-consumer.qBciO2
IC_BASE=/tmp/pts-rk-internal-horn.6x5cr6/default/theories
IC_ATTEMPT="$1"
cp theories/CombinatoryLogic-rk/IndexedHornSoundness.v "$IC_LOG/IndexedHornSoundness.v"
IC_ARGS=(rocq compile -Q "$IC_BASE" PTSrk -Q "$IC_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$IC_BASE/Interpretation_of_R" Interpretation_of_R -Q "$IC_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-indexed-horn.MHrkIn PTSrk.Combinatory -Q /tmp/pts-rk-indexed-soundness.wHrIDF PTSrk.Combinatory -Q /tmp/pts-rk-indexed-realization.jvWMAx PTSrk.Combinatory -Q "$IC_LOG" PTSrk.Combinatory "$IC_LOG/IndexedHornSoundness.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$IC_LOG/$IC_ATTEMPT.start"
printf '%q' /Users/akuklev/.local/share/pts-rk-ci/bin/opam > "$IC_LOG/$IC_ATTEMPT.command"
printf ' %q' exec -- "${IC_ARGS[@]}" >> "$IC_LOG/$IC_ATTEMPT.command"
printf '\n' >> "$IC_LOG/$IC_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${IC_ARGS[@]}" > "$IC_LOG/$IC_ATTEMPT.log" 2>&1
IC_RESULT=$?
printf '%s\n' "$IC_RESULT" > "$IC_LOG/$IC_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$IC_LOG/$IC_ATTEMPT.end"
cat "$IC_LOG/$IC_ATTEMPT.log"
exit "$IC_RESULT"
