#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
IC_LOG=/tmp/pts-rk-indexed-consumer.qBciO2
IC_BASE=/tmp/pts-rk-internal-horn.6x5cr6/default/theories
IC_ARGS=(rocq check -silent -o -Q "$IC_BASE" PTSrk -Q "$IC_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$IC_BASE/Interpretation_of_R" Interpretation_of_R -Q "$IC_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-indexed-horn.MHrkIn PTSrk.Combinatory -Q /tmp/pts-rk-indexed-soundness.wHrIDF PTSrk.Combinatory -Q /tmp/pts-rk-indexed-realization.jvWMAx PTSrk.Combinatory -Q "$IC_LOG" PTSrk.Combinatory PTSrk.Combinatory.IndexedHornSoundness)
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$IC_LOG/kernel.start"
printf '%q' /Users/akuklev/.local/share/pts-rk-ci/bin/opam > "$IC_LOG/kernel.command"
printf ' %q' exec -- "${IC_ARGS[@]}" >> "$IC_LOG/kernel.command"
printf '\n' >> "$IC_LOG/kernel.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${IC_ARGS[@]}" > "$IC_LOG/kernel.log" 2>&1
IC_RESULT=$?
printf '%s\n' "$IC_RESULT" > "$IC_LOG/kernel.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$IC_LOG/kernel.end"
cat "$IC_LOG/kernel.log"
exit "$IC_RESULT"
