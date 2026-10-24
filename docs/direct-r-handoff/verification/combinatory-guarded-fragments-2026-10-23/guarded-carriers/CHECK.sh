#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
GC_LOG=docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/guarded-carriers
GC_TMP=/tmp/pts-rk-guarded-carriers.mPsQdQ
GC_BASE=/tmp/pts-rk-quantified-models.uhpkYv/default/theories
GC_ATTEMPT="$1"
cp theories/CombinatoryLogic-rk/GuardedFiniteCarriers.v "$GC_TMP/GuardedFiniteCarriers.v"
GC_ARGS=(rocq compile -Q "$GC_BASE" PTSrk -Q "$GC_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$GC_BASE/Interpretation_of_R" Interpretation_of_R -Q "$GC_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q "$GC_TMP" PTSrk.Combinatory "$GC_TMP/GuardedFiniteCarriers.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$GC_LOG/$GC_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${GC_ARGS[@]}" > "$GC_LOG/$GC_ATTEMPT.command"
printf '\n' >> "$GC_LOG/$GC_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${GC_ARGS[@]}" > "$GC_LOG/$GC_ATTEMPT.log" 2>&1
GC_RESULT=$?
printf '%s\n' "$GC_RESULT" > "$GC_LOG/$GC_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$GC_LOG/$GC_ATTEMPT.end"
cat "$GC_LOG/$GC_ATTEMPT.log"
exit "$GC_RESULT"
