#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
GH_LOG=docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/guarded-hilbert
GH_TMP=/tmp/pts-rk-guarded-hilbert.ZjBk3c
GH_BASE=/tmp/pts-rk-quantified-models.uhpkYv/default/theories
GH_ARGS=(rocq check -silent -o -Q "$GH_BASE" PTSrk -Q "$GH_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$GH_BASE/Interpretation_of_R" Interpretation_of_R -Q "$GH_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-guarded-carriers.mPsQdQ PTSrk.Combinatory -Q /tmp/pts-rk-guarded-horn.VJZbDb PTSrk.Combinatory -Q "$GH_TMP" PTSrk.Combinatory PTSrk.Combinatory.GuardedHilbertModels)
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$GH_LOG/kernel.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${GH_ARGS[@]}" > "$GH_LOG/kernel.command"
printf '\n' >> "$GH_LOG/kernel.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${GH_ARGS[@]}" > "$GH_LOG/kernel.log" 2>&1
GH_RESULT=$?
printf '%s\n' "$GH_RESULT" > "$GH_LOG/kernel.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$GH_LOG/kernel.end"
cat "$GH_LOG/kernel.log"
exit "$GH_RESULT"
