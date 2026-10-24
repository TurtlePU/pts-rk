#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
MR_LOG=docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/realization
MR_TMP=/tmp/pts-rk-mm0-realization.8ricsy
MR_BASE=/tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories
MR_ARGS=(rocq check -silent -o -Q "$MR_BASE" PTSrk -Q "$MR_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$MR_BASE/Interpretation_of_R" Interpretation_of_R -Q "$MR_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-mm0-native-syntax.Lz2EQU PTSrk.Combinatory -Q /tmp/pts-rk-mm0-computational.3tS6OZ PTSrk.Combinatory -Q /tmp/pts-rk-mm0-catalogue.XiGatK PTSrk.Combinatory -Q "$MR_TMP" PTSrk.Combinatory PTSrk.Combinatory.MM0CatalogueRealization)
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$MR_LOG/kernel.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${MR_ARGS[@]}" > "$MR_LOG/kernel.command"
printf '\n' >> "$MR_LOG/kernel.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${MR_ARGS[@]}" > "$MR_LOG/kernel.log" 2>&1
MR_RESULT=$?
printf '%s\n' "$MR_RESULT" > "$MR_LOG/kernel.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$MR_LOG/kernel.end"
cat "$MR_LOG/kernel.log"
exit "$MR_RESULT"
