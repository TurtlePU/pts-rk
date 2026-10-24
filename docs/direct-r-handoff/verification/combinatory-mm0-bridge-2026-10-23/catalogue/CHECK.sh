#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
MC_LOG=docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/catalogue
MC_TMP=/tmp/pts-rk-mm0-catalogue.XiGatK
MC_BASE=/tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories
MC_ATTEMPT="$1"
cp theories/CombinatoryLogic-rk/MM0CatalogueAdequacy.v "$MC_TMP/MM0CatalogueAdequacy.v"
MC_ARGS=(rocq compile -Q "$MC_BASE" PTSrk -Q "$MC_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$MC_BASE/Interpretation_of_R" Interpretation_of_R -Q "$MC_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-mm0-native-syntax.Lz2EQU PTSrk.Combinatory -Q /tmp/pts-rk-mm0-computational.3tS6OZ PTSrk.Combinatory -Q "$MC_TMP" PTSrk.Combinatory "$MC_TMP/MM0CatalogueAdequacy.v")
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$MC_LOG/$MC_ATTEMPT.start"
printf '%q ' /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${MC_ARGS[@]}" > "$MC_LOG/$MC_ATTEMPT.command"
printf '\n' >> "$MC_LOG/$MC_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${MC_ARGS[@]}" > "$MC_LOG/$MC_ATTEMPT.log" 2>&1
MC_RESULT=$?
printf '%s\n' "$MC_RESULT" > "$MC_LOG/$MC_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$MC_LOG/$MC_ATTEMPT.end"
cat "$MC_LOG/$MC_ATTEMPT.log"
exit "$MC_RESULT"
