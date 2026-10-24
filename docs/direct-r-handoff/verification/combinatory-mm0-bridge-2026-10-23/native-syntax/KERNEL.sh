#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
NS_LOG=docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/native-syntax
NS_TMP=/tmp/pts-rk-mm0-native-syntax.Lz2EQU
NS_BASE=/tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories
NS_ATTEMPT="${1:-kernel-final}"
NS_ARGS=(rocq check -silent -o -Q "$NS_BASE" PTSrk -Q "$NS_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$NS_BASE/Interpretation_of_R" Interpretation_of_R -Q "$NS_BASE/CombinatoryLogic-rk" PTSrk.Combinatory -Q /tmp/pts-rk-mm0-computational.3tS6OZ PTSrk.Combinatory -Q /tmp/pts-rk-mm0-catalogue.XiGatK PTSrk.Combinatory -Q /tmp/pts-rk-mm0-realization.8ricsy PTSrk.Combinatory -Q /tmp/pts-rk-mm0-syntax-algebra.UuB45x PTSrk.Combinatory -Q "$NS_TMP" PTSrk.Combinatory PTSrk.Combinatory.MM0HilbertAdequacy PTSrk.Combinatory.MM0NativeReduction PTSrk.Combinatory.MM0NativeSyntax)
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$NS_LOG/$NS_ATTEMPT.start"
printf '%q' /Users/akuklev/.local/share/pts-rk-ci/bin/opam > "$NS_LOG/$NS_ATTEMPT.command"
printf ' %q' exec -- "${NS_ARGS[@]}" >> "$NS_LOG/$NS_ATTEMPT.command"
printf '\n' >> "$NS_LOG/$NS_ATTEMPT.command"
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- "${NS_ARGS[@]}" > "$NS_LOG/$NS_ATTEMPT.log" 2>&1
NS_RESULT=$?
printf '%s\n' "$NS_RESULT" > "$NS_LOG/$NS_ATTEMPT.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$NS_LOG/$NS_ATTEMPT.end"
cat "$NS_LOG/$NS_ATTEMPT.log"
exit "$NS_RESULT"
