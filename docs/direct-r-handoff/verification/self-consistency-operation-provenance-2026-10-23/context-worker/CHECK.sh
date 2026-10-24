#!/usr/bin/env bash
set -u
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
worker=/tmp/pts-rk-context-lookup.9QUeXr
fresh=/tmp/pts-rk-source-provenance-fresh.yW2QOO/default/theories
attempt=${1:?attempt identifier required}
cd /Users/akuklev/air/pts-rk || exit
date -u +%FT%TZ > "$worker/$attempt.start"
shasum -a 256 theories/self_consistency/InternalContextLookup.v > "$worker/$attempt.source"
command=(opam exec -- timeout 600 rocq compile -time
  -Q "$fresh" PTSrk
  -Q "$fresh/Interpretation_of_R" Interpretation_of_R
  -Q "$fresh/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$fresh/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$worker/dependency-links" PTSrk.SelfConsistency
  -Q "$fresh/self_consistency" PTSrk.SelfConsistency
  -Q /tmp/pts-rk-context-provenance.pPeQ4L PTSrk.SelfConsistency
  -Q theories/self_consistency PTSrk.SelfConsistency
  -Q "$worker" PTSrk.SelfConsistency
  -o "$worker/InternalContextLookup.vo"
  theories/self_consistency/InternalContextLookup.v)
printf '%q ' "${command[@]}" > "$worker/$attempt.command"
printf '\n' >> "$worker/$attempt.command"
"${command[@]}" > "$worker/$attempt.log" 2>&1
result=$?
printf '%s\n' "$result" > "$worker/$attempt.exit"
date -u +%FT%TZ > "$worker/$attempt.end"
tail -n 50 "$worker/$attempt.log"
exit "$result"
