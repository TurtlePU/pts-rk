#!/usr/bin/env bash
set -u
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
repo=/Users/akuklev/air/pts-rk
worker=/tmp/pts-rk-source-graph.Ovrq0T
fresh=/tmp/pts-rk-joint-resources-fresh.TqBIPV/default/theories
attempt=${1:?attempt identifier required}
cd "$repo" || exit
date -u +%FT%TZ > "$worker/$attempt.start"
shasum -a 256 theories/self_consistency/CheckerSourceGraph.v > "$worker/$attempt.source"
command=(opam exec -- timeout 300 rocq compile
  -Q "$fresh" PTSrk
  -Q "$fresh/Interpretation_of_R" Interpretation_of_R
  -Q "$fresh/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$fresh/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$fresh/self_consistency" PTSrk.SelfConsistency
  -Q theories/self_consistency PTSrk.SelfConsistency
  -Q "$worker" PTSrk.SelfConsistency
  -o "$worker/CheckerSourceGraph.vo"
  theories/self_consistency/CheckerSourceGraph.v)
printf '%q ' "${command[@]}" > "$worker/$attempt.command"
printf '\n' >> "$worker/$attempt.command"
"${command[@]}" > "$worker/$attempt.log" 2>&1
result=$?
printf '%s\n' "$result" > "$worker/$attempt.exit"
date -u +%FT%TZ > "$worker/$attempt.end"
tail -n 50 "$worker/$attempt.log"
exit "$result"
