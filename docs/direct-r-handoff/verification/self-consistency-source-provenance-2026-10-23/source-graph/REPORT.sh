#!/usr/bin/env bash
set -u
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
worker=/tmp/pts-rk-source-graph.Ovrq0T
fresh=/tmp/pts-rk-joint-resources-fresh.TqBIPV/default/theories
cd /Users/akuklev/air/pts-rk || exit
date -u +%FT%TZ > "$worker/report.start"
command=(opam exec -- timeout 300 rocq compile
  -Q "$fresh" PTSrk
  -Q "$fresh/Interpretation_of_R" Interpretation_of_R
  -Q "$fresh/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$fresh/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$fresh/self_consistency" PTSrk.SelfConsistency
  -Q "$worker" PTSrk.SelfConsistency
  "$worker/Report.v")
printf '%q ' "${command[@]}" > "$worker/report.command"
printf '\n' >> "$worker/report.command"
"${command[@]}" > "$worker/report.log" 2>&1
result=$?
printf '%s\n' "$result" > "$worker/report.exit"
date -u +%FT%TZ > "$worker/report.end"
tail -n 20 "$worker/report.log"
exit "$result"
