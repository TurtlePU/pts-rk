#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
GRAPH_WORK=/tmp/pts-rk-graph-realization.JR1tPK
GRAPH_BASE=/tmp/pts-rk-joint-resources-fresh.TqBIPV/default/theories
GRAPH_LABEL="${1:?attempt label required}"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$GRAPH_WORK/$GRAPH_LABEL.start"
shasum -a 256 theories/self_consistency/CheckerGraphRealization.v > "$GRAPH_WORK/$GRAPH_LABEL.source"
GRAPH_COMMAND=(opam exec -- timeout 300 rocq compile -time
  -Q "$GRAPH_BASE" PTSrk
  -Q "$GRAPH_BASE/Interpretation_of_R" Interpretation_of_R
  -Q "$GRAPH_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$GRAPH_BASE/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$GRAPH_BASE/self_consistency" PTSrk.SelfConsistency
  -Q /tmp/pts-rk-source-graph.Ovrq0T PTSrk.SelfConsistency
  -Q /tmp/pts-rk-operation-graph.ouqvvt PTSrk.SelfConsistency
  -Q "$GRAPH_WORK" PTSrk.SelfConsistency
  -o "$GRAPH_WORK/CheckerGraphRealization.vo"
  theories/self_consistency/CheckerGraphRealization.v)
printf '%q ' "${GRAPH_COMMAND[@]}" > "$GRAPH_WORK/$GRAPH_LABEL.command"
printf '\n' >> "$GRAPH_WORK/$GRAPH_LABEL.command"
"${GRAPH_COMMAND[@]}" > "$GRAPH_WORK/$GRAPH_LABEL.log" 2>&1
GRAPH_EXIT=$?
printf '%s\n' "$GRAPH_EXIT" > "$GRAPH_WORK/$GRAPH_LABEL.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$GRAPH_WORK/$GRAPH_LABEL.end"
tail -n 35 "$GRAPH_WORK/$GRAPH_LABEL.log"
exit "$GRAPH_EXIT"
