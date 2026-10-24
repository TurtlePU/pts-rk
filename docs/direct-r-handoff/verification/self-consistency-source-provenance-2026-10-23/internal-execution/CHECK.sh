#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
GRAPH_TMP=/tmp/pts-rk-operation-graph.ouqvvt
GRAPH_BASE=/tmp/pts-rk-joint-resources-fresh.TqBIPV/default/theories
GRAPH_LABEL="${1:-attempt-01}"
GRAPH_SOURCE="${2:-$GRAPH_TMP/InternalExecutionGraph.v}"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$GRAPH_TMP/$GRAPH_LABEL.start"
shasum -a 256 "$GRAPH_SOURCE" > "$GRAPH_TMP/$GRAPH_LABEL.source"
GRAPH_COMMAND=(opam exec -- timeout 300 rocq compile -time
  -Q "$GRAPH_BASE" PTSrk
  -Q "$GRAPH_BASE/Interpretation_of_R" Interpretation_of_R
  -Q "$GRAPH_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$GRAPH_BASE/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$GRAPH_BASE/self_consistency" PTSrk.SelfConsistency
  -Q "$GRAPH_TMP" PTSrk.SelfConsistency
  -o "$GRAPH_TMP/$(basename "$GRAPH_SOURCE" .v).vo" "$GRAPH_SOURCE")
printf '%q ' "${GRAPH_COMMAND[@]}" > "$GRAPH_TMP/$GRAPH_LABEL.command"
printf '\n' >> "$GRAPH_TMP/$GRAPH_LABEL.command"
"${GRAPH_COMMAND[@]}" > "$GRAPH_TMP/$GRAPH_LABEL.log" 2>&1
GRAPH_EXIT=$?
printf '%s\n' "$GRAPH_EXIT" > "$GRAPH_TMP/$GRAPH_LABEL.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$GRAPH_TMP/$GRAPH_LABEL.end"
tail -n 30 "$GRAPH_TMP/$GRAPH_LABEL.log"
exit "$GRAPH_EXIT"
