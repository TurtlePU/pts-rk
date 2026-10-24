#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
COMPARISON_TMP=/tmp/pts-rk-comparison-graph.AaaC94
COMPARISON_BASE=/tmp/pts-rk-source-provenance-fresh.yW2QOO/default/theories
COMPARISON_LABEL="${1:-attempt-01}"
COMPARISON_SOURCE="${2:-/Users/akuklev/air/pts-rk/theories/self_consistency/InternalComparisonGraph.v}"
COMPARISON_TIMEOUT="${3:-120}"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$COMPARISON_TMP/$COMPARISON_LABEL.start"
shasum -a 256 "$COMPARISON_SOURCE" > "$COMPARISON_TMP/$COMPARISON_LABEL.source"
COMPARISON_COMMAND=(opam exec -- timeout "$COMPARISON_TIMEOUT" rocq compile -time
  -Q "$COMPARISON_BASE" PTSrk
  -Q "$COMPARISON_BASE/Interpretation_of_R" Interpretation_of_R
  -Q "$COMPARISON_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$COMPARISON_BASE/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$COMPARISON_BASE/self_consistency" PTSrk.SelfConsistency
  -Q "$COMPARISON_TMP" PTSrk.SelfConsistency
  -o "$COMPARISON_TMP/$(basename "$COMPARISON_SOURCE" .v).vo" "$COMPARISON_SOURCE")
printf '%q ' "${COMPARISON_COMMAND[@]}" > "$COMPARISON_TMP/$COMPARISON_LABEL.command"
printf '\n' >> "$COMPARISON_TMP/$COMPARISON_LABEL.command"
"${COMPARISON_COMMAND[@]}" > "$COMPARISON_TMP/$COMPARISON_LABEL.log" 2>&1
COMPARISON_EXIT=$?
printf '%s\n' "$COMPARISON_EXIT" > "$COMPARISON_TMP/$COMPARISON_LABEL.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$COMPARISON_TMP/$COMPARISON_LABEL.end"
tail -n 24 "$COMPARISON_TMP/$COMPARISON_LABEL.log"
exit "$COMPARISON_EXIT"
