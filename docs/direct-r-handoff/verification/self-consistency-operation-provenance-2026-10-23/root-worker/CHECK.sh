#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
CONTEXT_WORK=/tmp/pts-rk-context-provenance.pPeQ4L
CONTEXT_BASE=/tmp/pts-rk-source-provenance-fresh.yW2QOO/default/theories
CONTEXT_LABEL="${1:?attempt label required}"
CONTEXT_MODULE="${2:-ContextLookupCodes}"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$CONTEXT_WORK/$CONTEXT_LABEL.start"
shasum -a 256 "theories/self_consistency/$CONTEXT_MODULE.v" > "$CONTEXT_WORK/$CONTEXT_LABEL.source"
CONTEXT_COMMAND=(opam exec -- timeout 300 rocq compile -time
  -Q "$CONTEXT_BASE" PTSrk
  -Q "$CONTEXT_BASE/Interpretation_of_R" Interpretation_of_R
  -Q "$CONTEXT_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$CONTEXT_BASE/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q /tmp/pts-rk-context-lookup.9QUeXr/dependency-links PTSrk.SelfConsistency
  -Q "$CONTEXT_BASE/self_consistency" PTSrk.SelfConsistency
  -Q /tmp/pts-rk-context-lookup.9QUeXr PTSrk.SelfConsistency
  -Q "$CONTEXT_WORK" PTSrk.SelfConsistency
  -o "$CONTEXT_WORK/$CONTEXT_MODULE.vo"
  "theories/self_consistency/$CONTEXT_MODULE.v")
printf '%q ' "${CONTEXT_COMMAND[@]}" > "$CONTEXT_WORK/$CONTEXT_LABEL.command"
printf '\n' >> "$CONTEXT_WORK/$CONTEXT_LABEL.command"
"${CONTEXT_COMMAND[@]}" > "$CONTEXT_WORK/$CONTEXT_LABEL.log" 2>&1
CONTEXT_EXIT=$?
printf '%s\n' "$CONTEXT_EXIT" > "$CONTEXT_WORK/$CONTEXT_LABEL.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$CONTEXT_WORK/$CONTEXT_LABEL.end"
tail -n 35 "$CONTEXT_WORK/$CONTEXT_LABEL.log"
exit "$CONTEXT_EXIT"
