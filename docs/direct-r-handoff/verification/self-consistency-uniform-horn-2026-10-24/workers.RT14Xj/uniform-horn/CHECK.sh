#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
HORN_WORK=/tmp/pts-rk-uniform-horn.mgPTYI
HORN_BASE=/tmp/pts-rk-operation-provenance-fresh.DkOoCf/default/theories
HORN_LABEL="${1:?attempt label required}"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HORN_WORK/$HORN_LABEL.start"
shasum -a 256 theories/self_consistency/UniformHorn.v > "$HORN_WORK/$HORN_LABEL.source"
cp theories/self_consistency/UniformHorn.v "$HORN_WORK/$HORN_LABEL.v"
HORN_COMMAND=(opam exec -- timeout 300 rocq compile -time
  -Q "$HORN_BASE" PTSrk
  -Q "$HORN_BASE/Interpretation_of_R" Interpretation_of_R
  -Q "$HORN_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$HORN_BASE/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$HORN_BASE/self_consistency" PTSrk.SelfConsistency
  -Q "$HORN_WORK" PTSrk.SelfConsistency
  -o "$HORN_WORK/UniformHorn.vo" theories/self_consistency/UniformHorn.v)
printf '%q ' "${HORN_COMMAND[@]}" > "$HORN_WORK/$HORN_LABEL.command"
printf '\n' >> "$HORN_WORK/$HORN_LABEL.command"
"${HORN_COMMAND[@]}" > "$HORN_WORK/$HORN_LABEL.log" 2>&1
HORN_EXIT=$?
printf '%s\n' "$HORN_EXIT" > "$HORN_WORK/$HORN_LABEL.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HORN_WORK/$HORN_LABEL.end"
tail -n 35 "$HORN_WORK/$HORN_LABEL.log"
exit "$HORN_EXIT"
