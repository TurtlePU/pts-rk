#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
RAW_WORK=/tmp/pts-rk-finite-raw-decoding.aSN7Ui
RAW_BASE=/tmp/pts-rk-operation-provenance-fresh.DkOoCf/default/theories
RAW_LABEL="${1:?attempt label required}"
RAW_MODULE="${2:-FiniteRawDecoding}"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$RAW_WORK/$RAW_LABEL.start"
shasum -a 256 "theories/self_consistency/$RAW_MODULE.v" > "$RAW_WORK/$RAW_LABEL.source"
RAW_COMMAND=(opam exec -- timeout 300 rocq compile -time
  -Q "$RAW_BASE" PTSrk
  -Q "$RAW_BASE/Interpretation_of_R" Interpretation_of_R
  -Q /tmp/pts-rk-raw-internal.Cw6I7V/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity
  -Q /tmp/pts-rk-raw-internal.Cw6I7V/default/theories/CombinatoryLogic-rk PTSrk.Combinatory
  -Q "$RAW_BASE/self_consistency" PTSrk.SelfConsistency
  -Q "$RAW_WORK" PTSrk.SelfConsistency
  -o "$RAW_WORK/$RAW_MODULE.vo" "theories/self_consistency/$RAW_MODULE.v")
printf '%q ' "${RAW_COMMAND[@]}" > "$RAW_WORK/$RAW_LABEL.command"
printf '\n' >> "$RAW_WORK/$RAW_LABEL.command"
"${RAW_COMMAND[@]}" > "$RAW_WORK/$RAW_LABEL.log" 2>&1
RAW_EXIT=$?
printf '%s\n' "$RAW_EXIT" > "$RAW_WORK/$RAW_LABEL.exit"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$RAW_WORK/$RAW_LABEL.end"
tail -n 30 "$RAW_WORK/$RAW_LABEL.log"
exit "$RAW_EXIT"
