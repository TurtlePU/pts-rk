#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
EVIDENCE_DIR=docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/realization
CHECK_LABEL="${1:-kernel-final}"
CHECK_BASE=/tmp/pts-rk-mm0-bridge.IH9mrh/default/theories
CHECK_ENCODING=/tmp/pts-rk-horn-encoding.vF7hVq
CHECK_WORK=/tmp/pts-rk-horn-realization.GMs4GF
CHECK_CMD=(/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- timeout 180 rocq check -silent -o
  -Q "$CHECK_BASE" PTSrk
  -Q "$CHECK_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$CHECK_BASE/Interpretation_of_R" Interpretation_of_R
  -Q "$CHECK_BASE/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$CHECK_ENCODING" PTSrk.Combinatory
  -Q "$CHECK_WORK" PTSrk.Combinatory PTSrk.Combinatory.HornProofRealization)
printf '%q ' "${CHECK_CMD[@]}" > "$EVIDENCE_DIR/$CHECK_LABEL.command"
printf '\n' >> "$EVIDENCE_DIR/$CHECK_LABEL.command"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$EVIDENCE_DIR/$CHECK_LABEL.started"
set +e
"${CHECK_CMD[@]}" > "$EVIDENCE_DIR/$CHECK_LABEL.log" 2>&1
CHECK_EXIT=$?
set -e
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$EVIDENCE_DIR/$CHECK_LABEL.finished"
printf '%s\n' "$CHECK_EXIT" > "$EVIDENCE_DIR/$CHECK_LABEL.exit"
tail -30 "$EVIDENCE_DIR/$CHECK_LABEL.log"
if [[ "$CHECK_EXIT" -ne 0 ]]; then exit "$CHECK_EXIT"; fi
awk '/^CONTEXT SUMMARY$/ {report=1} report' "$EVIDENCE_DIR/$CHECK_LABEL.log" > "$EVIDENCE_DIR/$CHECK_LABEL.inventory"
cmp "$EVIDENCE_DIR/$CHECK_LABEL.inventory" \
  _build/combinatory-mm0-bridge-audit.BLPblO/upstream-inventory.txt
shasum -a 256 theories/CombinatoryLogic-rk/HornProofRealization.v > "$EVIDENCE_DIR/source.sha256"
