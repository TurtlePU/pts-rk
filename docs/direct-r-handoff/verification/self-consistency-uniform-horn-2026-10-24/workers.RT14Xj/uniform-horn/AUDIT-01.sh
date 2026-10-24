#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
HORN_WORK=/tmp/pts-rk-uniform-horn.mgPTYI
HORN_BASE=/tmp/pts-rk-operation-provenance-fresh.DkOoCf/default/theories
HORN_MAP=(-Q "$HORN_BASE" PTSrk
  -Q "$HORN_BASE/Interpretation_of_R" Interpretation_of_R
  -Q "$HORN_BASE/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$HORN_BASE/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$HORN_BASE/self_consistency" PTSrk.SelfConsistency
  -Q "$HORN_WORK" PTSrk.SelfConsistency)
run() {
  local label="$1"; shift
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HORN_WORK/$label.start"
  printf '%q ' "$@" > "$HORN_WORK/$label.command"
  printf '\n' >> "$HORN_WORK/$label.command"
  "$@" > "$HORN_WORK/$label.log" 2>&1
  local result=$?
  printf '%s\n' "$result" > "$HORN_WORK/$label.exit"
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HORN_WORK/$label.end"
  return "$result"
}
run versions opam exec -- rocq --version || exit "$?"
run packages opam list --installed --columns=name,version || exit "$?"
run dune-version dune --version || exit "$?"
run assumptions opam exec -- timeout 60 rocq compile -time "${HORN_MAP[@]}" \
  -o "$HORN_WORK/UniformHornAudit.vo" "$HORN_WORK/UniformHornAudit.v" || exit "$?"
run kernel opam exec -- timeout 300 rocq check "${HORN_MAP[@]}" \
  PTSrk.SelfConsistency.UniformHornAudit || exit "$?"
shasum -a 256 theories/self_consistency/UniformHorn.v
rg -c 'Closed under the global context' "$HORN_WORK/assumptions.log"
