#!/usr/bin/env bash
set -uo pipefail
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
DENIAL_OPAM=/Users/akuklev/.local/share/pts-rk-ci/bin/opam
DENIAL_LOG=/tmp/pts-rk-horn-denials.ab2F9f
DENIAL_ROOT=/Users/akuklev/air/pts-rk
cd "$DENIAL_ROOT"
run() {
  local label="$1" code
  shift
  printf '%s ' "$label" >> "$DENIAL_LOG/commands.log"
  printf '%q ' "$@" >> "$DENIAL_LOG/commands.log"
  printf '\n' >> "$DENIAL_LOG/commands.log"
  date -u '+%Y-%m-%dT%H:%M:%SZ' >> "$DENIAL_LOG/$label.log"
  "$@" >> "$DENIAL_LOG/$label.log" 2>&1
  code=$?
  printf '%s\t%s\n' "$label" "$code" >> "$DENIAL_LOG/status.tsv"
  tail -35 "$DENIAL_LOG/$label.log"
  return "$code"
}
case "$1" in
  base)
    run versions "$DENIAL_OPAM" exec -- rocq -v || exit $?
    run base "$DENIAL_OPAM" exec -- rocq compile \
      -Q "$DENIAL_LOG" PTSrk.Combinatory \
      -o "$DENIAL_LOG/GroundHorn.vo" \
      theories/CombinatoryLogic-rk/GroundHorn.v
    ;;
  check)
    run "$2" "$DENIAL_OPAM" exec -- rocq compile \
      -Q "$DENIAL_LOG" PTSrk.Combinatory \
      -o "$DENIAL_LOG/GroundHornConsistency.vo" \
      theories/CombinatoryLogic-rk/GroundHornConsistency.v
    ;;
  kernel)
    run kernel "$DENIAL_OPAM" exec -- rocq check -silent -o \
      -Q "$DENIAL_LOG" PTSrk.Combinatory PTSrk.Combinatory.GroundHornConsistency
    ;;
  hilbert)
    run "$2" "$DENIAL_OPAM" exec -- rocq compile \
      -Q "$DENIAL_ROOT/_build/default/theories" PTSrk \
      -Q "$DENIAL_ROOT/_build/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
      -Q "$DENIAL_LOG" PTSrk.Combinatory \
      -o "$DENIAL_LOG/HilbertGrounding.vo" \
      theories/CombinatoryLogic-rk/HilbertGrounding.v
    ;;
  hilbert-kernel)
    run hilbert-kernel "$DENIAL_OPAM" exec -- rocq check -silent -o \
      -Q "$DENIAL_ROOT/_build/default/theories" PTSrk \
      -Q "$DENIAL_ROOT/_build/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
      -Q "$DENIAL_LOG" PTSrk.Combinatory PTSrk.Combinatory.HilbertGrounding
    ;;
  finite-base)
    run finite-base "$DENIAL_OPAM" exec -- rocq compile \
      -Q "$DENIAL_LOG" PTSrk.Combinatory \
      -o "$DENIAL_LOG/FiniteHorn.vo" theories/CombinatoryLogic-rk/FiniteHorn.v
    ;;
  finite-model)
    run "$2" "$DENIAL_OPAM" exec -- rocq compile \
      -Q "$DENIAL_ROOT/_build/default/theories" PTSrk \
      -Q "$DENIAL_ROOT/_build/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
      -Q "$DENIAL_LOG" PTSrk.Combinatory \
      -Q /tmp/pts-rk-horn-equality.hjwmlu Interpretation_of_R \
      -o "$DENIAL_LOG/HilbertFiniteModels.vo" \
      theories/CombinatoryLogic-rk/HilbertFiniteModels.v
    ;;
  finite-kernel)
    run finite-kernel "$DENIAL_OPAM" exec -- rocq check -silent -o \
      -Q "$DENIAL_ROOT/_build/default/theories" PTSrk \
      -Q "$DENIAL_ROOT/_build/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
      -Q "$DENIAL_LOG" PTSrk.Combinatory \
      -Q /tmp/pts-rk-horn-equality.hjwmlu Interpretation_of_R PTSrk.Combinatory.HilbertFiniteModels
    ;;
esac
