#!/usr/bin/env bash
set -eu
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
cd /Users/akuklev/air/pts-rk
SC_CHECK=/tmp/pts-rk-finite-codes.lrHajS
SC_FRESH=/tmp/pts-rk-replacement-fresh.87Hwa9/default
qargs=(
  -Q "$SC_FRESH/theories" PTSrk
  -Q "$SC_FRESH/theories/self_consistency" PTSrk.SelfConsistency
  -Q "$SC_CHECK" PTSrk.SelfConsistency
)
cmp theories/Syntax.v "$SC_FRESH/theories/Syntax.v"
cmp theories/self_consistency/StructuralCodes.v "$SC_FRESH/theories/self_consistency/StructuralCodes.v"
cmp theories/self_consistency/FiniteCodeFragments.v "$SC_CHECK/FiniteCodeFragments.v"
opam exec -- rocq compile "${qargs[@]}" "$SC_CHECK/Assumptions.v" > "$SC_CHECK/assumptions.log" 2>&1
opam exec -- rocq check -silent -o "${qargs[@]}" PTSrk.SelfConsistency.FiniteCodeFragments > "$SC_CHECK/kernel.log" 2>&1
awk '/^CONTEXT SUMMARY$/ {report=1} report' "$SC_CHECK/kernel.log" > "$SC_CHECK/inventory.txt"
cmp "$SC_CHECK/inventory.txt" _build/combinatory-quantified-models-audit.fUUdPV/upstream-inventory.txt
