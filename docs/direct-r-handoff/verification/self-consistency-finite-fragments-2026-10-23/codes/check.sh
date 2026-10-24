#!/usr/bin/env bash
set -u
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
cd /Users/akuklev/air/pts-rk
SC_CHECK=/tmp/pts-rk-finite-codes.lrHajS
SC_FRESH=/tmp/pts-rk-replacement-fresh.87Hwa9/default
cp theories/self_consistency/FiniteCodeFragments.v "$SC_CHECK/FiniteCodeFragments.v"
opam exec -- rocq compile \
  -Q "$SC_FRESH/theories" PTSrk \
  -Q "$SC_FRESH/theories/self_consistency" PTSrk.SelfConsistency \
  -Q "$SC_CHECK" PTSrk.SelfConsistency \
  "$SC_CHECK/FiniteCodeFragments.v"
