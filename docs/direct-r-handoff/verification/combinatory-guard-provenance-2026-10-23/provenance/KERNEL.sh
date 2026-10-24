#!/bin/bash
set -eu
cd /Users/akuklev/air/pts-rk
tag=$1
logs=docs/direct-r-handoff/verification/combinatory-guard-provenance-2026-10-23/provenance
build=/tmp/pts-rk-guard-provenance.I3682u
deps=/tmp/pts-rk-internal-horn.6x5cr6/default/theories
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
cmd=(/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq check -silent -o
  -Q "$deps" PTSrk
  -Q "$deps/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$deps/Interpretation_of_R" Interpretation_of_R
  -Q "$deps/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$build" PTSrk.Combinatory PTSrk.Combinatory.MM0GuardProvenance)
printf '%q ' "${cmd[@]}" > "$logs/$tag.command"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$logs/$tag.start"
set +e
"${cmd[@]}" > "$logs/$tag.log" 2>&1
status=$?
set -e
printf '%s\n' "$status" > "$logs/$tag.exit"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$logs/$tag.end"
tail -25 "$logs/$tag.log"
exit "$status"
