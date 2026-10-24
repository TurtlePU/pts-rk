#!/usr/bin/env bash
set -u
root=/Users/akuklev/air/pts-rk
proofbuild=/tmp/pts-rk-finite-support.Q1zQ9S
deps=/tmp/pts-rk-mm0-bridge.IH9mrh/default/theories
evidence="$root/docs/direct-r-handoff/verification/combinatory-internal-reflection-2026-10-23/finite-support"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam=/Users/akuklev/.local/share/pts-rk-ci/bin/opam
args=(rocq check -silent -o -Q "$deps" PTSrk
  -Q "$deps/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$deps/Interpretation_of_R" Interpretation_of_R
  -Q "$deps/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$proofbuild" PTSrk.Combinatory PTSrk.Combinatory.GuardedFiniteSupport)
printf '%q ' "$opam" exec -- "${args[@]}" > "$evidence/kernel.command"
printf '\n' >> "$evidence/kernel.command"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence/kernel.started"
"$opam" exec -- "${args[@]}" > "$evidence/kernel.log" 2>&1
result=$?
printf '%s\n' "$result" > "$evidence/kernel.exit"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence/kernel.finished"
tail -n 40 "$evidence/kernel.log"
exit "$result"
