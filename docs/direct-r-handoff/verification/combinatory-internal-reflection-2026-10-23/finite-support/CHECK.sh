#!/usr/bin/env bash
set -u
root=/Users/akuklev/air/pts-rk
proofbuild=/tmp/pts-rk-finite-support.Q1zQ9S
deps=/tmp/pts-rk-mm0-bridge.IH9mrh/default/theories
evidence="$root/docs/direct-r-handoff/verification/combinatory-internal-reflection-2026-10-23/finite-support"
attempt=${1:?attempt identifier required}
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam=/Users/akuklev/.local/share/pts-rk-ci/bin/opam
cp "$root/theories/CombinatoryLogic-rk/GuardedFiniteSupport.v" "$proofbuild/GuardedFiniteSupport.v"
args=(rocq compile -time -Q "$deps" PTSrk
  -Q "$deps/NormalizationComplexity" PTSrk.NormalizationComplexity
  -Q "$deps/Interpretation_of_R" Interpretation_of_R
  -Q "$deps/CombinatoryLogic-rk" PTSrk.Combinatory
  -Q "$proofbuild" PTSrk.Combinatory "$proofbuild/GuardedFiniteSupport.v")
printf '%q ' "$opam" exec -- "${args[@]}" > "$evidence/$attempt.command"
printf '\n' >> "$evidence/$attempt.command"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence/$attempt.started"
shasum -a 256 "$proofbuild/GuardedFiniteSupport.v" > "$evidence/$attempt.sha256"
"$opam" exec -- "${args[@]}" > "$evidence/$attempt.log" 2>&1
result=$?
printf '%s\n' "$result" > "$evidence/$attempt.exit"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence/$attempt.finished"
tail -n 20 "$evidence/$attempt.log"
exit "$result"
