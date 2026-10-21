#!/bin/bash
set -eu
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
evidence=/Users/akuklev/air/pts-rk/_build/self-interpreter-improvements-2026-10-21
fresh=/tmp/pts-rk-self-improvements-audit.vjkEgS
run_stage() {
  name=$1
  shift
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "$evidence/$name.start"
  printf '%q ' "$@" > "$evidence/$name.command"
  printf '\n' >> "$evidence/$name.command"
  set +e
  "$@" > "$evidence/$name.log" 2>&1
  result=$?
  set -e
  printf '%s\n' "$result" > "$evidence/$name.exit"
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "$evidence/$name.end"
  printf '%s: %s\n' "$name" "$result"
  return "$result"
}
shasum -a 256 theories/self_interpreter/*.v theories/self_interpreter/dune > "$evidence/source-before.sha256"
run_stage versions opam list --installed --columns=name,version
run_stage fresh-build timeout 1200 opam exec -- dune build --build-dir="$fresh" --display=short --no-buffer -j 2 @theories/self_interpreter/audit
run_stage core-kernel timeout 300 opam exec -- rocq check -silent -o -Q "$fresh/default/theories" PTSrk PTSrk.Ranks
run_stage interpreter-kernel timeout 1200 opam exec -- rocq check -silent -o -Q "$fresh/default/theories" PTSrk -Q "$fresh/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$fresh/default/theories/self_interpreter" PTSrk.SelfInterpreter PTSrk.SelfInterpreter.Audit
run_stage pristine-inventory cmp "$evidence/core-kernel.log" docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log
run_stage original-sources git diff --exit-code ffa7131 -- ':(glob)theories/*.v' ':(glob)theories/NormalizationComplexity/*.v' theories/NormalizationComplexity/dune ':(glob)theories/ZFC_model/*.v' theories/ZFC_model/dune
shasum -a 256 theories/self_interpreter/*.v theories/self_interpreter/dune > "$evidence/source-after.sha256"
run_stage stable-sources cmp "$evidence/source-before.sha256" "$evidence/source-after.sha256"
run_stage whitespace git diff --check
rg -c '^Closed under the global context$' "$evidence/fresh-build.log"
