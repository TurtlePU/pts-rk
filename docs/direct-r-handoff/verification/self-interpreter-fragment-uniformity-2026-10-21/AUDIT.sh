#!/bin/bash
set -eu
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
evidence=/Users/akuklev/air/pts-rk/_build/self-interpreter-fragment-uniformity-2026-10-21
fresh=$(mktemp -d /tmp/pts-rk-fragment-audit.XXXXXX)
printf '%s\n' "$fresh" > "$evidence/fresh-directory.txt"
run_stage() {
  stage_name=$1
  shift
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "$evidence/$stage_name.start"
  printf '%q ' "$@" > "$evidence/$stage_name.command"
  printf '\n' >> "$evidence/$stage_name.command"
  set +e
  "$@" > "$evidence/$stage_name.log" 2>&1
  stage_result=$?
  set -e
  printf '%s\n' "$stage_result" > "$evidence/$stage_name.exit"
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "$evidence/$stage_name.end"
  printf '%s: %s\n' "$stage_name" "$stage_result"
  return "$stage_result"
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
