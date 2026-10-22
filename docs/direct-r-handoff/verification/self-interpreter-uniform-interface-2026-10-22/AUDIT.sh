#!/bin/bash
set -euo pipefail
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
evidence=/Users/akuklev/air/pts-rk/_build/self-interpreter-uniform-interface-2026-10-22
mkdir -p "$evidence"
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
if test "${1:-}" = pristine; then
  baseline=$(mktemp -d /tmp/pts-rk-uniform-pristine.XXXXXX)
  printf '%s\n' "$baseline" > "$evidence/pristine-directory.txt"
  run_stage pristine-export bash -o pipefail -c 'git archive "$1" | tar -x -C "$2"' pristine-export 723cf2ec61c737ae82ba33d2e7db44f650122b0e "$baseline"
  run_stage pristine-build timeout 300 opam exec -- dune build --root="$baseline" --display=short --no-buffer -j 1 theories/Ranks.vo
  run_stage pristine-kernel timeout 300 opam exec -- rocq check -silent -o -Q "$baseline/_build/default/theories" PTSrk PTSrk.Ranks
  if test -f "$evidence/core-kernel.log"; then
    run_stage fresh-pristine-inventory cmp "$evidence/core-kernel.log" "$evidence/pristine-kernel.log"
  fi
  exit
fi
if test "${1:-}" = prebuild; then
  fresh=$(mktemp -d /tmp/pts-rk-self-uniform-audit.XXXXXX)
  printf '%s\n' "$fresh" > "$evidence/fresh-directory.txt"
  run_stage versions opam list --installed --columns=name,version
  run_stage prebuild timeout 1800 opam exec -- dune build --build-dir="$fresh" --display=short --no-buffer -j 2 theories/self_interpreter/CappedDependentInterpreter.vo
  exit
fi
if test "${1:-}" = ci; then
  run_stage full-ci timeout 2700 env DIRECT_R_LOG_DIR="$evidence/full-ci" bash tools/check-local-ci.sh
  exit
fi
fresh=$(< "$evidence/fresh-directory.txt")
test -d "$fresh/default/theories"
if test "${1:-}" = interface; then
  run_stage interface-build timeout 1800 opam exec -- dune build --build-dir="$fresh" --display=short --no-buffer -j 2 theories/self_interpreter/FragmentClosureInterpreter.vo theories/self_interpreter/BudgetInternalization.vo theories/self_interpreter/FiniteLiteralBank.vo
  exit
fi
shasum -a 256 theories/self_interpreter/*.v theories/self_interpreter/dune > "$evidence/source-before.sha256"
run_stage fresh-build timeout 1800 opam exec -- dune build --build-dir="$fresh" --display=short --no-buffer -j 2 @theories/self_interpreter/audit
run_stage core-kernel timeout 300 opam exec -- rocq check -silent -o -Q "$fresh/default/theories" PTSrk PTSrk.Ranks
run_stage interpreter-kernel timeout 1800 opam exec -- rocq check -silent -o -Q "$fresh/default/theories" PTSrk -Q "$fresh/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity -Q "$fresh/default/theories/self_interpreter" PTSrk.SelfInterpreter PTSrk.SelfInterpreter.Audit
run_stage pristine-inventory cmp "$evidence/core-kernel.log" "$evidence/pristine-kernel.log"
run_stage original-sources git diff --exit-code ffa7131 -- ':(glob)theories/*.v' ':(glob)theories/NormalizationComplexity/*.v' theories/NormalizationComplexity/dune ':(glob)theories/ZFC_model/*.v' theories/ZFC_model/dune
shasum -a 256 theories/self_interpreter/*.v theories/self_interpreter/dune > "$evidence/source-after.sha256"
run_stage stable-sources cmp "$evidence/source-before.sha256" "$evidence/source-after.sha256"
run_stage whitespace git diff --check
