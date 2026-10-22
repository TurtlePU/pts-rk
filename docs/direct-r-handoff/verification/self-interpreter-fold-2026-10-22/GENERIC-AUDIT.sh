#!/usr/bin/env bash
# Incremental extension of the source-stable 92-endpoint fresh audit.
# Existing dependencies must be exactly those recorded by that audit.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
GEN_LOG="${1:?previous absolute audit log directory required}"
GEN_BUILD="${2:?previous absolute fresh build directory required}"
test -f "$GEN_LOG/sources-after.log"
test -f "$GEN_LOG/pristine-inventory.txt"
mkdir "$GEN_LOG/generic"
run() {
  local stage="$1" begin end result
  shift
  begin="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$GEN_LOG/generic/commands.txt"
  printf '\n' >> "$GEN_LOG/generic/commands.txt"
  set +e
  "$@" > "$GEN_LOG/generic/$stage.log" 2>&1
  result=$?
  set -e
  end="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$stage" "$result" "$begin" "$end" \
    | tee -a "$GEN_LOG/generic/status.tsv"
  if [[ "$result" -ne 0 ]]; then
    tail -60 "$GEN_LOG/generic/$stage.log"
    exit "$result"
  fi
}
manifest() {
  shasum -a 256 theories/*.v theories/dune \
    theories/NormalizationComplexity/*.v theories/NormalizationComplexity/dune \
    theories/self_interpreter/*.v theories/self_interpreter/dune \
    theories/CombinatoryLogic-rk/*.v theories/CombinatoryLogic-rk/dune
}
dependencies_unchanged() {
  sed -E '/theories\/self_interpreter\/(FoldAudit\.v|dune)$/d' \
    "$GEN_LOG/sources-after.log" > "$GEN_LOG/generic/dependencies-before.txt"
  sed -E '/theories\/self_interpreter\/(GenericFold\.v|FoldAudit\.v|dune)$/d' \
    "$GEN_LOG/generic/sources-before.log" > "$GEN_LOG/generic/dependencies-after.txt"
  cmp "$GEN_LOG/generic/dependencies-before.txt" "$GEN_LOG/generic/dependencies-after.txt"
}
reports() {
  local expected actual
  expected="$(rg -c '^Print Assumptions ' theories/self_interpreter/FoldAudit.v)"
  actual="$(rg -c '^Closed under the global context$' "$GEN_LOG/generic/endpoints.log")"
  printf 'Public endpoints: %s; fresh closed reports: %s\n' "$expected" "$actual"
  [[ "$expected" -eq 106 && "$actual" -eq "$expected" ]]
  ! rg -n '^Axioms:|^Assumptions:' "$GEN_LOG/generic/endpoints.log"
}
inventory() {
  sed -n '/^CONTEXT SUMMARY/,$p' "$GEN_LOG/generic/kernel.log" \
    > "$GEN_LOG/generic/inventory.txt"
  test -s "$GEN_LOG/generic/inventory.txt"
  cmp "$GEN_LOG/pristine-inventory.txt" "$GEN_LOG/generic/inventory.txt"
}
safety() {
  ! rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' \
    theories/self_interpreter/{Algebra,GenericFold,UnifiedAlgebra,PHOASFold,PHOASCPS,CombinatoryFold,CombinatoryAlgebra,FoldAudit}.v
}
run sources-before manifest
run dependencies-unchanged dependencies_unchanged
run safety safety
run generic-module opam exec -- timeout 300 dune build --build-dir "$GEN_BUILD" \
  --display=short --no-buffer -j 2 theories/self_interpreter/GenericFold.vo
run endpoints opam exec -- timeout 300 dune build --build-dir "$GEN_BUILD" \
  --display=short --no-buffer -j 2 @theories/self_interpreter/fold-audit
run closed-reports reports
run kernel opam exec -- timeout 900 rocq check -silent -o \
  -Q "$GEN_BUILD/default/theories" PTSrk \
  -Q "$GEN_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$GEN_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  -Q "$GEN_BUILD/default/theories/self_interpreter" PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.GenericFold
run inventory-compare inventory
run working-audit opam exec -- timeout 600 dune build \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
run sources-after manifest
run source-stability cmp "$GEN_LOG/generic/sources-before.log" "$GEN_LOG/generic/sources-after.log"
run whitespace git diff --check -- theories/self_interpreter PTS-rk_self_interpreter.tex
printf 'Generic fold extension audit passed. Logs: %s/generic\n' "$GEN_LOG"
