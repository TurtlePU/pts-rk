#!/usr/bin/env bash
# Fresh focused fold audit. Does not stand in for full repository CI.
set -euo pipefail
FOLD_ROOT="$(git rev-parse --show-toplevel)"
cd "$FOLD_ROOT"
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
FOLD_FINISH=false
if [[ "${1:-}" == --finish ]]; then
  FOLD_FINISH=true
  FOLD_LOG="${2:?existing log directory required}"
  FOLD_BUILD="${3:?existing fresh build required}"
  FOLD_PRISTINE="${4:?existing pristine snapshot required}"
else
  FOLD_LOG="$(mktemp -d "$FOLD_ROOT/_build/self-interpreter-fold-audit.XXXXXX")"
  FOLD_BUILD="$(mktemp -d /tmp/pts-rk-fold-fresh.XXXXXX)"
  FOLD_PRISTINE="$(mktemp -d /tmp/pts-rk-fold-pristine.XXXXXX)"
fi
FOLD_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
FOLD_SOURCES=(theories/self_interpreter/Algebra.v
  theories/self_interpreter/GenericFold.v
  theories/self_interpreter/UnifiedAlgebra.v
  theories/self_interpreter/PHOASFold.v theories/self_interpreter/PHOASCPS.v
  theories/self_interpreter/CombinatoryFold.v
  theories/self_interpreter/CombinatoryAlgebra.v
  theories/self_interpreter/FoldAudit.v)
if ! "$FOLD_FINISH"; then
  printf 'Logs: %s\nFresh: %s\nPristine: %s\n' \
    "$FOLD_LOG" "$FOLD_BUILD" "$FOLD_PRISTINE" | tee "$FOLD_LOG/paths.txt"
  printf 'stage\texit\tstart_utc\tend_utc\n' > "$FOLD_LOG/status.tsv"
fi
run() {
  local stage="$1" begin end result
  shift
  begin="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$FOLD_LOG/commands.txt"
  printf '\n' >> "$FOLD_LOG/commands.txt"
  set +e
  "$@" > "$FOLD_LOG/$stage.log" 2>&1
  result=$?
  set -e
  end="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$stage" "$result" "$begin" "$end" \
    | tee -a "$FOLD_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then
    tail -60 "$FOLD_LOG/$stage.log"
    exit "$result"
  fi
}
source_manifest() {
  shasum -a 256 theories/*.v theories/dune \
    theories/NormalizationComplexity/*.v theories/NormalizationComplexity/dune \
    theories/self_interpreter/*.v theories/self_interpreter/dune \
    theories/CombinatoryLogic-rk/*.v theories/CombinatoryLogic-rk/dune
}
closed_reports() {
  local expected actual
  expected="$(rg -c '^Print Assumptions ' theories/self_interpreter/FoldAudit.v)"
  actual="$(rg -c '^Closed under the global context$' "$FOLD_LOG/endpoints.log")"
  printf 'Public endpoints: %s; fresh closed reports: %s\n' "$expected" "$actual"
  [[ "$expected" -eq 106 && "$actual" -eq "$expected" ]]
  ! rg -n '^Axioms:|^Assumptions:' "$FOLD_LOG/endpoints.log"
}
safety() {
  ! rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${FOLD_SOURCES[@]}"
}
inventory_compare() {
  # Retain raw diagnostics; compare the COMPLETE kernel context summaries.
  # The self_interpreter physical/logical spelling emits an expected loadpath
  # warning before the inventory that is absent from the pristine core log.
  sed -n '/^CONTEXT SUMMARY/,$p' "$FOLD_LOG/pristine-kernel.log" \
    > "$FOLD_LOG/pristine-inventory.txt"
  sed -n '/^CONTEXT SUMMARY/,$p' "$FOLD_LOG/kernel.log" \
    > "$FOLD_LOG/fold-inventory.txt"
  test -s "$FOLD_LOG/pristine-inventory.txt"
  test -s "$FOLD_LOG/fold-inventory.txt"
  cmp "$FOLD_LOG/pristine-inventory.txt" "$FOLD_LOG/fold-inventory.txt"
}
if ! "$FOLD_FINISH"; then
run head git rev-parse HEAD
run versions opam list --installed --columns=name,version
run rocq-version opam exec -- rocq -v
run dune-version opam exec -- dune --version
run ocaml-version opam exec -- ocamlc -version
run sources-before source_manifest
run safety safety
run pristine-archive git archive --output="$FOLD_LOG/upstream.tar" "$FOLD_BASE"
run pristine-extract tar -xf "$FOLD_LOG/upstream.tar" -C "$FOLD_PRISTINE"
run pristine-build opam exec -- timeout 300 dune build --root "$FOLD_PRISTINE" \
  --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 300 rocq check -silent -o \
  -Q "$FOLD_PRISTINE/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-modules opam exec -- timeout 1800 dune build --build-dir "$FOLD_BUILD" \
  --display=short --no-buffer -j 2 \
  theories/self_interpreter/GenericFold.vo \
  theories/self_interpreter/UnifiedAlgebra.vo \
  theories/self_interpreter/PHOASFold.vo theories/self_interpreter/PHOASCPS.vo \
  theories/self_interpreter/CombinatoryAlgebra.vo
run endpoints opam exec -- timeout 300 dune build --build-dir "$FOLD_BUILD" \
  --display=short --no-buffer -j 2 @theories/self_interpreter/fold-audit
run closed-reports closed_reports
run kernel opam exec -- timeout 1800 rocq check -silent -o \
  -Q "$FOLD_BUILD/default/theories" PTSrk \
  -Q "$FOLD_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$FOLD_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  -Q "$FOLD_BUILD/default/theories/self_interpreter" PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.FoldAudit
fi
run inventory-compare-normalized inventory_compare
run original-kernel-unchanged git diff --exit-code "$FOLD_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run working-audit opam exec -- timeout 1800 dune build \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
run sources-after source_manifest
run source-stability cmp "$FOLD_LOG/sources-before.log" "$FOLD_LOG/sources-after.log"
run whitespace git diff --check -- theories/self_interpreter PTS-rk_self_interpreter.tex
printf 'Focused fold audit passed. Logs: %s\n' "$FOLD_LOG"
