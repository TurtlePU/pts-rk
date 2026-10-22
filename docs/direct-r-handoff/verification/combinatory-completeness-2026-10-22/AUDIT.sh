#!/usr/bin/env bash
# Fresh focused proof audit; complete repository CI is a separate command.
set -euo pipefail

COMB_ROOT="$(git rev-parse --show-toplevel)"
cd "$COMB_ROOT"
COMB_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$COMB_LOCAL/bin:$PATH"
export OPAMROOT="$COMB_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
mkdir -p "$COMB_ROOT/_build"
COMB_LOG="$(mktemp -d "$COMB_ROOT/_build/combinatory-completeness-audit.XXXXXX")"
COMB_BUILD="$(mktemp -d /tmp/pts-rk-combinatory-completeness.XXXXXX)"
COMB_UPSTREAM="$(mktemp -d /tmp/pts-rk-combinatory-completeness-pristine.XXXXXX)"
COMB_BASELINE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
COMB_DIR=theories/CombinatoryLogic-rk
COMB_SOURCES=("$COMB_DIR/Core.v" "$COMB_DIR/Presentation.v"
  "$COMB_DIR/FiniteBasis.v" "$COMB_DIR/ProductCatalogue.v"
  "$COMB_DIR/Hilbert.v" "$COMB_DIR/ProductHilbert.v"
  "$COMB_DIR/IdentityCatalogue.v" "$COMB_DIR/ConstantCatalogue.v"
  "$COMB_DIR/SubstitutionCatalogue.v" "$COMB_DIR/CatalogueHilbert.v"
  "$COMB_DIR/CatalogueEconomy.v" "$COMB_DIR/ContextualHilbert.v"
  "$COMB_DIR/ProductExposure.v" "$COMB_DIR/ContextualSubstitution.v"
  "$COMB_DIR/HilbertAbstraction.v" "$COMB_DIR/CatalogueShapes.v"
  "$COMB_DIR/HilbertReplay.v")

printf 'Logs: %s\nBuild: %s\nUpstream: %s\n' \
  "$COMB_LOG" "$COMB_BUILD" "$COMB_UPSTREAM" | tee "$COMB_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$COMB_LOG/status.tsv"

run() {
  local label="$1" start finish result
  shift
  start="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$COMB_LOG/commands.txt"
  printf '\n' >> "$COMB_LOG/commands.txt"
  set +e
  "$@" > "$COMB_LOG/$label.log" 2>&1
  result=$?
  set -e
  finish="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$start" "$finish" \
    | tee -a "$COMB_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then
    tail -70 "$COMB_LOG/$label.log"
    exit "$result"
  fi
}

check_reports() {
  local expected actual
  expected="$(rg --no-filename '^Print Assumptions ' "${COMB_SOURCES[@]}" | wc -l | tr -d ' ')"
  actual="$(rg -c '^Closed under the global context$' "$COMB_LOG/fresh-build.log")"
  printf 'Own reports: %s\nAggregate closed reports: %s\n' "$expected" "$actual"
  # The unchanged imported Ranks module prints one additional closed report.
  [[ "$actual" -eq "$((expected + 1))" ]] || return 1
  if rg -n '^Axioms:|^Assumptions:' "$COMB_LOG/fresh-build.log"; then
    return 1
  fi
}

safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' \
      "${COMB_SOURCES[@]}"; then
    return 1
  fi
}

run head git rev-parse HEAD
run dune-version opam exec -- dune --version
run rocq-version opam exec -- rocq -v
run ocaml-version opam exec -- ocamlc -version
run packages opam list --installed --columns=name,version
run source-before shasum -a 256 "${COMB_SOURCES[@]}" "$COMB_DIR/dune"
run upstream-archive git archive --output="$COMB_LOG/upstream.tar" "$COMB_BASELINE"
run upstream-extract tar -xf "$COMB_LOG/upstream.tar" -C "$COMB_UPSTREAM"
run upstream-build opam exec -- timeout 300 dune build --root "$COMB_UPSTREAM" \
  --display=short --no-buffer -j 2 theories/Ranks.vo
run upstream-kernel opam exec -- timeout 300 rocq check -silent -o \
  -Q "$COMB_UPSTREAM/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 300 dune build --build-dir "$COMB_BUILD" \
  --display=short --no-buffer -j 2 @theories/CombinatoryLogic-rk/audit
run closed-reports check_reports
run kernel opam exec -- timeout 300 rocq check -silent -o \
  -Q "$COMB_BUILD/default/theories" PTSrk \
  -Q "$COMB_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$COMB_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  PTSrk.Combinatory.Core PTSrk.Combinatory.Presentation PTSrk.Combinatory.FiniteBasis \
  PTSrk.Combinatory.ProductCatalogue PTSrk.Combinatory.Hilbert PTSrk.Combinatory.ProductHilbert \
  PTSrk.Combinatory.IdentityCatalogue PTSrk.Combinatory.ConstantCatalogue \
  PTSrk.Combinatory.SubstitutionCatalogue PTSrk.Combinatory.CatalogueHilbert \
  PTSrk.Combinatory.CatalogueEconomy PTSrk.Combinatory.ContextualHilbert \
  PTSrk.Combinatory.ProductExposure PTSrk.Combinatory.ContextualSubstitution \
  PTSrk.Combinatory.HilbertAbstraction PTSrk.Combinatory.CatalogueShapes \
  PTSrk.Combinatory.HilbertReplay
run inventory-compare cmp "$COMB_LOG/upstream-kernel.log" "$COMB_LOG/kernel.log"
run original-kernel-unchanged git diff --exit-code "$COMB_BASELINE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run source-after shasum -a 256 "${COMB_SOURCES[@]}" "$COMB_DIR/dune"
run source-stable cmp "$COMB_LOG/source-before.log" "$COMB_LOG/source-after.log"
run safety-scan safety_scan
run whitespace git diff --check -- "$COMB_DIR" tools/ci-check-direct-r.sh \
  docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md
printf 'Focused combinatory completeness-support audit passed. Logs: %s\n' "$COMB_LOG"
