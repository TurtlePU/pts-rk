#!/usr/bin/env bash
# Focused fresh audit; does not replace the complete staged repository CI.
set -euo pipefail

COMB_ROOT="$(git rev-parse --show-toplevel)"
cd "$COMB_ROOT"
COMB_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$COMB_LOCAL/bin:$PATH"
export OPAMROOT="$COMB_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
COMB_LOG="$(mktemp -d "$COMB_ROOT/_build/combinatory-audit.XXXXXX")"
COMB_BUILD="$(mktemp -d /tmp/pts-rk-combinatory-audit.XXXXXX)"
COMB_UPSTREAM="$(mktemp -d /tmp/pts-rk-combinatory-upstream.XXXXXX)"
COMB_BASELINE=723cf2ec61c737ae82ba33d2e7db44f650122b0e

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

run head git rev-parse HEAD
run dune-version opam exec -- dune --version
run rocq-version opam exec -- rocq -v
run ocaml-version opam exec -- ocamlc -version
run packages opam list --installed --columns=name,version
run source-before shasum -a 256 theories/Combinatory/Core.v \
  theories/Combinatory/Presentation.v theories/Combinatory/FiniteBasis.v \
  theories/Combinatory/dune
run upstream-archive git archive --output="$COMB_LOG/upstream.tar" "$COMB_BASELINE"
run upstream-extract tar -xf "$COMB_LOG/upstream.tar" -C "$COMB_UPSTREAM"
run upstream-build opam exec -- timeout 300 dune build --root "$COMB_UPSTREAM" \
  --display=short --no-buffer -j 2 theories/Ranks.vo
run upstream-kernel opam exec -- timeout 300 rocq check -silent -o \
  -Q "$COMB_UPSTREAM/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 300 dune build --build-dir "$COMB_BUILD" \
  --display=short --no-buffer -j 2 @theories/Combinatory/audit
run kernel opam exec -- timeout 300 rocq check -silent -o \
  -Q "$COMB_BUILD/default/theories" PTSrk \
  -Q "$COMB_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$COMB_BUILD/default/theories/Combinatory" PTSrk.Combinatory \
  PTSrk.Combinatory.Core PTSrk.Combinatory.Presentation PTSrk.Combinatory.FiniteBasis
run inventory-compare cmp "$COMB_LOG/upstream-kernel.log" "$COMB_LOG/kernel.log"
run original-kernel-unchanged git diff --exit-code "$COMB_BASELINE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run source-after shasum -a 256 theories/Combinatory/Core.v \
  theories/Combinatory/Presentation.v theories/Combinatory/FiniteBasis.v \
  theories/Combinatory/dune
run source-stable cmp "$COMB_LOG/source-before.log" "$COMB_LOG/source-after.log"
run whitespace git diff --check -- theories/Combinatory docs/direct-r-handoff/STATE.md \
  docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md
printf 'Focused combinatory audit passed. Logs: %s\n' "$COMB_LOG"
