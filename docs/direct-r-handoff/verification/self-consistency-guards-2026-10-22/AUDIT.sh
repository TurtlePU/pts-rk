#!/usr/bin/env bash
# Focused fresh verification, not a replacement for full repository CI.
set -euo pipefail
SC_ROOT="$(git rev-parse --show-toplevel)"
cd "$SC_ROOT"
SC_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$SC_LOCAL/bin:$PATH"
export OPAMROOT="$SC_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
SC_LOG="$(mktemp -d "$SC_ROOT/_build/self-consistency-guards-audit.XXXXXX")"
SC_BUILD="$(mktemp -d /tmp/pts-rk-guards-fresh.XXXXXX)"
SC_PRISTINE="$(mktemp -d /tmp/pts-rk-guards-pristine.XXXXXX)"
SC_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
printf 'Logs: %s\nFresh: %s\nPristine: %s\n' "$SC_LOG" "$SC_BUILD" "$SC_PRISTINE" | tee "$SC_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$SC_LOG/status.tsv"
run() {
  local label="$1" start end result
  shift
  start="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$SC_LOG/commands.txt"
  printf '\n' >> "$SC_LOG/commands.txt"
  set +e
  "$@" > "$SC_LOG/$label.log" 2>&1
  result=$?
  set -e
  end="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$start" "$end" | tee -a "$SC_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -60 "$SC_LOG/$label.log"; exit "$result"; fi
}
manifest() {
  shasum -a 256 theories/*.v theories/dune theories/Interpretation_of_R/*.v theories/Interpretation_of_R/dune theories/self_consistency/*.v theories/self_consistency/dune
}
closed_reports() {
  local expected actual
  expected="$(rg -c '^Print Assumptions ' theories/self_consistency/Audit.v)"
  actual="$(rg -c '^Closed under the global context$' "$SC_LOG/endpoints.log")"
  printf '%s endpoints; %s closed reports\n' "$expected" "$actual"
  [[ "$actual" -eq "$expected" ]] || return 1
  ! rg '^Axioms:|^Assumptions:' "$SC_LOG/endpoints.log"
}
inventory() {
  sed -n '/^CONTEXT SUMMARY/,$p' "$SC_LOG/pristine-kernel.log" > "$SC_LOG/pristine-inventory.txt"
  sed -n '/^CONTEXT SUMMARY/,$p' "$SC_LOG/kernel.log" > "$SC_LOG/current-inventory.txt"
  test -s "$SC_LOG/pristine-inventory.txt" || return 1
  test -s "$SC_LOG/current-inventory.txt" || return 1
  cmp "$SC_LOG/pristine-inventory.txt" "$SC_LOG/current-inventory.txt"
}
safety() {
  ! rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' theories/self_consistency/*.v
}
run head git rev-parse HEAD
run versions opam list --installed --columns=name,version
run rocq-version opam exec -- rocq -v
run dune-version opam exec -- dune --version
run sources-before manifest
run safety safety
run pristine-archive git archive --output="$SC_LOG/upstream.tar" "$SC_BASE" dune-project theories
run pristine-extract tar -xf "$SC_LOG/upstream.tar" -C "$SC_PRISTINE"
run pristine-build opam exec -- timeout 300 dune build --root "$SC_PRISTINE" --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 300 rocq check -silent -o -Q "$SC_PRISTINE/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 300 dune build --build-dir "$SC_BUILD" --display=short --no-buffer -j 2 theories/self_consistency/SerializationBounds.vo theories/self_consistency/InternalCarrier.vo theories/self_consistency/GuardedTables.vo theories/self_consistency/FiniteRejection.vo
run endpoints opam exec -- timeout 300 dune build --build-dir "$SC_BUILD" --display=short --no-buffer -j 2 @theories/self_consistency/audit
run closed-reports closed_reports
run kernel opam exec -- timeout 300 rocq check -silent -o -Q "$SC_BUILD/default/theories" PTSrk -Q "$SC_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R -Q "$SC_BUILD/default/theories/self_consistency" PTSrk.SelfConsistency PTSrk.SelfConsistency.Audit
run inventory inventory
run original-unchanged git diff --exit-code "$SC_BASE" -- theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run sources-after manifest
run stable cmp "$SC_LOG/sources-before.log" "$SC_LOG/sources-after.log"
printf 'Focused internal-carrier/finite-table audit passed. Logs: %s\n' "$SC_LOG"
