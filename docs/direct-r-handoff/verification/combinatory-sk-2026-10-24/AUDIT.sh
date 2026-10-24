#!/usr/bin/env bash
# Fresh full active combinatory library audit after the SK surface migration.
set -euo pipefail
sk_root=$(git rev-parse --show-toplevel)
cd "$sk_root"
sk_local="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$sk_local/bin:$PATH"
export OPAMROOT="$sk_local/opam"
export OPAMSWITCH=pts-rk-ci
sk_base=723cf2ec61c737ae82ba33d2e7db44f650122b0e
sk_dir=theories/CombinatoryLogic-rk
sk_evidence=docs/direct-r-handoff/verification/combinatory-sk-2026-10-24
sk_logs=$(mktemp -d "$sk_root/$sk_evidence/audit.XXXXXX")
sk_build=$(mktemp -d /tmp/pts-rk-sk-audit.XXXXXX)
sk_pristine=$(mktemp -d /tmp/pts-rk-sk-pristine.XXXXXX)
sk_sources=("$sk_dir"/*.v)
sk_modules=()
for sk_source in "${sk_sources[@]}"; do
  sk_name=${sk_source##*/}
  sk_modules+=("PTSrk.Combinatory.${sk_name%.v}")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' \
  "$sk_logs" "$sk_build" "$sk_pristine" | tee "$sk_logs/paths.txt"
printf 'stage\texit\tstarted_utc\tfinished_utc\n' > "$sk_logs/status.tsv"
run() {
  local label=$1 started finished result
  shift
  started=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
  printf '%q ' "$@" >> "$sk_logs/commands.txt"
  printf '\n' >> "$sk_logs/commands.txt"
  set +e
  "$@" > "$sk_logs/$label.log" 2>&1
  result=$?
  set -e
  finished=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" |
    tee -a "$sk_logs/status.tsv"
  if [[ $result != 0 ]]; then tail -60 "$sk_logs/$label.log"; exit "$result"; fi
}
reports() {
  local expected actual
  expected=$(rg --no-filename '^Print Assumptions ' "${sk_sources[@]}" | wc -l | tr -d ' ')
  actual=$(rg -c '^Closed under the global context$' "$sk_logs/fresh-build.log")
  printf 'Active modules: %s\nOwn reports: %s\nAggregate reports: %s\n' \
    "${#sk_modules[@]}" "$expected" "$actual"
  # One additional closed report is inherited from Ranks.
  [[ ${#sk_modules[@]} == 73 && $actual == $((expected + 1)) ]] || return 1
  if rg -n '^Axioms:|^Assumptions:' "$sk_logs/fresh-build.log"; then return 1; fi
}
inventory() {
  [[ $(rg -c '^CONTEXT SUMMARY$' "$sk_logs/kernel.log") == 1 ]] || return 1
  [[ $(rg -c '^CONTEXT SUMMARY$' "$sk_logs/pristine-kernel.log") == 1 ]] || return 1
  awk '/^CONTEXT SUMMARY$/ {show=1} show' "$sk_logs/kernel.log" > "$sk_logs/inventory.txt"
  awk '/^CONTEXT SUMMARY$/ {show=1} show' "$sk_logs/pristine-kernel.log" > "$sk_logs/pristine-inventory.txt"
  cmp "$sk_logs/inventory.txt" "$sk_logs/pristine-inventory.txt"
}
safety() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${sk_sources[@]}"; then
    return 1
  fi
}
prior_proofs() {
  # Only the two explicitly replaced basis files are absent. Every other
  # previously checked Rocq body and the literal MM0 theory must be unchanged.
  awk '$2 ~ /\.v$/ && $2 !~ /\/(BCKW|AffineDuplication)\.v$/ || $2 ~ /\.mm0$/' \
    docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/audit.lNl9UC/source-after.log |
    shasum -a 256 -c -
}
run head git rev-parse HEAD
run driver shasum -a 256 "$sk_evidence/AUDIT.sh"
run rocq-version opam exec -- rocq -v
run dune-version opam exec -- dune --version
run packages opam list --installed --columns=name,version
run source-before shasum -a 256 "${sk_sources[@]}" "$sk_dir/dune" "$sk_dir/CombinatoryPTS-rk.mm0"
run pristine-archive git archive --output="$sk_pristine/source.tar" "$sk_base"
run pristine-extract tar -xf "$sk_pristine/source.tar" -C "$sk_pristine"
run pristine-build opam exec -- timeout 600 dune build --root "$sk_pristine" \
  --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 600 rocq check -silent -o \
  -Q "$sk_pristine/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 900 dune build --build-dir "$sk_build" \
  --display=short --no-buffer -j 2 @theories/CombinatoryLogic-rk/audit
run closed-reports reports
run kernel opam exec -- timeout 900 rocq check -silent -o \
  -Q "$sk_build/default/theories" PTSrk \
  -Q "$sk_build/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$sk_build/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$sk_build/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory "${sk_modules[@]}"
run inventory-comparison inventory
run original-kernel git diff --exit-code "$sk_base" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run prior-proofs prior_proofs
run safety safety
run source-after shasum -a 256 "${sk_sources[@]}" "$sk_dir/dune" "$sk_dir/CombinatoryPTS-rk.mm0"
run source-stability cmp "$sk_logs/source-before.log" "$sk_logs/source-after.log"
run whitespace git diff --check -- "$sk_dir" "$sk_evidence"
printf 'PASS: fresh active SK/combinatory audit. Logs: %s\n' "$sk_logs"
