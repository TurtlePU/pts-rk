#!/usr/bin/env bash
# Fresh complete closure check for the fixed finite-dictionary interface.
set -euo pipefail
DICTIONARY_ROOT="$(git rev-parse --show-toplevel)"
cd "$DICTIONARY_ROOT"
DICTIONARY_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$DICTIONARY_LOCAL/bin:$PATH"
export OPAMROOT="$DICTIONARY_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
DICTIONARY_LOG="$(mktemp -d "$DICTIONARY_ROOT/_build/self-consistency-dictionaries-audit.XXXXXX")"
DICTIONARY_BUILD="$(mktemp -d /tmp/pts-rk-dictionaries-fresh.XXXXXX)"
DICTIONARY_PRISTINE="$(mktemp -d /tmp/pts-rk-dictionaries-pristine.XXXXXX)"
DICTIONARY_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
DICTIONARY_DIR=theories/self_consistency
DICTIONARY_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23
DICTIONARY_PREVIOUS=docs/direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23/audit-final/source-after.log
DICTIONARY_MODULES=(InternalFiniteDictionaries FiniteDictionaryRealization
  DictionaryRejection FiniteDictionaryAudit)
DICTIONARY_SOURCES=()
for dictionary_module in "${DICTIONARY_MODULES[@]}"; do
  DICTIONARY_SOURCES+=("$DICTIONARY_DIR/$dictionary_module.v")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' "$DICTIONARY_LOG" "$DICTIONARY_BUILD" "$DICTIONARY_PRISTINE" | tee "$DICTIONARY_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$DICTIONARY_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$DICTIONARY_LOG/commands.txt"
  printf '\n' >> "$DICTIONARY_LOG/commands.txt"
  set +e
  "$@" > "$DICTIONARY_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$DICTIONARY_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$DICTIONARY_LOG/$label.log"; exit "$result"; fi
}
source_manifest() {
  rg --files theories -g '*.v' -g dune | LC_ALL=C sort | while IFS= read -r dictionary_file; do
    shasum -a 256 "$dictionary_file"
  done
}
reports() {
  local expected actual
  expected="$(rg -c '^Print Assumptions ' "$DICTIONARY_DIR/FiniteDictionaryAudit.v")"
  actual="$(rg -c '^Closed under the global context$' "$DICTIONARY_LOG/fresh-build.log")"
  printf 'New public endpoints: %s\nAggregate fresh closed reports: %s\n' "$expected" "$actual"
  [[ "$expected" -gt 0 && "$actual" -ge "$expected" ]] || return 1
  if rg -n '^Axioms:|^Assumptions:' "$DICTIONARY_LOG/fresh-build.log"; then return 1; fi
}
compare_inventory() {
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$DICTIONARY_LOG/pristine-kernel.log")" -eq 1 ]] || return 1
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$DICTIONARY_LOG/kernel.log")" -eq 1 ]] || return 1
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$DICTIONARY_LOG/pristine-kernel.log" > "$DICTIONARY_LOG/pristine-inventory.txt"
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$DICTIONARY_LOG/kernel.log" > "$DICTIONARY_LOG/inventory.txt"
  cmp "$DICTIONARY_LOG/pristine-inventory.txt" "$DICTIONARY_LOG/inventory.txt"
}
previous_sources() {
  # Only audit registration and the Dune module/alias list may change.
  awk '$2 != "theories/self_consistency/Audit.v" && $2 != "theories/self_consistency/dune"' \
    "$DICTIONARY_PREVIOUS" > "$DICTIONARY_LOG/previous-sources.sha256"
  shasum -a 256 -c "$DICTIONARY_LOG/previous-sources.sha256"
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${DICTIONARY_SOURCES[@]}"; then return 1; fi
}
whitespace() {
  local dictionary_file dictionary_result
  local dictionary_files=("${DICTIONARY_SOURCES[@]}" "$DICTIONARY_DIR/dune"
    "$DICTIONARY_DIR/Audit.v" "$DICTIONARY_DIR/README.md" "$DICTIONARY_DIR/EVIDENCE.md"
    "$DICTIONARY_DIR/DIRECT_ROADMAP.tex" docs/direct-r-handoff/STATE.md
    docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  while IFS= read -r dictionary_file; do
    dictionary_files+=("$dictionary_file")
  done < <(rg --files "$DICTIONARY_EVIDENCE" -g '*.sh' -g '*.md' | LC_ALL=C sort)
  git diff --check -- "${dictionary_files[@]}" || return "$?"
  for dictionary_file in "${dictionary_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$dictionary_file" >/dev/null 2>&1; then
      # --no-index returns 1 for an ordinary nonempty addition, 2 for check errors.
      if git diff --no-index --check -- /dev/null "$dictionary_file"; then
        dictionary_result=0
      else
        dictionary_result=$?
      fi
      if [[ "$dictionary_result" -gt 1 ]]; then return "$dictionary_result"; fi
    fi
  done
}
run head git rev-parse HEAD
run versions opam exec -- rocq -v
run dune-version opam exec -- dune --version
run packages opam list --installed --columns=name,version
run disk df -h . /tmp
run source-before source_manifest
run previous-proofs-unchanged previous_sources
run pristine-archive git archive --output="$DICTIONARY_LOG/pristine.tar" "$DICTIONARY_BASE"
run pristine-extract tar -xf "$DICTIONARY_LOG/pristine.tar" -C "$DICTIONARY_PRISTINE"
run pristine-build opam exec -- timeout 600 dune build --root "$DICTIONARY_PRISTINE" --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 600 rocq check -silent -o -Q "$DICTIONARY_PRISTINE/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 1200 dune build --build-dir "$DICTIONARY_BUILD" --display=short --no-buffer -j 2 @theories/self_consistency/finite-dictionary-audit
run closed-reports reports
run kernel opam exec -- timeout 1200 rocq check -silent -o -bytecode-compiler yes \
  -Q "$DICTIONARY_BUILD/default/theories" PTSrk \
  -Q "$DICTIONARY_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$DICTIONARY_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$DICTIONARY_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  -Q "$DICTIONARY_BUILD/default/theories/self_consistency" PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.FiniteDictionaryAudit
run inventory-compare compare_inventory
run original-kernel-unchanged git diff --exit-code "$DICTIONARY_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run safety-scan safety_scan
run source-after source_manifest
run source-stable cmp "$DICTIONARY_LOG/source-before.log" "$DICTIONARY_LOG/source-after.log"
run previous-proofs-still-unchanged previous_sources
run whitespace whitespace
printf 'PASS: fresh finite-dictionary closure. Logs: %s\n' "$DICTIONARY_LOG"
