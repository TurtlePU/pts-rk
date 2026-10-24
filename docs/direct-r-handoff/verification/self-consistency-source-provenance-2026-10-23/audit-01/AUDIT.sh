#!/usr/bin/env bash
# Fresh complete closure check: independent checker source provenance.
set -euo pipefail
SOURCE_ROOT="$(git rev-parse --show-toplevel)"
cd "$SOURCE_ROOT"
SOURCE_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$SOURCE_LOCAL/bin:$PATH"
export OPAMROOT="$SOURCE_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
SOURCE_LOG="$(mktemp -d "$SOURCE_ROOT/_build/self-consistency-source-provenance-audit.XXXXXX")"
SOURCE_BUILD="$(mktemp -d /tmp/pts-rk-source-provenance-fresh.XXXXXX)"
SOURCE_PRISTINE="$(mktemp -d /tmp/pts-rk-source-provenance-pristine.XXXXXX)"
SOURCE_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
SOURCE_DIR=theories/self_consistency
SOURCE_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-source-provenance-2026-10-23
SOURCE_PREVIOUS=docs/direct-r-handoff/verification/self-consistency-joint-resources-2026-10-23/audit-final/source-after.log
# Freeze this explicit module scope before the first fresh run. The exact
# declaration inventory is derived from these source files, not from reports.
SOURCE_MODULES=(CheckerSourceGraph InternalExecutionGraph CheckerGraphRealization)
SOURCE_SOURCES=("$SOURCE_DIR/SourceProvenanceAudit.v")
for source_module in "${SOURCE_MODULES[@]}"; do
  SOURCE_SOURCES+=("$SOURCE_DIR/$source_module.v")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' "$SOURCE_LOG" "$SOURCE_BUILD" "$SOURCE_PRISTINE" | tee "$SOURCE_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$SOURCE_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$SOURCE_LOG/commands.txt"
  printf '\n' >> "$SOURCE_LOG/commands.txt"
  set +e
  "$@" > "$SOURCE_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$SOURCE_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$SOURCE_LOG/$label.log"; exit "$result"; fi
}
registered_modules() {
  local source_module
  for source_module in "${SOURCE_MODULES[@]}"; do
    rg -q "(^|[[:space:]])$source_module([[:space:])]|$)" "$SOURCE_DIR/dune" || return 1
    printf '%s\n' "$source_module"
  done
}
source_manifest() {
  rg --files theories -g '*.v' -g dune | LC_ALL=C sort | while IFS= read -r source_file; do
    shasum -a 256 "$source_file"
  done
}
declaration_coverage() {
  local source_module
  for source_module in "${SOURCE_MODULES[@]}"; do
    awk -v module="$source_module" \
      '/^[[:space:]]*(Theorem|Lemma|Example|Corollary|Fact|Proposition) / {name=$2; sub(/:$/, "", name); print module "." module "." name}' \
      "$SOURCE_DIR/$source_module.v"
  done | LC_ALL=C sort > "$SOURCE_LOG/expected-declarations.txt"
  awk '$1 == "Print" && $2 == "Assumptions" {name=$3; sub(/\.$/, "", name); print name}' \
    "$SOURCE_DIR/SourceProvenanceAudit.v" | LC_ALL=C sort > "$SOURCE_LOG/audited-declarations.txt"
  cmp "$SOURCE_LOG/expected-declarations.txt" "$SOURCE_LOG/audited-declarations.txt"
}
reports() {
  local expected actual
  expected="$(wc -l < "$SOURCE_LOG/expected-declarations.txt")"
  actual="$(rg -c '^Closed under the global context$' "$SOURCE_LOG/fresh-build.log")"
  printf 'New public endpoints: %s\nAggregate fresh closed reports: %s\n' "$expected" "$actual"
  [[ "$expected" -gt 0 && "$actual" -ge "$expected" ]] || return 1
  if rg -n '^Axioms:|^Assumptions:' "$SOURCE_LOG/fresh-build.log"; then return 1; fi
}
compare_inventory() {
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$SOURCE_LOG/pristine-kernel.log")" -eq 1 ]] || return 1
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$SOURCE_LOG/kernel.log")" -eq 1 ]] || return 1
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$SOURCE_LOG/pristine-kernel.log" > "$SOURCE_LOG/pristine-inventory.txt"
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$SOURCE_LOG/kernel.log" > "$SOURCE_LOG/inventory.txt"
  cmp "$SOURCE_LOG/pristine-inventory.txt" "$SOURCE_LOG/inventory.txt"
}
previous_sources() {
  # All previous proof files are frozen; only audit/Dune registration may change.
  awk '$2 != "theories/self_consistency/Audit.v" && $2 != "theories/self_consistency/dune"' \
    "$SOURCE_PREVIOUS" > "$SOURCE_LOG/previous-sources.sha256"
  shasum -a 256 -c "$SOURCE_LOG/previous-sources.sha256"
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${SOURCE_SOURCES[@]}"; then return 1; fi
}
whitespace() {
  local source_file source_result
  local source_files=("${SOURCE_SOURCES[@]}" "$SOURCE_DIR/dune"
    "$SOURCE_DIR/Audit.v" "$SOURCE_DIR/README.md" "$SOURCE_DIR/EVIDENCE.md"
    "$SOURCE_DIR/DIRECT_ROADMAP.tex" docs/direct-r-handoff/STATE.md
    docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  while IFS= read -r source_file; do
    source_files+=("$source_file")
  done < <(rg --files "$SOURCE_EVIDENCE" -g '*.sh' -g '*.md' -g '*.v' | LC_ALL=C sort)
  git diff --check -- "${source_files[@]}" || return "$?"
  for source_file in "${source_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$source_file" >/dev/null 2>&1; then
      if git diff --no-index --check -- /dev/null "$source_file"; then
        source_result=0
      else
        source_result=$?
      fi
      if [[ "$source_result" -gt 1 ]]; then return "$source_result"; fi
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
run registered-modules registered_modules
run declaration-coverage declaration_coverage
run pristine-archive git archive --output="$SOURCE_LOG/pristine.tar" "$SOURCE_BASE"
run pristine-extract tar -xf "$SOURCE_LOG/pristine.tar" -C "$SOURCE_PRISTINE"
run pristine-build opam exec -- timeout 600 dune build --root "$SOURCE_PRISTINE" --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 600 rocq check -silent -o -Q "$SOURCE_PRISTINE/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 3600 dune build --build-dir "$SOURCE_BUILD" --display=short --no-buffer -j 2 @theories/self_consistency/source-provenance-audit
run closed-reports reports
run kernel opam exec -- timeout 3600 rocq check -silent -o -bytecode-compiler yes \
  -Q "$SOURCE_BUILD/default/theories" PTSrk \
  -Q "$SOURCE_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$SOURCE_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$SOURCE_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  -Q "$SOURCE_BUILD/default/theories/self_consistency" PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.SourceProvenanceAudit
run inventory-compare compare_inventory
run original-kernel-unchanged git diff --exit-code "$SOURCE_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run safety-scan safety_scan
run source-after source_manifest
run source-stable cmp "$SOURCE_LOG/source-before.log" "$SOURCE_LOG/source-after.log"
run previous-proofs-still-unchanged previous_sources
run whitespace whitespace
printf 'PASS: fresh source-provenance closure. Logs: %s\n' "$SOURCE_LOG"
