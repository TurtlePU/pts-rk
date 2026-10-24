#!/usr/bin/env bash
# Fresh complete closure check: joint traversal, storage and contract boundary.
set -euo pipefail
JOINT_ROOT="$(git rev-parse --show-toplevel)"
cd "$JOINT_ROOT"
JOINT_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$JOINT_LOCAL/bin:$PATH"
export OPAMROOT="$JOINT_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
JOINT_LOG="$(mktemp -d "$JOINT_ROOT/_build/self-consistency-joint-resources-audit.XXXXXX")"
JOINT_BUILD="$(mktemp -d /tmp/pts-rk-joint-resources-fresh.XXXXXX)"
JOINT_PRISTINE="$(mktemp -d /tmp/pts-rk-joint-resources-pristine.XXXXXX)"
JOINT_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
JOINT_DIR=theories/self_consistency
JOINT_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-joint-resources-2026-10-23
JOINT_PREVIOUS=docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23/audit-final/source-after.log
JOINT_MODULES=(InternalJointTraversal CheckerResourceBounds ComputationBoundary)
# The realization module is included only if the proof completes and remains
# in theories. A blocked candidate must instead be archived as unverified.
if [[ -f "$JOINT_DIR/JointTraversalRealization.v" ]]; then
  JOINT_MODULES+=(JointTraversalRealization)
fi
JOINT_SOURCES=("$JOINT_DIR/JointResourceAudit.v")
for joint_module in "${JOINT_MODULES[@]}"; do
  JOINT_SOURCES+=("$JOINT_DIR/$joint_module.v")
done
printf 'Logs: %s\nBuild: %s\nPristine: %s\n' "$JOINT_LOG" "$JOINT_BUILD" "$JOINT_PRISTINE" | tee "$JOINT_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$JOINT_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$JOINT_LOG/commands.txt"
  printf '\n' >> "$JOINT_LOG/commands.txt"
  set +e
  "$@" > "$JOINT_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$JOINT_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$JOINT_LOG/$label.log"; exit "$result"; fi
}
registered_modules() {
  local joint_module
  for joint_module in "${JOINT_MODULES[@]}"; do
    rg -q "(^|[[:space:]])$joint_module([[:space:])]|$)" "$JOINT_DIR/dune" || return 1
    printf '%s\n' "$joint_module"
  done
}
source_manifest() {
  rg --files theories -g '*.v' -g dune | LC_ALL=C sort | while IFS= read -r joint_file; do
    shasum -a 256 "$joint_file"
  done
}
declaration_coverage() {
  local joint_module
  for joint_module in "${JOINT_MODULES[@]}"; do
    awk -v module="$joint_module" \
      '/^(Theorem|Lemma|Example|Corollary|Fact|Proposition) / {name=$2; sub(/:$/, "", name); print module "." module "." name}' \
      "$JOINT_DIR/$joint_module.v"
  done | LC_ALL=C sort > "$JOINT_LOG/expected-declarations.txt"
  awk '$1 == "Print" && $2 == "Assumptions" {name=$3; sub(/\.$/, "", name); print name}' \
    "$JOINT_DIR/JointResourceAudit.v" | LC_ALL=C sort > "$JOINT_LOG/audited-declarations.txt"
  cmp "$JOINT_LOG/expected-declarations.txt" "$JOINT_LOG/audited-declarations.txt"
}
reports() {
  local expected actual
  expected="$(wc -l < "$JOINT_LOG/expected-declarations.txt")"
  actual="$(rg -c '^Closed under the global context$' "$JOINT_LOG/fresh-build.log")"
  printf 'New public endpoints: %s\nAggregate fresh closed reports: %s\n' "$expected" "$actual"
  [[ "$expected" -gt 0 && "$actual" -ge "$expected" ]] || return 1
  if rg -n '^Axioms:|^Assumptions:' "$JOINT_LOG/fresh-build.log"; then return 1; fi
}
compare_inventory() {
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$JOINT_LOG/pristine-kernel.log")" -eq 1 ]] || return 1
  [[ "$(rg -c '^CONTEXT SUMMARY$' "$JOINT_LOG/kernel.log")" -eq 1 ]] || return 1
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$JOINT_LOG/pristine-kernel.log" > "$JOINT_LOG/pristine-inventory.txt"
  awk '/^CONTEXT SUMMARY$/ {report=1} report' "$JOINT_LOG/kernel.log" > "$JOINT_LOG/inventory.txt"
  cmp "$JOINT_LOG/pristine-inventory.txt" "$JOINT_LOG/inventory.txt"
}
previous_sources() {
  # All previous proof files are frozen; only audit/Dune registration may change.
  awk '$2 != "theories/self_consistency/Audit.v" && $2 != "theories/self_consistency/dune"' \
    "$JOINT_PREVIOUS" > "$JOINT_LOG/previous-sources.sha256"
  shasum -a 256 -c "$JOINT_LOG/previous-sources.sha256"
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${JOINT_SOURCES[@]}"; then return 1; fi
}
whitespace() {
  local joint_file joint_result
  local joint_files=("${JOINT_SOURCES[@]}" "$JOINT_DIR/dune"
    "$JOINT_DIR/Audit.v" "$JOINT_DIR/README.md" "$JOINT_DIR/EVIDENCE.md"
    "$JOINT_DIR/DIRECT_ROADMAP.tex" docs/direct-r-handoff/STATE.md
    docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  while IFS= read -r joint_file; do
    joint_files+=("$joint_file")
  done < <(rg --files "$JOINT_EVIDENCE" -g '*.sh' -g '*.md' -g '*.v' | LC_ALL=C sort)
  git diff --check -- "${joint_files[@]}" || return "$?"
  for joint_file in "${joint_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$joint_file" >/dev/null 2>&1; then
      if git diff --no-index --check -- /dev/null "$joint_file"; then
        joint_result=0
      else
        joint_result=$?
      fi
      if [[ "$joint_result" -gt 1 ]]; then return "$joint_result"; fi
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
run pristine-archive git archive --output="$JOINT_LOG/pristine.tar" "$JOINT_BASE"
run pristine-extract tar -xf "$JOINT_LOG/pristine.tar" -C "$JOINT_PRISTINE"
run pristine-build opam exec -- timeout 600 dune build --root "$JOINT_PRISTINE" --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 600 rocq check -silent -o -Q "$JOINT_PRISTINE/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 3600 dune build --build-dir "$JOINT_BUILD" --display=short --no-buffer -j 2 @theories/self_consistency/joint-resource-audit
run closed-reports reports
run kernel opam exec -- timeout 3600 rocq check -silent -o -bytecode-compiler yes \
  -Q "$JOINT_BUILD/default/theories" PTSrk \
  -Q "$JOINT_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$JOINT_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$JOINT_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  -Q "$JOINT_BUILD/default/theories/self_consistency" PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.JointResourceAudit
run inventory-compare compare_inventory
run original-kernel-unchanged git diff --exit-code "$JOINT_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run safety-scan safety_scan
run source-after source_manifest
run source-stable cmp "$JOINT_LOG/source-before.log" "$JOINT_LOG/source-after.log"
run previous-proofs-still-unchanged previous_sources
run whitespace whitespace
printf 'PASS: fresh joint-resource closure. Logs: %s\n' "$JOINT_LOG"
