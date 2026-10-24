#!/usr/bin/env bash
# Post-documentation checks; not a second proof compilation.
set -euo pipefail
OPERATION_FINAL_ROOT="$(git rev-parse --show-toplevel)"
cd "$OPERATION_FINAL_ROOT"
OPERATION_FINAL_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23
source "$OPERATION_FINAL_EVIDENCE/SCOPE.sh"
[[ "$OPERATION_FROZEN" = yes ]] || { printf 'Scope is not frozen.\n' >&2; exit 2; }
OPERATION_FINAL_LOG="$(mktemp -d "$OPERATION_FINAL_ROOT/_build/self-consistency-operation-provenance-final.XXXXXX")"
OPERATION_FINAL_SOURCES=("theories/self_consistency/$OPERATION_AUDIT.v")
OPERATION_FINAL_DIR=theories/self_consistency
for operation_module in "${OPERATION_MODULES[@]}"; do
  OPERATION_FINAL_SOURCES+=("theories/self_consistency/$operation_module.v")
done
printf 'Logs: %s\n' "$OPERATION_FINAL_LOG" | tee "$OPERATION_FINAL_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$OPERATION_FINAL_LOG/status.tsv"
run() {
  local label="$1" started finished result
  shift
  started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$OPERATION_FINAL_LOG/commands.txt"
  printf '\n' >> "$OPERATION_FINAL_LOG/commands.txt"
  set +e
  "$@" > "$OPERATION_FINAL_LOG/$label.log" 2>&1
  result=$?
  set -e
  finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$label" "$result" "$started" "$finished" | tee -a "$OPERATION_FINAL_LOG/status.tsv"
  if [[ "$result" -ne 0 ]]; then tail -70 "$OPERATION_FINAL_LOG/$label.log"; exit "$result"; fi
}
source_manifest() {
  awk '{print $2}' "$OPERATION_FINAL_EVIDENCE/audit-final/source-after.log" |
    while IFS= read -r operation_file; do shasum -a 256 "$operation_file"; done
}
registration_normalization() {
  # Accept only the reviewed one-line import, two-line module block and alias.
  perl -0pe '
    my $n = s/^From PTSrk\.SelfConsistency Require Import OperationProvenanceAudit\.\n//mg;
    die "expected exactly one added audit import\n" unless $n == 1;
  ' theories/self_consistency/Audit.v > "$OPERATION_FINAL_LOG/Audit.normalized.v" || return "$?"
  cmp "$OPERATION_FINAL_EVIDENCE/baseline/Audit.v.snapshot" "$OPERATION_FINAL_LOG/Audit.normalized.v" || return "$?"
  perl -0pe '
    my $n = s/^   NamedBeta BooleanAgreement ContextLookupCodes InternalContextLookup ContextLookupRealization\n   InternalComparisonGraph ComparisonGraphRealization OperationProvenanceAudit\n//mg;
    die "expected exactly one added module block\n" unless $n == 1;
    my $a = s/\n\(alias\n \(name operation-provenance-audit\)\n \(deps OperationProvenanceAudit\.vo\)\)\n\z//;
    die "expected exactly one terminal audit alias\n" unless $a == 1;
  ' theories/self_consistency/dune > "$OPERATION_FINAL_LOG/dune.normalized" || return "$?"
  cmp "$OPERATION_FINAL_EVIDENCE/baseline/self-consistency-dune.txt" "$OPERATION_FINAL_LOG/dune.normalized" || return "$?"
  shasum -a 256 "$OPERATION_FINAL_LOG/Audit.normalized.v" "$OPERATION_FINAL_LOG/dune.normalized"
  # Concurrent MM0 development: precisely thirteen additive module/vo entries.
  perl -0pe '
    my $m = s/^   GuardedHilbertCoverage MM0NativeSyntax MM0ComputationalAdequacy\n   MM0NativeReduction MM0CatalogueAdequacy MM0CatalogueRealization\n   MM0GuardedSyntaxAlgebra MM0GuardedReflection MM0HilbertAdequacy\n   HornProofEncoding HornProofRealization GuardedFiniteSupport\n   HornInternalSoundness MM0GuardedInternalReflection\)\n/   GuardedHilbertCoverage)\n/mg;
    die "expected exactly one concurrent module block\n" unless $m == 1;
    my $a = s/^   GuardedHilbertCoverage\.vo MM0NativeSyntax\.vo MM0ComputationalAdequacy\.vo\n   MM0NativeReduction\.vo MM0CatalogueAdequacy\.vo MM0CatalogueRealization\.vo\n   MM0GuardedSyntaxAlgebra\.vo MM0GuardedReflection\.vo MM0HilbertAdequacy\.vo\n   HornProofEncoding\.vo HornProofRealization\.vo GuardedFiniteSupport\.vo\n   HornInternalSoundness\.vo MM0GuardedInternalReflection\.vo\)\)\n/   GuardedHilbertCoverage.vo))\n/mg;
    die "expected exactly one concurrent vo block\n" unless $a == 1;
  ' theories/CombinatoryLogic-rk/dune > "$OPERATION_FINAL_LOG/combinatory-dune.normalized" || return "$?"
  cmp "$OPERATION_FINAL_EVIDENCE/baseline/combinatory-dune.txt" "$OPERATION_FINAL_LOG/combinatory-dune.normalized" || return "$?"
  shasum -a 256 "$OPERATION_FINAL_LOG/combinatory-dune.normalized"
}
declaration_coverage() {
  local operation_module
  for operation_module in "${OPERATION_MODULES[@]}"; do
    awk -v module="$operation_module" \
      '/^[[:space:]]*(Theorem|Lemma|Example|Corollary|Fact|Proposition) / {name=$2; sub(/:$/, "", name); print module "." module "." name}' \
      "$OPERATION_FINAL_DIR/$operation_module.v" || return "$?"
  done | LC_ALL=C sort > "$OPERATION_FINAL_LOG/expected-declarations.txt" || return "$?"
  awk '$1 == "Print" && $2 == "Assumptions" {name=$3; sub(/\.$/, "", name); print name}' \
    "$OPERATION_FINAL_DIR/$OPERATION_AUDIT.v" | LC_ALL=C sort > "$OPERATION_FINAL_LOG/audited-declarations.txt" || return "$?"
  cmp "$OPERATION_FINAL_LOG/expected-declarations.txt" "$OPERATION_FINAL_LOG/audited-declarations.txt" || return "$?"
  awk '$1 == "Check" {name=$2; sub(/\.$/, "", name); print name}' \
    "$OPERATION_FINAL_DIR/$OPERATION_AUDIT.v" | LC_ALL=C sort > "$OPERATION_FINAL_LOG/checked-declarations.txt" || return "$?"
  cmp "$OPERATION_FINAL_LOG/expected-declarations.txt" "$OPERATION_FINAL_LOG/checked-declarations.txt" || return "$?"
}
safety_scan() {
  if rg -n '\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${OPERATION_FINAL_SOURCES[@]}"; then return 1; fi
}
note_hashes() {
  test -s "$OPERATION_FINAL_EVIDENCE/note-horn-final/source.sha256" || return 1
  shasum -a 256 -c "$OPERATION_FINAL_EVIDENCE/note-horn-final/source.sha256"
}
whitespace() {
  local operation_file operation_result
  local operation_files=("${OPERATION_FINAL_SOURCES[@]}" theories/self_consistency/Audit.v
    theories/self_consistency/dune theories/self_consistency/README.md
    theories/self_consistency/EVIDENCE.md theories/self_consistency/DIRECT_ROADMAP.tex
    docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md)
  while IFS= read -r operation_file; do operation_files+=("$operation_file"); done \
    < <(rg --files "$OPERATION_FINAL_EVIDENCE" -g '*.sh' -g '*.md' -g '*.v' | LC_ALL=C sort)
  git diff --check -- "${operation_files[@]}" || return "$?"
  for operation_file in "${operation_files[@]}"; do
    if ! git ls-files --error-unmatch -- "$operation_file" >/dev/null 2>&1; then
      if git diff --no-index --check -- /dev/null "$operation_file"; then
        operation_result=0
      else
        operation_result=$?
      fi
      if [[ "$operation_result" -gt 1 ]]; then return "$operation_result"; fi
    fi
  done
}
no_cache_artifacts() {
  if rg --files --hidden "$OPERATION_FINAL_EVIDENCE" -g '*.vo' -g '*.vos' -g '*.vok' \
    -g '*.glob' -g '*.aux' -g '*.tar' -g '*.png' -g '*.jpg' -g '*.pdf'; then return 1; fi
}
run head git rev-parse HEAD
run head-stable cmp "$OPERATION_FINAL_LOG/head.log" "$OPERATION_FINAL_EVIDENCE/audit-final/head.log"
run current-sources source_manifest
run source-stable cmp "$OPERATION_FINAL_LOG/current-sources.log" "$OPERATION_FINAL_EVIDENCE/audit-final/source-after.log"
run previous-proofs shasum -a 256 -c "$OPERATION_FINAL_EVIDENCE/audit-final/previous-sources.sha256"
run registration-normalization registration_normalization
run declaration-coverage declaration_coverage
run inventory-compare cmp "$OPERATION_FINAL_EVIDENCE/audit-final/pristine-inventory.txt" "$OPERATION_FINAL_EVIDENCE/audit-final/inventory.txt"
run safety-scan safety_scan
run original-kernel git diff --exit-code 723cf2ec61c737ae82ba33d2e7db44f650122b0e -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run note-hashes note_hashes
run whitespace whitespace
run archive-scope no_cache_artifacts
printf 'PASS: final operation-provenance documentation/source checks. Logs: %s\n' "$OPERATION_FINAL_LOG"
