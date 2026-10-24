#!/usr/bin/env bash
set -eu
cd /Users/akuklev/air/pts-rk
MC_EVIDENCE=docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23
MC_PRISTINE=docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/audit-02/upstream-inventory.txt
for MC_PART in computational realization; do
  sed -n '/CONTEXT SUMMARY/,$p' "$MC_EVIDENCE/$MC_PART/kernel.log" |
    sed '/^[[:space:]]*$/d; s/[[:space:]]*$//' > "$MC_EVIDENCE/$MC_PART/inventory.txt"
  sed '/^[[:space:]]*$/d; s/[[:space:]]*$//' "$MC_PRISTINE" |
    diff -u - "$MC_EVIDENCE/$MC_PART/inventory.txt"
done
test "$(grep -c '^Closed under the global context' "$MC_EVIDENCE/computational/attempt-22.log")" = 37
test "$(grep -c '^Closed under the global context' "$MC_EVIDENCE/realization/attempt-04.log")" = 7
cmp theories/CombinatoryLogic-rk/MM0ComputationalAdequacy.v /tmp/pts-rk-mm0-computational.3tS6OZ/MM0ComputationalAdequacy.v
cmp theories/CombinatoryLogic-rk/MM0CatalogueRealization.v /tmp/pts-rk-mm0-realization.8ricsy/MM0CatalogueRealization.v
shasum -a 256 theories/CombinatoryLogic-rk/MM0ComputationalAdequacy.v > "$MC_EVIDENCE/computational/source.sha256"
shasum -a 256 theories/CombinatoryLogic-rk/MM0CatalogueRealization.v > "$MC_EVIDENCE/realization/source.sha256"
if rg -n '\b(Admitted|admit|Axiom|Parameter)\b|Unset (Guard|Universe)|bypass' theories/CombinatoryLogic-rk/MM0ComputationalAdequacy.v theories/CombinatoryLogic-rk/MM0CatalogueRealization.v; then
  exit 1
fi
git diff --check -- theories/CombinatoryLogic-rk/MM0ComputationalAdequacy.v theories/CombinatoryLogic-rk/MM0CatalogueRealization.v
printf 'All scoped checks passed: 44 closed reports, both pristine inventories, unchanged compiled sources.\n'
