#!/usr/bin/env bash
# Post-documentation stability and whitespace checks, including untracked sources.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
FRAGMENT_RECORD=docs/direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23
shasum -a 256 -c "$FRAGMENT_RECORD/audit-final/source-after.log"
for fragment_module in FiniteCodeFragments FiniteSelectorSeparation FiniteCaseGuards \
  FiniteFragmentNormalization FiniteFragmentTables FiniteFragmentRejection FiniteFragmentAudit; do
  # --no-index returns 1 for the expected nonempty addition, 2/3 on errors.
  git diff --no-index --check /dev/null "theories/self_consistency/$fragment_module.v" || [[ "$?" -eq 1 ]]
done
git diff --check -- theories/self_consistency/dune theories/self_consistency/Audit.v \
  theories/self_consistency/README.md theories/self_consistency/EVIDENCE.md \
  theories/self_consistency/DIRECT_ROADMAP.tex docs/direct-r-handoff/STATE.md \
  docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md docs/DirectR-CI.md
bash -n "$FRAGMENT_RECORD/AUDIT.sh"
shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.tex theories/self_consistency/DIRECT_ROADMAP.pdf
printf 'PASS: final proof stability, changed-file whitespace and audit syntax.\n'
