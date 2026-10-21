#!/bin/bash
set -eu
cd /Users/akuklev/air/pts-rk
evidence=_build/self-interpreter-improvements-2026-10-21
test "$(cat "$evidence/fresh-build.exit")" = 0
test "$(cat "$evidence/core-kernel.exit")" = 0
test "$(cat "$evidence/interpreter-kernel.exit")" = 0
test "$(cat "$evidence/ci-driver.exit")" = 0
test "$(cat "$evidence/note-01.exit")" = 0
test "$(cat "$evidence/pdf-inspect.exit")" = 0
cmp "$evidence/core-kernel.log" docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log
# Glob magic prevents '*' from matching descendant development directories.
# Compare proof sources/Dune, not subsequent explanatory README/PDF additions.
git diff --exit-code ffa7131 -- ':(glob)theories/*.v' \
  ':(glob)theories/NormalizationComplexity/*.v' theories/NormalizationComplexity/dune \
  ':(glob)theories/ZFC_model/*.v' theories/ZFC_model/dune
shasum -a 256 theories/self_interpreter/*.v theories/self_interpreter/dune > "$evidence/source-after.sha256"
cmp "$evidence/source-before.sha256" "$evidence/source-after.sha256"
source_reports=$(rg '^Print Assumptions' theories/self_interpreter/*.v | wc -l | tr -d ' ')
fresh_reports=$(rg -c '^Closed under the global context$' "$evidence/fresh-build.log")
test "$fresh_reports" = "$((source_reports + 1))"
test "$(awk 'NR>1 {n++} END {print n}' "$evidence/ci/stages.tsv")" = 226
awk 'NR>1 && $2 != "PASS" {exit 1}' "$evidence/ci/stages.tsv"
git diff --check
git diff --cached --quiet
test "$(git rev-parse HEAD)" = f5fdac0c1deeeb43d6138f8de3178224b79d42a4
printf 'PASS: %s self-interpreter reports + 1 upstream; 226 CI stages; stable sources and original proof comparisons.\n' "$source_reports"
