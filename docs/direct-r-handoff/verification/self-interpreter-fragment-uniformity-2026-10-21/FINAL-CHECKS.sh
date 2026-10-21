#!/bin/bash
set -eu
cd /Users/akuklev/air/pts-rk
evidence=_build/self-interpreter-fragment-uniformity-2026-10-21
for stage_name in versions fresh-build core-kernel interpreter-kernel pristine-inventory original-sources stable-sources whitespace full-ci note-01 note-02 note-03 pdf-inspect pdf-inspect-final; do
  test "$(<"$evidence/$stage_name.exit")" = 0
done
test "$(rg -c '^Closed under the global context$' "$evidence/fresh-build.log")" = 2348
test "$(rg -c '^Print Assumptions' theories/self_interpreter/*.v | awk -F: '{sum += $2} END {print sum}')" = 2347
test "$(wc -l < "$evidence/source-before.sha256" | tr -d ' ')" = 115
cmp "$evidence/source-before.sha256" "$evidence/source-after.sha256"
cmp "$evidence/core-kernel.log" docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log
awk -F '\t' 'NR>1 {total++; if ($2!="PASS" || $3!=0) bad++} END {exit !(total==226 && bad==0)}' "$evidence/ci/stages.tsv"
rg -q '^Last stage: complete$' "$evidence/ci/result.txt"
rg -q 'Constants/Inductives relying on type-in-type: <none>' "$evidence/interpreter-kernel.log"
rg -q 'Constants/Inductives relying on unsafe \(co\)fixpoints: <none>' "$evidence/interpreter-kernel.log"
rg -q 'Inductives whose positivity is assumed: <none>' "$evidence/interpreter-kernel.log"
git diff --check
git diff --cached --quiet
test "$(git rev-parse HEAD)" = 1d1f2462b1d5dff9f94f8f1f3247f40d34769a90
printf 'PASS: fresh compilation/kernel, 2347 own closed reports, stable 115-entry manifest, 226 CI stages, note/PDF checks; publication state unchanged.\n'
