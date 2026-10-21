#!/bin/bash
set -eu
cd /Users/akuklev/air/pts-rk
evidence=_build/self-interpreter-capped-quotation-2026-10-21
for stage_name in versions fresh-build core-kernel interpreter-kernel pristine-inventory original-sources stable-sources whitespace full-ci-retry audit-incremental-02 note-01 note-02 pdf-inspect pdf-inspect-final; do
  test "$(<"$evidence/$stage_name.exit")" = 0
done
test "$(rg -c '^Closed under the global context$' "$evidence/fresh-build.log")" = 2550
test "$(rg -c '^Print Assumptions' theories/self_interpreter/*.v | awk -F: '{sum += $2} END {print sum}')" = 2549
test "$(rg -c '^Check ' theories/self_interpreter/Audit.v)" = 1034
test "$(wc -l < "$evidence/source-before.sha256" | tr -d ' ')" = 123
cmp "$evidence/source-before.sha256" "$evidence/source-after.sha256"
shasum -a 256 -c "$evidence/source-before.sha256"
cmp "$evidence/core-kernel.log" docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log
awk -F '\t' 'NR>1 {total++; if ($2!="PASS" || $3!=0) bad++} END {exit !(total==226 && bad==0)}' "$evidence/ci-retry/stages.tsv"
rg -q '^Last stage: complete$' "$evidence/ci-retry/result.txt"
rg -q 'Constants/Inductives relying on type-in-type: <none>' "$evidence/interpreter-kernel.log"
rg -q 'Constants/Inductives relying on unsafe \(co\)fixpoints: <none>' "$evidence/interpreter-kernel.log"
rg -q 'Inductives whose positivity is assumed: <none>' "$evidence/interpreter-kernel.log"
if rg 'Overfull|Underfull|LaTeX Warning:|Missing character:' /tmp/pts-rk-self-note.KAJfjK/PTS-rk_self_interpreter.log; then
  exit 1
fi
git diff --check
git diff --cached --quiet
test "$(git rev-parse HEAD)" = 1d1f2462b1d5dff9f94f8f1f3247f40d34769a90
printf 'PASS: fresh compilation/kernel, 2549 own closed reports, stable 123-entry manifest, 226 CI stages, note/PDF checks; publication state unchanged.\n'
