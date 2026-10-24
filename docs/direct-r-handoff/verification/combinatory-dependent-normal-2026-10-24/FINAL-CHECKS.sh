#!/usr/bin/env bash
set -euo pipefail
evidence_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_dir=$(cd "$evidence_dir/../../../.." && pwd)
cd "$project_dir"
mkdir -p "$evidence_dir/final"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence_dir/final/started.txt"
baseline=docs/direct-r-handoff/verification/combinatory-normal-first-2026-10-24/final-sources.sha256
awk '$2 ~ /\.v$/ || ($2 ~ /\.agda$/ && $2 !~ /\/Everything.agda$/) || $2 ~ /\/dune$/ || $2 ~ /\.mm0$/' \
  "$baseline" > "$evidence_dir/final/unchanged-baseline.sha256"
test "$(wc -l < "$evidence_dir/final/unchanged-baseline.sha256" | tr -d ' ')" = 146
shasum -a 256 -c "$evidence_dir/final/unchanged-baseline.sha256" \
  > "$evidence_dir/final/unchanged-baseline.log"
git rev-parse HEAD > "$evidence_dir/final/head.txt"
git diff --check -- theories/CombinatoryLogic-rk docs/direct-r-handoff/STATE.md \
  docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md \
  > "$evidence_dir/final/tracked-whitespace.log"
new_sources=(NormalizedFamilies NormalizedComprehension NormalizedProducts
  NormalizedInference NormalizedContexts NormalizedExamples NativeBidirectional)
: > "$evidence_dir/final/new-whitespace.log"
for name in "${new_sources[@]}"; do
  source="theories/CombinatoryLogic-rk/agda/$name.agda"
  set +e
  git diff --no-index --check /dev/null "$source" >> "$evidence_dir/final/new-whitespace.log" 2>&1
  status=$?
  set -e
  if [[ "$status" != 0 && "$status" != 1 ]]; then exit "$status"; fi
done
test ! -s "$evidence_dir/final/new-whitespace.log"
sources=(theories/CombinatoryLogic-rk/*.v theories/CombinatoryLogic-rk/agda/*.agda
  theories/CombinatoryLogic-rk/dune theories/CombinatoryLogic-rk/check-agda.sh
  theories/CombinatoryLogic-rk/build-note.sh theories/CombinatoryLogic-rk/CombinatoryPTS-rk.mm0
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf
  theories/CombinatoryLogic-rk/README.md theories/CombinatoryLogic-rk/EVIDENCE.md)
shasum -a 256 "${sources[@]}" > "$evidence_dir/final-sources.sha256"
shasum -a 256 -c "$evidence_dir/final-sources.sha256" > "$evidence_dir/final/source-stability.log"
for archive in workers contexts products examples note/inspection; do
  (cd "$evidence_dir/$archive" && shasum -a 256 -c archive.sha256) \
    > "$evidence_dir/final/${archive//\//-}-archive.log"
done
test "$(cat "$evidence_dir/aggregate/exit.txt")" = 0
test "$(cat "$evidence_dir/note/exit.txt")" = 0
test "$(rg -c '^ *Checking .*UHjrtk/source/' "$evidence_dir/aggregate/build-check.log")" = 79
if rg -in 'warning:|error:' "$evidence_dir/aggregate/build-check.log" \
    > "$evidence_dir/final/agda-diagnostics.log"; then
  exit 1
else
  test "$?" = 1
fi
shasum -a 256 docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md \
  docs/direct-r-handoff/BUILD.md > "$evidence_dir/final/handoff.sha256"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence_dir/final/finished.txt"
printf '0\n' > "$evidence_dir/final/exit.txt"
printf 'PASS: 146 unchanged baseline files; source/PDF hashes; archives; 79 safe modules; whitespace.\n'
