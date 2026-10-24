#!/usr/bin/env bash
# Archive only verification products, never Agda interfaces or full copies.
set -euo pipefail
cd "$(dirname "$0")/../../../.."
evidence=docs/direct-r-handoff/verification/combinatory-normal-first-2026-10-24
mkdir -p "$evidence/agda" "$evidence/note" "$evidence/note-first"
agda_build=$(sed -n 's/^Agda verification directory: //p' "$evidence/final/agda-driver.log")
note_build=$(sed -n 's/^Build directory: //p' "$evidence/final/note-final-driver.log")
first_note=$(sed -n 's/^Build directory: //p' "$evidence/final/note-first-driver.log")
for name in sources.sha256 copied-sources.sha256 cubical-commit.txt versions.log \
  started.txt finished.txt command.txt check.log exit-code.txt \
  source-stability.log copied-source-stability.log; do
  cp "$agda_build/$name" "$evidence/agda/"
done
for name in command.txt started.txt finished.txt versions.log \
  agda-source-sha256.txt mm0-source-sha256.txt build.log CombinatoryPTS-rk.log \
  build-exit-code.txt validation-exit-code.txt pygments-output.txt; do
  cp "$note_build/$name" "$evidence/note/"
  cp "$first_note/$name" "$evidence/note-first/"
done
# Exact compiler commands have a trailing blank; retain the original bytes.
gzip -c "$evidence/agda/command.txt" > "$evidence/agda/command.txt.raw.gz"
sed -i '' 's/[[:blank:]]*$//' "$evidence/agda/command.txt"
awk '$2 ~ /\.v$/ || $2 ~ /\/dune$/ || $2 ~ /\.mm0$/ ||
     ($2 ~ /\.agda$/ && $2 !~ /\/(Everything|SKSourceNormal)\.agda$/)' \
  docs/direct-r-handoff/verification/combinatory-sk-canonical-2026-10-24/final-sources.sha256 \
  > "$evidence/final/baseline-sources.sha256"
shasum -a 256 -c "$evidence/final/baseline-sources.sha256" \
  > "$evidence/final/preceding-source-stability.log"
shasum -a 256 -c "$evidence/agda/sources.sha256" \
  > "$evidence/final/final-agda-stability.log"
git diff --check -- theories/CombinatoryLogic-rk \
  docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md \
  docs/direct-r-handoff/BUILD.md "$evidence" > "$evidence/final/whitespace.log"
printf '0\n' > "$evidence/final/whitespace.exit"
