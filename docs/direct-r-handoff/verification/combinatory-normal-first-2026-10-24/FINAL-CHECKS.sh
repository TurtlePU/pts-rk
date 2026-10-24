#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../../.."
evidence=docs/direct-r-handoff/verification/combinatory-normal-first-2026-10-24
shasum -a 256 -c "$evidence/agda/sources.sha256" > "$evidence/final/final-agda-stability.log"
shasum -a 256 -c "$evidence/final/baseline-sources.sha256" > "$evidence/final/preceding-source-stability.log"
shasum -a 256 -c "$evidence/note/inspection-pdf.sha256" > "$evidence/final/pdf-stability.log"
owned=(CanonicalAlgebra NormalizedSubstitution SKBracketSize SKCanonicalExamples
  SKDirectBoundary SKDirectGround SKDirectSoundness SKSourceRank)
source_files=()
for name in "${owned[@]}"; do
  source_files+=("theories/CombinatoryLogic-rk/agda/$name.agda")
done
set +e
rg -n 'TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|allow-unsolved|postulate|Admitted|unsafe' \
  "${source_files[@]}" > "$evidence/final/new-source-safety.log"
scan=$?
printf '%s\n' "$scan" > "$evidence/final/new-source-safety.exit"
set -e
test "$scan" = 1
: > "$evidence/final/new-file-whitespace.log"
for file in "${source_files[@]}" "$evidence/COMMANDS.md" "$evidence/inspect.swift" \
  "$evidence/COLLECT.sh" "$evidence/FINAL-CHECKS.sh"; do
  set +e
  git diff --no-index --check /dev/null "$file" >> "$evidence/final/new-file-whitespace.log" 2>&1
  status=$?
  set -e
  # --no-index implies --exit-code: a clean new file still returns 1.
  test "$status" -le 1
done
test ! -s "$evidence/final/new-file-whitespace.log"
git diff --check -- theories/CombinatoryLogic-rk docs/direct-r-handoff/STATE.md \
  docs/direct-r-handoff/BUILD.md docs/direct-r-handoff/DECISIONS.md "$evidence" \
  > "$evidence/final/whitespace.log"
printf '0\n' > "$evidence/final/whitespace.exit"
bash -n theories/CombinatoryLogic-rk/build-note.sh "$evidence/COLLECT.sh" "$evidence/FINAL-CHECKS.sh"
shasum -a 256 theories/CombinatoryLogic-rk/*.v theories/CombinatoryLogic-rk/agda/*.agda \
  theories/CombinatoryLogic-rk/dune theories/CombinatoryLogic-rk/check-agda.sh \
  theories/CombinatoryLogic-rk/build-note.sh theories/CombinatoryLogic-rk/CombinatoryPTS-rk.mm0 \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  theories/CombinatoryLogic-rk/README.md theories/CombinatoryLogic-rk/EVIDENCE.md \
  > "$evidence/final-sources.sha256"
shasum -a 256 -c "$evidence/final-sources.sha256" > "$evidence/final/source-stability.log"
(cd "$evidence/workers" && shasum -a 256 -c archive.sha256) > "$evidence/final/worker-archive-stability.log"
(cd "$evidence/substitution" && shasum -a 256 -c ARTIFACTS.sha256) > "$evidence/final/substitution-archive-stability.log"
printf 'PASS: stable sources/PDF/archives; safe-source scan and whitespace checks.\n'
