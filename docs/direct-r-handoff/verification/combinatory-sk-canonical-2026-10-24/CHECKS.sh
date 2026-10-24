#!/usr/bin/env bash
set -euo pipefail
project=/Users/akuklev/air/pts-rk
evidence=$project/docs/direct-r-handoff/verification/combinatory-sk-canonical-2026-10-24
cd "$project"
sources=(theories/CombinatoryLogic-rk/agda/SKSource.agda
  theories/CombinatoryLogic-rk/agda/SKSourceEquality.agda
  theories/CombinatoryLogic-rk/agda/SKSourceNormal.agda
  theories/CombinatoryLogic-rk/agda/SKBracket.agda
  theories/CombinatoryLogic-rk/agda/SKCanonicalNormal.agda
  theories/CombinatoryLogic-rk/agda/SKCanonical.agda)
reject_pattern() {
  local pattern=$1
  shift
  if rg -n "$pattern" "$@"; then
    return 1
  else
    local status=$?
    test "$status" = 1
  fi
}
reject_pattern 'postulate|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|allow-unsolved|primTrustMe|\{!!\}' "${sources[@]}"
reject_pattern '[[:blank:]]+$' "${sources[@]}"
reject_pattern 'BCKW|AffineDuplication' theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/*.v theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex
git diff --check -- theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex \
  theories/CombinatoryLogic-rk/README.md theories/CombinatoryLogic-rk/EVIDENCE.md \
  theories/CombinatoryLogic-rk/build-note.sh theories/CombinatoryLogic-rk/agda/Everything.agda \
  docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md
cmp "${sources[5]}" "$evidence/canonical/attempt02.agda"
shasum -a 256 -c "$evidence/final/unchanged-baseline.sha256"
shasum -a 256 -c "$evidence/agda/sources.sha256"
(cd "$evidence/workers" && shasum -a 256 -c archive.sha256)
shasum -a 256 theories/CombinatoryLogic-rk/*.v theories/CombinatoryLogic-rk/agda/*.agda \
  theories/CombinatoryLogic-rk/dune theories/CombinatoryLogic-rk/check-agda.sh \
  theories/CombinatoryLogic-rk/build-note.sh theories/CombinatoryLogic-rk/CombinatoryPTS-rk.mm0 \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  > "$evidence/final-sources.sha256"
printf '%s\n' 'PASS: unchanged baseline, checked-source stability, worker archive, safety and whitespace.'
