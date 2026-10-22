#!/bin/bash
set -eu
cd /Users/akuklev/air/pts-rk
evidence=/Users/akuklev/air/pts-rk/_build/self-interpreter-uniform-interface-2026-10-22
mkdir -p "$evidence"
proofs=(
  theories/self_interpreter/BudgetInternalization.v
  theories/self_interpreter/FiniteLiteralBank.v
  theories/self_interpreter/NumericLiteralBank.v
  theories/self_interpreter/FixedInterface.v
  theories/self_interpreter/RankPadding.v
  theories/self_interpreter/FragmentClosureInterpreter.v
)
set +e
rg -n '\b(Admitted|admit|Axiom|Axioms)\b|Unset (Guard|Universe|Positivity) Checking|Set (Allow StrictProp|Type in Type)' \
  "${proofs[@]}" > "$evidence/new-source-safety.log" 2>&1
scan_status=$?
set -e
test "$scan_status" -eq 1
for source_file in "${proofs[@]}"; do
  source_name=${source_file##*/}
  set +e
  git diff --no-index --check /dev/null "$source_file" \
    > "$evidence/whitespace-$source_name.log" 2>&1
  check_status=$?
  set -e
  test "$check_status" -le 1
  test ! -s "$evidence/whitespace-$source_name.log"
done
git diff --check > "$evidence/tracked-whitespace.log"
shasum -a 256 "${proofs[@]}" > "$evidence/new-source.sha256"
shasum -a 256 PTS-rk_self_interpreter.tex PTS-rk_self_interpreter.pdf \
  theories/self_consistency/README.tex theories/self_consistency/README.pdf \
  > "$evidence/documents.sha256"
printf 'New-source safety and tracked/untracked whitespace checks: PASS\n'
