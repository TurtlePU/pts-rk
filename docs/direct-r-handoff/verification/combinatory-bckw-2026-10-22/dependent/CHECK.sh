#!/usr/bin/env bash
# Positive and intentionally rejected BCKW type-scheme regressions.
set -euo pipefail
test_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
compiler=${AGDA_BIN:-agda}
test_build=$(mktemp -d /tmp/pts-rk-bckw-dependent-check.XXXXXX)
mkdir -p "$test_build/source" "$test_build/data" "$test_build/config"
cp "$test_dir"/*.agda "$test_build/source/"
export XDG_DATA_HOME="$test_build/data"
export AGDA_DIR="$test_build/config"
"$compiler" --version > "$test_build/version.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$test_build/started.txt"
shasum -a 256 "$test_dir"/*.agda > "$test_build/source-before.sha256"
printf 'module\texpected\tactual\n' > "$test_build/status.tsv"
printf 'Logs: %s\n' "$test_build"
for module in BCKWPositive BCKWNegative BCKWDependentNegative BCKWDependentNegative2; do
  expected=42
  if [[ "$module" == BCKWPositive ]]; then expected=0; fi
  command_args=("$compiler" --safe --no-default-libraries --ignore-interfaces
    -i "$test_build/source" "$test_build/source/$module.agda")
  printf '%q ' "${command_args[@]}" >> "$test_build/commands.txt"
  printf '\n' >> "$test_build/commands.txt"
  set +e
  "${command_args[@]}" > "$test_build/$module.log" 2>&1
  actual=$?
  set -e
  printf '%s\t%s\t%s\n' "$module" "$expected" "$actual" | tee -a "$test_build/status.tsv"
  [[ "$actual" -eq "$expected" ]]
  if [[ "$expected" -eq 42 ]]; then
    rg -q 'MetaCannotDependOn' "$test_build/$module.log"
    rg -q 'not in scope of the metavariable' "$test_build/$module.log"
  fi
done
shasum -a 256 "$test_dir"/*.agda > "$test_build/source-after.sha256"
cmp "$test_build/source-before.sha256" "$test_build/source-after.sha256"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$test_build/finished.txt"
printf 'PASS: one positive and three expected type-scope rejections.\n'
