#!/usr/bin/env bash
# Check the specification and actual local proof regressions with upstream MM0.
# Toolchain pin and limitations are documented in README.md and EVIDENCE.md.
set -euo pipefail
note_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_dir=$(cd "$note_dir/../.." && pwd)
compiler=${MM0_RS:-mm0-rs}
checker=${MM0_C:-mm0-c}
for tool in "$compiler" "$checker"; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'Missing MM0 tool: %s (set MM0_RS and MM0_C).\n' "$tool" >&2
    exit 127
  fi
done
build_dir=$(mktemp -d /tmp/pts-rk-combinatory-mm0.XXXXXX)
printf 'MM0 verification directory: %s\n' "$build_dir"
spec="$note_dir/CombinatoryPTS-rk.mm0"
examples="$project_dir/docs/direct-r-handoff/verification/combinatory-mm0-2026-10-22/CombinatoryPTS-rk-examples.mm1"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$build_dir/started.txt"
"$compiler" --version > "$build_dir/versions.log"
shasum -a 256 "$spec" "$examples" > "$build_dir/sources.sha256"
run_stage() {
  local label=$1
  shift
  printf '%q ' "$@" >> "$build_dir/commands.txt"
  printf '\n' >> "$build_dir/commands.txt"
  if "$@" > "$build_dir/$label.log" 2>&1; then
    printf '%s\t0\n' "$label" >> "$build_dir/status.tsv"
    printf 'PASS %s\n' "$label"
  else
    local code=$?
    printf '%s\t%s\n' "$label" "$code" >> "$build_dir/status.tsv"
    tail -60 "$build_dir/$label.log"
    exit "$code"
  fi
}
run_stage compile-spec "$compiler" compile -W "$spec" "$build_dir/spec.mmb"
# mm0-c checks the binary certificate against the public .mm0 declarations.
run_stage check-spec "$checker" "$build_dir/spec.mmb" < "$spec"
run_stage compile-examples "$compiler" compile -W "$examples" "$build_dir/examples.mmb"
run_stage check-examples "$checker" "$build_dir/examples.mmb" < "$spec"
shasum -a 256 -c "$build_dir/sources.sha256" > "$build_dir/source-stability.log"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$build_dir/finished.txt"
printf 'All four MM0 stages passed; declarations and local proofs checked.\n'
