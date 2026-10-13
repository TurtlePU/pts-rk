#!/usr/bin/env bash
# Run inside the target repository using its working Rocq/Equations switch.
set -euo pipefail
command -v dune >/dev/null || { echo 'dune is unavailable; activate the repository toolchain.' >&2; exit 127; }
[[ -f dune-project && -f Interpretation_of_R/DirectRCheck.v ]] || { echo 'Run from the patched repository root.' >&2; exit 2; }
LOG_DIR="${DIRECT_R_LOG_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/direct-r-build.XXXXXX")}"; mkdir -p "$LOG_DIR"
printf 'Build logs: %s\n' "$LOG_DIR"
dune --version | tee "$LOG_DIR/dune-version.log"
if command -v rocq >/dev/null; then rocq -v | tee "$LOG_DIR/rocq-version.log"; fi
stage() { local name="$1"; shift; printf '\n=== %s ===\n' "$name"; dune build "$@" 2>&1 | tee "$LOG_DIR/$name.log"; }
stage upstream theories/Ranks.vo
stage native Interpretation_of_R/DirectREval.vo Interpretation_of_R/DirectRCheck.vo
stage interpretation Interpretation_of_R/functional/DirectR.vo
stage arithmetic Interpretation_of_R/functional/DirectRArithmetic.vo
stage examples-and-assumptions Interpretation_of_R/functional/DirectRTests.vo
printf '\nAll requested builds succeeded. Review Print Assumptions output.\n'
printf 'This does NOT fill GeneratorTotal/GeneratorSound or deduction preservation.\n'
