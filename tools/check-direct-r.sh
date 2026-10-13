#!/usr/bin/env bash
# Run inside the target repository using its working Rocq/Equations switch.
set -euo pipefail
command -v dune >/dev/null || { echo 'dune is unavailable; activate the repository toolchain.' >&2; exit 127; }
[[ -f dune-project && -f theories/DirectRCheck.v ]] || { echo 'Run from the patched repository root.' >&2; exit 2; }
LOG_DIR="${DIRECT_R_LOG_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/direct-r-build.XXXXXX")}"; mkdir -p "$LOG_DIR"
printf 'Build logs: %s\n' "$LOG_DIR"
dune --version | tee "$LOG_DIR/dune-version.log"
if command -v rocq >/dev/null; then rocq --version | tee "$LOG_DIR/rocq-version.log"; fi
stage() { local name="$1"; shift; printf '\n=== %s ===\n' "$name"; dune build "$@" 2>&1 | tee "$LOG_DIR/$name.log"; }
stage upstream theories/Ranks.vo
stage native theories/DirectREval.vo theories/DirectRCheck.vo
stage interpretation theories/DirectR.vo
stage arithmetic theories/DirectRArithmetic.vo
stage examples-and-assumptions theories/DirectRTests.vo
printf '\nAll requested builds succeeded. Review Print Assumptions output.\n'
printf 'This does NOT fill GeneratorTotal/GeneratorSound or deduction preservation.\n'
