#!/usr/bin/env bash
# Copy the complete driver before execution; later edits cannot alter a run.
set -euo pipefail
HORN_ROOT="$(git rev-parse --show-toplevel)"
cd "$HORN_ROOT"
HORN_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24
source "$HORN_EVIDENCE/SCOPE.sh"
[[ "$HORN_FROZEN" == yes ]] || { printf 'Scope is not frozen; no fresh audit launched.\n' >&2; exit 2; }
HORN_LOG="$(mktemp -d "$HORN_ROOT/_build/self-consistency-uniform-horn-audit.XXXXXX")"
HORN_SNAPSHOT="$HORN_LOG/driver"
mkdir "$HORN_SNAPSHOT"
for horn_driver in AUDIT.sh RUN-AUDIT.sh SCOPE.sh gates.py GATE-TESTS.py; do
  cp "$HORN_EVIDENCE/$horn_driver" "$HORN_SNAPSHOT/$horn_driver"
done
shasum -a 256 "$HORN_SNAPSHOT"/* > "$HORN_LOG/driver-before.sha256"
chmod a-w "$HORN_SNAPSHOT"/*
printf 'Immutable driver: %s\n' "$HORN_SNAPSHOT"
exec bash "$HORN_SNAPSHOT/RUN-AUDIT.sh" "$HORN_ROOT" "$HORN_LOG" "$HORN_EVIDENCE" "$HORN_SNAPSHOT"
