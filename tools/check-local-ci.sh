#!/usr/bin/env bash
# Validate the workflow and run its build driver in the dedicated local switch.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOCAL_HOME="${DIRECT_R_LOCAL_HOME:-${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci}"
export PATH="$LOCAL_HOME/bin:$PATH"
export OPAMROOT="$LOCAL_HOME/opam"
export OPAMSWITCH="${DIRECT_R_LOCAL_SWITCH:-pts-rk-ci}"
export DIRECT_R_LOG_DIR="${DIRECT_R_LOG_DIR:-$ROOT/_build/local-ci-logs}"

for tool in actionlint opam timeout; do
  command -v "$tool" >/dev/null || {
    printf 'Missing local CI tool: %s. See docs/DirectR-CI.md.\n' "$tool" >&2
    exit 127
  }
done

cd "$ROOT"
actionlint .github/workflows/direct-r.yml
opam exec -- bash tools/ci-check-direct-r.sh
