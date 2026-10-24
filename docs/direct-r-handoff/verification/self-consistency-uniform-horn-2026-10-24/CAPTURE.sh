#!/usr/bin/env bash
# Capture once, before continuation proof/registration changes.
set -euo pipefail
HORN_ROOT="$(git rev-parse --show-toplevel)"
cd "$HORN_ROOT"
HORN_EVIDENCE=docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24
HORN_BASELINE="$HORN_EVIDENCE/baseline"
[[ ! -e "$HORN_BASELINE" ]] || { printf 'Baseline already exists; refusing overwrite.\n' >&2; exit 2; }
mkdir -p "$HORN_BASELINE"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$HORN_BASELINE/captured-utc.txt"
git rev-parse HEAD > "$HORN_BASELINE/head.txt"
git status --short --untracked-files=all > "$HORN_BASELINE/git-status.txt"
git diff --cached --stat > "$HORN_BASELINE/index-stat.txt"
git diff --numstat > "$HORN_BASELINE/diff-numstat.txt"
df -h . /private/tmp > "$HORN_BASELINE/disk.txt"
rg --files theories -g '*.v' -g dune | LC_ALL=C sort > "$HORN_BASELINE/source-paths.txt"
while IFS= read -r horn_source; do
  shasum -a 256 "$horn_source"
done < "$HORN_BASELINE/source-paths.txt" > "$HORN_BASELINE/sources.sha256"
cp theories/self_consistency/dune "$HORN_BASELINE/self-consistency-dune.snapshot"
cp theories/self_consistency/Audit.v "$HORN_BASELINE/self-consistency-Audit.v.snapshot"
cp theories/CombinatoryLogic-rk/dune "$HORN_BASELINE/combinatory-dune.snapshot"
git diff -- theories/self_consistency/dune theories/self_consistency/Audit.v \
  theories/CombinatoryLogic-rk/dune > "$HORN_BASELINE/registration.diff"
HORN_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$HORN_LOCAL/bin:$PATH"
export OPAMROOT="$HORN_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
opam exec -- rocq -v > "$HORN_BASELINE/rocq-version.txt"
opam exec -- dune --version > "$HORN_BASELINE/dune-version.txt"
opam list --installed --columns=name,version > "$HORN_BASELINE/packages.txt"
shasum -a 256 "$HORN_EVIDENCE/CAPTURE.sh" > "$HORN_BASELINE/capture-driver.sha256"
printf 'Baseline captured: %s; sources: ' "$HORN_BASELINE"
wc -l < "$HORN_BASELINE/sources.sha256"
