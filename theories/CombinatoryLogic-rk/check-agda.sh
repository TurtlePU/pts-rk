#!/usr/bin/env bash
# Fresh, safe Cubical checking; no project-local or user-default interfaces.
set -euo pipefail
note_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
compiler=${AGDA_BIN:-agda}
: "${CUBICAL_DIR:?Set CUBICAL_DIR to the pinned Cubical v0.9 checkout}"
cubical_dir=$(cd "$CUBICAL_DIR" && pwd)
expected=b150186d2544e7efeddd31e5d14a8b9ecbb100f7
actual=$(git -C "$cubical_dir" rev-parse HEAD)
if [[ $actual != "$expected" ]]; then
  printf 'Expected Cubical revision %s, found %s\n' "$expected" "$actual" >&2
  exit 1
fi
git -C "$cubical_dir" diff --exit-code HEAD -- '*.agda' '*.agda-lib'
untracked=$(git -C "$cubical_dir" ls-files --others --exclude-standard -- '*.agda' '*.agda-lib')
if [[ -n "$untracked" ]]; then
  printf 'Unexpected untracked Cubical sources:\n%s\n' "$untracked" >&2
  exit 1
fi
build_dir=$(mktemp -d /tmp/pts-rk-combinatory-agda.XXXXXX)
printf 'Agda verification directory: %s\n' "$build_dir"
mkdir -p "$build_dir/source" "$build_dir/data" "$build_dir/config"
shasum -a 256 "$note_dir"/agda/*.agda > "$build_dir/sources.sha256"
for source in "$note_dir"/agda/*.agda; do
  cp "$source" "$build_dir/source/"
  cmp "$source" "$build_dir/source/$(basename "$source")"
done
shasum -a 256 -c "$build_dir/sources.sha256" > "$build_dir/copied-source-stability.log"
shasum -a 256 "$build_dir/source"/*.agda > "$build_dir/copied-sources.sha256"
printf '%s\n' "$actual" > "$build_dir/cubical-commit.txt"
export XDG_DATA_HOME="$build_dir/data"
export AGDA_DIR="$build_dir/config"
"$compiler" --version > "$build_dir/versions.log"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$build_dir/started.txt"
# Cubical mode is specified in source pragmas, not globally: the compiler's
# primitive modules have their own modes. --safe checks the import closure.
command_args=("$compiler" --safe --no-default-libraries --ignore-interfaces
  -i "$cubical_dir" -i "$build_dir/source" "$build_dir/source/Everything.agda")
printf '%q ' "${command_args[@]}" > "$build_dir/command.txt"
printf '\n' >> "$build_dir/command.txt"
if "${command_args[@]}" > "$build_dir/check.log" 2>&1; then
  printf '0\n' > "$build_dir/exit-code.txt"
else
  status=$?
  printf '%s\n' "$status" > "$build_dir/exit-code.txt"
  tail -80 "$build_dir/check.log"
  exit "$status"
fi
shasum -a 256 -c "$build_dir/sources.sha256" > "$build_dir/source-stability.log"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$build_dir/finished.txt"
printf 'PASS: fresh Cubical Agda import closure checked with --safe.\n'
