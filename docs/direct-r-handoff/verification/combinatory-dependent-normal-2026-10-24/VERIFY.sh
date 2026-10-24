#!/usr/bin/env bash
# Run one fresh final check and retain its exact invocation and exit status.
set -euo pipefail
evidence_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_dir=$(cd "$evidence_dir/../../../.." && pwd)
cd "$project_dir"
case ${1:-} in
  agda)
    output_dir="$evidence_dir/aggregate"
    command_args=(env AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda
      CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical
      bash theories/CombinatoryLogic-rk/check-agda.sh)
    ;;
  note)
    output_dir="$evidence_dir/note"
    command_args=(bash theories/CombinatoryLogic-rk/build-note.sh)
    ;;
  *) printf 'Usage: bash VERIFY.sh agda|note\n' >&2; exit 2 ;;
esac
mkdir -p "$output_dir"
test ! -f "$output_dir/exit.txt"
printf '%q ' "${command_args[@]}" | sed 's/ *$//' > "$output_dir/command.txt"
printf '\n' >> "$output_dir/command.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$output_dir/started.txt"
set +e
"${command_args[@]}" > "$output_dir/driver.log" 2>&1
status=$?
set -e
printf '%s\n' "$status" > "$output_dir/exit.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$output_dir/finished.txt"
cat "$output_dir/driver.log"
if [[ "$status" != 0 ]]; then exit "$status"; fi
if [[ "$1" == agda ]]; then
  build_dir=$(sed -n 's/^Agda verification directory: //p' "$output_dir/driver.log")
  for item in check.log sources.sha256 copied-sources.sha256 cubical-commit.txt \
    copied-source-stability.log source-stability.log versions.log \
    started.txt finished.txt exit-code.txt; do
    cp "$build_dir/$item" "$output_dir/build-$item"
  done
else
  build_dir=$(sed -n 's/^Build directory: //p' "$output_dir/driver.log")
  for item in build.log CombinatoryPTS-rk.log versions.log started.txt finished.txt \
    build-exit-code.txt validation-exit-code.txt agda-source-sha256.txt \
    mm0-source-sha256.txt pygments-output.txt; do
    cp "$build_dir/$item" "$output_dir/build-$item"
  done
  cp "$build_dir"/agda-*.agda "$output_dir/"
fi
gzip -c "$build_dir/command.txt" > "$output_dir/build-command.raw.gz"
sed 's/[[:blank:]]*$//' "$build_dir/command.txt" > "$output_dir/build-command.txt"
printf '%s\n' "$build_dir" > "$output_dir/build-directory.txt"
