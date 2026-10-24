#!/usr/bin/env bash
set -eu
root=/Users/akuklev/air/pts-rk
audit=/tmp/pts-rk-skfast.TSEzs7/consolidated
mkdir -p "$audit/source" "$audit/data" "$audit/config"
cp "$root"/theories/CombinatoryLogic-rk/agda/*.agda "$audit/source/"
shasum -a 256 "$root/theories/CombinatoryLogic-rk/agda/SKSourceRank.agda" "$root/theories/CombinatoryLogic-rk/agda/SKSourceNormal.agda" "$root/theories/CombinatoryLogic-rk/agda/SKCanonicalExamples.agda" > "$audit/sources.sha256"
export XDG_DATA_HOME="$audit/data"
export AGDA_DIR="$audit/config"
compiler=/tmp/pts-rk-agda-2.8.0.MvVO53/agda
cubical=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical
"$compiler" --version > "$audit/version.txt"
git -C "$cubical" rev-parse HEAD > "$audit/cubical-commit.txt"
args=("$compiler" --safe --no-default-libraries --ignore-interfaces -i "$cubical" -i "$audit/source" "$audit/source/SKCanonicalExamples.agda")
printf '%q ' "${args[@]}" > "$audit/command.txt"
printf '\n' >> "$audit/command.txt"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$audit/start.txt"
if "${args[@]}" > "$audit/check.log" 2>&1; then
  result=0
else
  result=$?
fi
printf '%s\n' "$result" > "$audit/exit-code.txt"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$audit/end.txt"
shasum -a 256 -c "$audit/sources.sha256" > "$audit/stability.txt"
tail -25 "$audit/check.log"
exit "$result"
