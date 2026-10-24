#!/usr/bin/env bash
set -u
root=/Users/akuklev/air/pts-rk
audit=/tmp/pts-rk-sksize.flfBIE
attempt=$1
mkdir -p "$audit/source" "$audit/data" "$audit/config" "$audit/snapshots/$attempt"
cp "$root"/theories/CombinatoryLogic-rk/agda/*.agda "$audit/source/"
cp "$root/theories/CombinatoryLogic-rk/agda/SKBracketSize.agda" "$audit/snapshots/$attempt/"
export XDG_DATA_HOME="$audit/data"
export AGDA_DIR="$audit/config"
compiler=/tmp/pts-rk-agda-2.8.0.MvVO53/agda
cubical=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical
args=("$compiler" --safe --no-default-libraries -i "$cubical" -i "$audit/source" "$audit/source/SKBracketSize.agda")
printf '%q ' "${args[@]}" > "$audit/command-$attempt.txt"
printf '\n' >> "$audit/command-$attempt.txt"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$audit/start-$attempt.txt"
"${args[@]}" > "$audit/check-$attempt.log" 2>&1
result=$?
printf '%s\n' "$result" > "$audit/exit-$attempt.txt"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$audit/end-$attempt.txt"
tail -35 "$audit/check-$attempt.log"
exit "$result"
