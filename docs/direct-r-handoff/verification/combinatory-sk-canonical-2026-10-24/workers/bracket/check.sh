#!/usr/bin/env bash
set -u
root=/Users/akuklev/air/pts-rk
audit=/tmp/pts-rk-skbracket.Cjke1Y
attempt=$1
mkdir -p "$audit/source" "$audit/data" "$audit/config"
cp "$root"/theories/CombinatoryLogic-rk/agda/*.agda "$audit/source/"
mkdir -p "$audit/snapshots/$attempt"
cp "$root/theories/CombinatoryLogic-rk/agda/SKBracket.agda" "$audit/snapshots/$attempt/"
if test -f "$root/theories/CombinatoryLogic-rk/agda/SKSource.agda"; then
  cp "$root/theories/CombinatoryLogic-rk/agda/SKSource.agda" "$audit/snapshots/$attempt/"
fi
export XDG_DATA_HOME="$audit/data"
export AGDA_DIR="$audit/config"
compiler=/tmp/pts-rk-agda-2.8.0.MvVO53/agda
cubical=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical
args=("$compiler" --safe --no-default-libraries -i "$cubical" -i "$audit/source" "$audit/source/SKBracket.agda")
printf '%q ' "${args[@]}" > "$audit/command-$attempt.txt"
printf '\n' >> "$audit/command-$attempt.txt"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$audit/start-$attempt.txt"
"${args[@]}" > "$audit/check-$attempt.log" 2>&1
result=$?
printf '%s\n' "$result" > "$audit/exit-$attempt.txt"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$audit/end-$attempt.txt"
tail -50 "$audit/check-$attempt.log"
exit "$result"
