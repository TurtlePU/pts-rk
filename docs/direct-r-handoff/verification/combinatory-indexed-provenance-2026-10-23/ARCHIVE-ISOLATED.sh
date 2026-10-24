#!/usr/bin/env bash
# Preserve isolated raw outputs without treating reused objects as fresh evidence.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
IP_ARCHIVE=docs/direct-r-handoff/verification/combinatory-indexed-provenance-2026-10-23
archive_one() {
  local source="$1" target="$2" item base
  mkdir -p "$target"
  for item in "$source"/*; do
    [[ -f "$item" ]] || continue
    base="$(basename "$item")"
    case "$base" in *.v|*.vo|*.glob|*.vos|*.vok) continue ;; esac
    gzip -c "$item" > "$target/$base.raw.gz"
    cp "$item" "$target/$base"
    perl -0pi -e 's/[ \t]+$//mg; s/\n+\z/\n/' "$target/$base"
  done
}
archive_one /tmp/pts-rk-indexed-horn.MHrkIn "$IP_ARCHIVE/encoding"
archive_one /tmp/pts-rk-indexed-consumer.qBciO2 "$IP_ARCHIVE/consumer"
printf 'Isolated encoding and consumer evidence preserved.\n'
