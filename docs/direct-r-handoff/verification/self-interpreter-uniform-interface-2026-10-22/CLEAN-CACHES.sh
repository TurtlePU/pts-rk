#!/bin/bash
# Only this completed run's two generated directories; never the working build.
set -euo pipefail
cd /Users/akuklev/air/pts-rk
evidence=/Users/akuklev/air/pts-rk/_build/self-interpreter-uniform-interface-2026-10-22
test "$(< "$evidence/interpreter-kernel.exit")" = 0
test "$(< "$evidence/stable-sources.exit")" = 0
test "$(< "$evidence/full-ci.exit")" = 0
test "$(< "$evidence/fresh-pristine-inventory.exit")" = 0
test ! -L /tmp/pts-rk-self-uniform-audit.ZjpFUy
test ! -L /tmp/pts-rk-uniform-pristine.68AZJl
test -f /tmp/pts-rk-self-uniform-audit.ZjpFUy/.db
test -f /tmp/pts-rk-self-uniform-audit.ZjpFUy/default/theories/self_interpreter/Audit.vo
test -f /tmp/pts-rk-uniform-pristine.68AZJl/_build/.db
test -f /tmp/pts-rk-uniform-pristine.68AZJl/_build/default/theories/Ranks.vo
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$evidence/cache-cleanup.log"
du -sk /tmp/pts-rk-self-uniform-audit.ZjpFUy /tmp/pts-rk-uniform-pristine.68AZJl >> "$evidence/cache-cleanup.log"
rm -rf -- /tmp/pts-rk-self-uniform-audit.ZjpFUy /tmp/pts-rk-uniform-pristine.68AZJl
test ! -e /tmp/pts-rk-self-uniform-audit.ZjpFUy
test ! -e /tmp/pts-rk-uniform-pristine.68AZJl
df -h . >> "$evidence/cache-cleanup.log"
printf 'Completed audit cache and pristine snapshot removed; all logs retained.\n'
