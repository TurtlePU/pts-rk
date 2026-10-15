#!/usr/bin/env bash
# Compile metadata/layout regression fixtures using the vendored runtime.
set -euo pipefail
project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
test_dir=$(mktemp -d /tmp/pts-rk-markdown-class.XXXXXX)
printf 'Test directory: %s\n' "$test_dir"
for input in markdown.cls markdown.sty markdown; do
  ln -s "$project_dir/latex/$input" "$test_dir/$input"
done
cp "$project_dir/tests/markdown/"*.tex "$test_dir/"
cd "$test_dir"
for fixture in authors-lines authors-default authors-false empty-date; do
  lualatex -interaction=nonstopmode -halt-on-error "$fixture.tex" \
    > "$fixture.build.log" 2>&1
done
python3 - <<'PY'
from pathlib import Path
for name in ('authors-lines', 'authors-default', 'authors-false', 'empty-date'):
    log = Path(name + '.log').read_text()
    assert 'Unused global option' not in log, name
    assert 'Missing character:' not in log, name
    for sep in ('AUTHSEP', 'AUTHAND', 'AUTHANDS'):
        line = next(x for x in log.splitlines() if x.startswith('TEST-' + sep + ':'))
        if name == 'authors-lines':
            assert r'\protect \\' in line, (name, line)
            assert 'and' not in line and ',' not in line, (name, line)
        else:
            assert r'\protect \\' not in line, (name, line)
    date = next(x for x in log.splitlines() if x.startswith('TEST-DATE:'))
    assert ('16 October 2026' in date) == (name != 'empty-date'), (name, date)
    print(name + ': PASS')
PY
