#!/usr/bin/env bash
# Compile metadata/layout regression fixtures using the vendored runtime.
set -euo pipefail
project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
test_dir=$(mktemp -d /tmp/pts-rk-markdown-class.XXXXXX)
printf 'Test directory: %s\n' "$test_dir"
for input in markdown.cls markdown.sty markdown verified-badges.sty; do
  ln -s "$project_dir/latex/$input" "$test_dir/$input"
done
cp "$project_dir/tests/markdown/"*.tex "$test_dir/"
cd "$test_dir"
for fixture in authors-lines authors-lines-bare authors-default authors-false empty-date formalization msc2020 msc2020-unavailable; do
  lualatex -interaction=nonstopmode -halt-on-error "$fixture.tex" \
    > "$fixture.build.log" 2>&1
done
for fixture in formalization-unknown formalization-unknown-in-proof formalization-duplicate formalization-invalid; do
  if lualatex -interaction=nonstopmode -halt-on-error "$fixture.tex" \
      > "$fixture.build.log" 2>&1; then
    printf 'Expected failure: %s\n' "$fixture" >&2
    exit 1
  fi
done
if [[ $(uname -s) == Darwin ]] && command -v swift >/dev/null; then
  swift "$project_dir/tests/markdown/check_pdf_links.swift" formalization.pdf
else
  printf 'PDFKit URL/proof-text check skipped (requires macOS + Swift).\n'
fi
python3 - <<'PY'
from pathlib import Path
msc = Path('msc2020.log').read_text()
assert 'TEST-MSC: 2020: 03B38, 03D15, 03B70, 03B40, 68N18' in msc
assert 'Undefined control sequence' not in Path('msc2020-unavailable.log').read_text()
print('msc2020: supported and unavailable command PASS')
for name, diagnostic in (
    ('unknown', 'Unknown formalization root'),
    ('unknown-in-proof', 'Unknown formalization root'),
    ('duplicate', 'duplicate formalization root'),
    ('invalid', 'invalid formalization root'),
):
    assert diagnostic in Path('formalization-' + name + '.log').read_text(), name
    print('formalization-' + name + ': expected error PASS')
log = Path('formalization.log').read_text()
for target in (
    r'https://example.org/rocq/theories/ZFC_model/ModelSoundness.v\#L133',
    r'https://example.org/old/theories/Syntax.v\#L7',
    'https://example.org/lean/Main.lean',
    'https://example.org/agda/Main.agda',
    'https://example.org/repo',
    r'https://example.org/rocq/theories/Typing.v\#L50',
    'https://example.org/rocq/theories/Proof.v',
):
    assert 'TEST-LINK: ' + target in log.replace('\n', ''), target
assert 'Undefined control sequence' not in log
print('formalization: PASS')
for name in ('authors-lines', 'authors-lines-bare', 'authors-default', 'authors-false', 'empty-date'):
    log = Path(name + '.log').read_text()
    assert 'Unused global option' not in log, name
    assert 'Missing character:' not in log, name
    for sep in ('AUTHSEP', 'AUTHAND', 'AUTHANDS'):
        line = next(x for x in log.splitlines() if x.startswith('TEST-' + sep + ':'))
        if name in ('authors-lines', 'authors-lines-bare'):
            assert r'\protect \\' in line, (name, line)
            assert 'and' not in line and ',' not in line, (name, line)
        else:
            assert r'\protect \\' not in line, (name, line)
    date = next(x for x in log.splitlines() if x.startswith('TEST-DATE:'))
    expected = 'October 16, 2026' if name == 'authors-lines-bare' else '16 October 2026'
    assert (expected in date) == (name != 'empty-date'), (name, date)
    affil = next(x for x in log.splitlines() if x.startswith('TEST-AFFILSEP:'))
    gap = next(x for x in log.splitlines() if x.startswith('TEST-DATESKIP:'))
    value = lambda line: float(line.split(':', 1)[1].strip().removesuffix('pt'))
    if name in ('authors-lines', 'authors-lines-bare'):
        assert abs(value(affil) - 3) < .001, affil
        assert abs(value(gap) - 7) < .001, gap
    else:
        assert abs(value(affil) - 10) < .001, affil
        assert value(gap) == 0, gap
    print(name + ': PASS')
PY
