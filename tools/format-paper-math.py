#!/usr/bin/env python3
"""Format the Markdown paper's math source; --check only checks idempotence."""
from pathlib import Path
import argparse
from paper_math import format_source

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
path = Path(__file__).resolve().parents[1] / 'latex/PTS-rk.tex'
before = path.read_text()
after = format_source(before)
if args.check:
    print('Math source formatting:', 'PASS' if before == after else 'needs formatting')
    raise SystemExit(0 if before == after else 1)
path.write_text(after)
print('Math source formatted' if before != after else 'No changes')
