# Markdown class metadata regression fixtures

From the repository root run `bash tools/check-markdown-class.sh`.
Requires LuaLaTeX and Python 3, using the vendored Markdown class/runtime.
The script retains a fresh temporary directory with all input/output and logs.

- `authors-lines.tex`: three authors on separate lines, explicit date, mixed
  email/no-email authors and shared/different affiliations.
- `authors-lines-bare.tex`: bare boolean flag with a legacy preamble filename
  and month-first date.
- `authors-default.tex`: original inline separators and legacy bare preamble.
- `authors-false.tex`: explicit false preserves the default inline separators.
- `empty-date.tex`: scalar author, empty date, no authblk layout override.
- `formalization.tex`: multiple assistants, revision aliases, escaped line
  anchors, absolute overrides, moving theorem titles and ordinary/named proof
  environments. PDFKit checks actual annotation URLs and proof text on macOS.
- `formalization-{unknown,unknown-in-proof,duplicate,invalid}.tex`: expected errors rather
  than silently producing unlinked or wrongly linked badges.

The preamble deliberately ends with `\makeatother` and uses plain `url`, not
hyperref, to exercise external-preamble catcode restoration and protected
email metadata in moving author arguments. Log assertions check all three
author separator definitions, affiliation/date skips, date values, glyph
warnings and unused options.
The full paper build and visual PDF inspection additionally check actual
title-page layout and the placement of the date after affiliations.

Run `python3 -m unittest discover -s tests/markdown -p 'test_*.py'` for math
formatting, prose protection and formalization link regression tests, including
exact preservation of all the traditional paper's assistant/URL pairs.
