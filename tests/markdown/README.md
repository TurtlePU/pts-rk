# Markdown class metadata regression fixtures

From the repository root run `bash tools/check-markdown-class.sh`.
Requires LuaLaTeX and Python 3, using the vendored Markdown class/runtime.
The script retains a fresh temporary directory with all input/output and logs.

- `authors-lines.tex`: three authors on separate lines, explicit date, mixed
  email/no-email authors and shared/different affiliations.
- `authors-default.tex`: original inline separators and legacy bare preamble.
- `authors-false.tex`: explicit false preserves the default inline separators.
- `empty-date.tex`: scalar author, empty date, no authblk layout override.

The preamble deliberately ends with `\makeatother` and uses plain `url`, not
hyperref, to exercise external-preamble catcode restoration and protected
email metadata in moving author arguments. Log assertions check all three
author separator definitions, date values, glyph warnings and unused options.
The full paper build and visual PDF inspection additionally check actual
title-page layout and the placement of the date after affiliations.
