# Markdown paper polish — 2026-10-15

No Git commit/push or proof changes. Preserved existing dirty work. Original
traditional paper source/PDF unchanged. LuaHBTeX 1.24.0 (TeX Live 2026).

## Build and regression checks

`bash tools/build-markdown-paper.sh` — exit 0, final fresh directory
`/tmp/pts-rk-markdown-paper.OpRA0X`, 41 pages, 1037559 bytes.
The helper invokes latexmk/LuaLaTeX/Biber and the rendered-source checker;
retained `build.log` and `content-check.log` are copied from this directory.

`python3 tools/check-markdown-paper.py` — exit 0. 71977 normalized body
characters and 818 ordered non-name mathematical fragments agree. Presentation
normalization additionally recognizes mathpar displays and Unicode punctuation;
it does not change or omit mathematical grouping/operators. Rendered parser
check finds exactly three intended code listings and no escaped math or
unparsed native environment markers.

Compared the final `paper-markdown.aux` with the traditional baseline
`/tmp/pts-rk-paper-merged-baseline.QBbT9z/paper.aux` using Python regexes
`\\newlabel\{([^}]+)\}\{\{([^}]*)\}` and
`\\abx@aux@cite\{[^}]*\}\{([^}]*)\}`: all 32 ordered label/number
pairs and 103 citation occurrences equal. BBL files byte-identical. Final
LuaLaTeX pass has no missing glyphs. Overfull boxes and pre-existing small-caps
italic substitutions remain; this is not a warning-free or pixel-equivalence
claim.

PDFKit/Swift raster review: pages 3, 5, 10, 25 and 26 at 1100×1500 maximum.
Badges are inline; standalone commutative diagram and Unicode glyphs render.
Native display reflow changes pagination from 40 to 41 pages.

Final PDF SHA-256:
`2d4398482db2f0fb66589e6cae741638f8d430fb3cc04e1b603a9dc1efc6ed05`.
Traditional source SHA-256 remains
`c721c21badf6380ed7e2d5e74e25610c1876ea286943eea6cba91ed91457e10b`.

## Intermediate failures and fixes

- Fresh `/tmp/pts-rk-markdown-paper.Fs8zrO`: build failed (latexmk exit 12,
  helper exit 1), first error `Missing $ inserted`, generated line 1651.
  A list-nested `%mathpar` consumed following prose and its inline dollars.
  Retained explicit display delimiters for the two nested displays instead.
  Unicode quotation marks in mathematical text also had missing glyphs;
  mapped their Unicode source spelling to the original TeX quote ligatures.
- `/tmp/pts-rk-markdown-paper.SPHnwf` and `.1Jn5tr`: successful intermediate
  builds; subsequent source-only script/commas spacing polish prompted the
  final fresh rebuild above. Delivered PDF is from `.OpRA0X`, not a failed or
  intermediate run.

The parser has one documented local extension: optional trailing `*` in
smart-hybrid offside environment names. The fresh complete build exercises
`%align*`, `%gather*`, `%multline*` and standalone `%tikzcd` successfully.
