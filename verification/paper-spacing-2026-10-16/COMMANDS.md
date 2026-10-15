# Markdown paper spacing — 2026-10-16

Changes are limited to the Markdown paper/runtime/checker and continuity docs.
No Git mutation, proof edits or Rocq verification. Existing user work preserved.
LuaHBTeX 1.24.0, TeX Live 2026.

## Successful commands

`lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp verification/paper-spacing-2026-10-16/spacing-regression.tex`
exits 0. With the exact `\par{}` separator emitted by Markdown, box height is
57.05pt; without it, 39.05pt. Excess is 18pt. Retained fixture and TeX log
demonstrate the empty-paragraph issue independently of full-paper pagination.

`bash tools/build-markdown-paper.sh` exits 0 in fresh directory
`/tmp/pts-rk-markdown-paper.hN0prN`; final PDF has 40 pages, 1036555 bytes.
The helper runs latexmk/LuaLaTeX/Biber and
`python3 tools/check-markdown-paper.py --rendered-dir /tmp/pts-rk-markdown-paper.hN0prN/_markdown_paper-markdown`.
Build and content-check logs are retained here. All 71977 normalized body
characters and 818 ordered math fragments match. Exactly three intended code
listings; no escaped/unparsed syntax or redundant paragraph separator immediately
before raw math displays. Final LaTeX pass has no missing glyphs or undefined
references. Existing overfull boxes and small-caps italic substitutions remain.

Compared the final AUX to
`/tmp/pts-rk-paper-merged-baseline.QBbT9z/paper.aux` with the same Python
regexes as the previous verification: ordered 32 label/number pairs and
103 citation occurrences equal; final BBL byte-identical to baseline BBL.
Checked no `\Delta` remains and no opening/closing ::: fence retains blank
inside-edge padding. Removed 162 padding lines; joined 21 prose continuations.

PDFKit/Swift rendered final pages 3, 5, 9, 25, 26; visually inspected pages
5 and 25 for paragraph/display spacing, inline badges and standalone diagram.
`git diff --check` on changed paper/runtime/checker paths passes.

Final PDF SHA-256:
`60d8721ba495b819776e56ec26906d2eae00d2bbfebc198ef55d470bc0a365f2`.
Traditional paper source SHA-256 unchanged:
`c721c21badf6380ed7e2d5e74e25610c1876ea286943eea6cba91ed91457e10b`.

## Intermediate attempts

- `/tmp/pts-rk-markdown-paper.KOGkJN`: terminated own latexmk/LuaLaTeX
  processes after prolonged parsing (approximately 90 seconds), before any
  completed PDF. The raw block grammar required a blank line or EOF and did
  not accept a closing ::: directly. Added non-consuming fence lookahead.
- `/tmp/pts-rk-markdown-paper.6qbFR2`: full fresh successful build, before
  additional prose-macro continuation cleanup; 41 pages. Not the final PDF.
- `/tmp/pts-rk-markdown-paper.AIxawA`: helper exits 1 (latexmk exit 12), first
  actual TeX error `\caption outside float`, generated line 2033. A mechanical
  prose join accidentally appended body text to two fence-opening lines.
  Restored those two newlines and reran the full fresh build successfully.

Retained interrupted and failed logs are named accordingly. Only the final
successful PDF was delivered. Local runtime changes and their scope are
documented in the Markdown PROVENANCE.md; traditional source/PDF are untouched.
