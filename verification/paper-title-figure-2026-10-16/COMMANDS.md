# Dated title, author layout, Unicode and Figure 2 — 2026-10-16

Only Markdown paper/runtime/class/tests/build documentation changed. Existing
dirty Rocq, CI and cache/log work is excluded from the requested commits.
No proof advancement or fresh Rocq verification claimed. Ordinary origin/main
push requested; remote main checked at 35682e6 before publication.

## Final verification

`bash tools/build-markdown-paper.sh` — exit 0, fresh directory
`/tmp/pts-rk-markdown-paper.PBYDVw`. 40 pages, 1037340 bytes.
Retained build.log/content-check.log. LuaHBTeX 1.24.0 (TeX Live 2026).
The source/rendered checker passes: 72031 canonical body characters, 818
ordered non-name math fragments, exactly three source listings, no unparsed
syntax or redundant separators before displays. Unicode aliases are mapped
to the original TeX glyphs, not substituted fonts. All 32 ordered label/number
pairs, 103 citations and byte-identical BBL match the traditional baseline
in /tmp/pts-rk-paper-merged-baseline.QBbT9z (same regex checks as previous run).
Final LaTeX pass has no missing glyphs or undefined references. Existing
small-caps italic substitutions and overfull boxes remain.

`bash tools/check-markdown-class.sh` — exit 0, fresh directory
`/tmp/pts-rk-markdown-class.rx9TmK`. All four cases PASS:
authors-lines, authors-default, authors-false, empty-date. Retained their logs.
Checks all author separator definitions, explicit/empty date values, unused
options and glyphs; fixtures cover three authors, shared affiliations, mixed
emails, a bare preamble filename and a preamble ending with makeatother.

Figure regression, run from latex/:

```sh
figure_test_dir=$(mktemp -d /tmp/pts-rk-figure-spacing-final.XXXXXX)
lualatex -interaction=nonstopmode -halt-on-error \
  -output-directory="$figure_test_dir" \
  ../verification/paper-title-figure-2026-10-16/figure-spacing.tex
```

Exit 0, /tmp/pts-rk-figure-spacing-final.AJmN7h. Actual preamble loaded;
old mathpar box height 42.944pt versus float-local layout 21.944pt: 21pt
removed padding. This isolated fixture has no bibliography pass; its Biber/
reference rerun notices are expected, not a failure of the complete paper.

PDFKit/Swift raster review of final title and Figure 2 on pages 1–2 confirms
separate author lines without list punctuation, date below affiliations,
and reduced internal math spacing with ordinary float/caption spacing intact.
Shell syntax and non-vendored diff whitespace checks pass. Copied upstream
package files retain their original comment-line trailing whitespace.

PDF SHA-256:
`cd324ebc373308d17bdd9ac22f037e9e0ca426c3a82280f9d931054c86d13bf6`.
Markdown source SHA-256:
`1e552874ef4801cd472c5e51a2b306e681a37ef1a172763113c41df4d53d130d`.
Traditional source unchanged, SHA-256:
`c721c21badf6380ed7e2d5e74e25610c1876ea286943eea6cba91ed91457e10b`.

## Intermediate failures/corrections

- D8wNI2 build: content checker failed because the Markdown copy omitted the
  traditional source's TOWER-hardness/preprocessing badge disclaimer. Synced
  the existing text; did not weaken the check.
- Class fixtures fLxicg: first actual error `spacefactor in vertical mode`
  after preamble makeatother; class now restores internal-name catcodes.
- Class fixtures KqKUv5: first actual error `url used in a moving argument`;
  protect email URLs when passing author metadata to authblk.
- l1SxRK build: checker rejected six rendered listings versus three source
  listings because a concurrent source spacing edit caused multiple hashed
  parser outputs. Final verification uses a new stable-source directory.
- Preliminary figure layout used mathparpagebreakable. Its negative lineskip
  tightened the float top too far; replaced with a non-display vbox using the
  public mathpartir bindings, preserving natural float separation.

No failed/intermediate PDF is the delivered artifact. Runtime/class local
changes and upstream pin/license notices are documented in PROVENANCE.md.
