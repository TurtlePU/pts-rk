# Markdown-TeX support

Copied from [akuklev/MLTT-S](https://github.com/akuklev/MLTT-S/tree/5879278756f8b80432467c1bbd23dc01b802d00b)
on 2026-10-15, including the sibling `markdown.cls` and `markdown.sty` files.
The reference manuscript is `main.tex` at that commit.

The class implements the metadata header and an external LaTeX preamble.
The Markdown package includes the reference's `smartHybrid` and `fencedEnvs`
extensions. These are required by the manuscript; the standard TeX Live
package does not provide the same dialect. They are retained locally so the
build has no dependency on a sibling checkout or a mutable remote branch.

Local extension (2026-10-15): the smart-hybrid offside environment-name parser
accepts an optional trailing `*`, enabling native `%align*`, `%gather*` and
`%multline*` blocks. Nested list displays
retain explicit math delimiters: this parser's raw body consumes any indented
line, including subsequent list prose, rather than measuring relative indent.

Local spacing fix (2026-10-16): raw math display environments request the
parser's existing `undosep` cancellation, removing the immediately preceding
Markdown paragraph/block separator. TeX then places its ordinary display glue
after the preceding text instead of starting a new empty paragraph first.
This applies to mathpar, align, gather, multline and equation (including
starred names), not arbitrary raw environments. Other runtime files are unchanged.

The same fix accepts a closing `:::` fence as a raw-environment boundary,
in addition to a blank line or EOF. This lets an indented math block end a
fenced theorem without a padding blank line; otherwise the block parser fails
and can spend excessive time backtracking through the document. The closing
fence is only looked ahead at, not consumed by the raw-environment parser.

The package files retain their copyright, MIT and/or LPPL 1.3-or-later notices.
No license is stated in the reference's `markdown.cls`; it was copied from
the user-specified template, with the following local changes (2026-10-16):

- Boolean `authorsonlines` / `authorsonlines=true` option (default false) replaces authblk's
  author-list separators with protected line breaks before emitting metadata.
- In line mode, move 70% of the configured affiliation skip to before the
  date, leaving 30% before affiliations; default/false layout is unchanged.
  Recognize the bare flag in the legacy preamble-option parser as well.
- Restore `\makeatletter` after the external preamble, which may itself
  legitimately use `\makeatother`.
- Protect email `\url` when authblk builds its moving author arguments, so
  the class works with the plain url package as well as hyperref.

Explicit YAML dates use the existing metadata path and are displayed after
the author/affiliation section. Five compiled regression fixtures cover the
option's true/default/false settings, explicit/empty dates and email handling.
The PTS-rk article's packages and theorem setup remain in
`../tex/markdown-preamble.tex`.
