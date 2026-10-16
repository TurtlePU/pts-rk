# Paper and slides

- [paper.tex](paper.tex): PTS-rk calculus, metatheory, set model, normalization
  complexity, and related claims.
- [paper.pdf](paper.pdf): checked-in paper PDF.
- [paper-markdown.tex](paper-markdown.tex): MLTT-S-style Markdown–TeX version,
  with metadata, Markdown headings and fenced theorem/proof environments.
- [paper-markdown.pdf](paper-markdown.pdf): compiled version for visual review.
- [slides.tex](slides.tex) and [slides.pdf](slides.pdf): presentation sources
  and checked-in slides.

## Markdown–TeX paper

Build from the repository root with `bash tools/build-markdown-paper.sh`.
This requires LuaLaTeX, latexmk, Biber and the original article's packages
(including minted) and Python 3 for the content checks. The script uses a fresh
temporary directory, retains its logs, checks the source and rendered parser
output, and copies only a successful PDF into this directory. It does not
overwrite the traditional paper source or PDF.

The local [Markdown runtime provenance](markdown/PROVENANCE.md) pins the
user-specified MLTT-S template. The [preamble](tex/markdown-preamble.tex)
preserves the article's math macros, theorem counters and bibliography setup;
the metadata class changes the title/author header. Paragraphs use `parskip`:
no first-line indentation, with space between paragraphs.

The paper uses the bare `authorsonlines` flag (equivalent to
`authorsonlines=true`) in its class options. For structured YAML
authors this replaces all author separators with line breaks, without commas
or “and”; affiliations, ORCID and email remain attached to the same authors.
The default/`false` preserves the original inline layout. Both forms work with
`preamble=...` or a legacy bare preamble filename. Line mode moves 70% of the
affiliation skip to before the date, retaining 30% before affiliations.
YAML `date: October 16, 2026` is
rendered after authors and affiliations; an omitted/empty date stays hidden.

Native syntax:

- Citations: `[@key]`, `[@first; @second]`, or `[@key, Section 5]`.
- Lists: `- item` and `1. item`, with indented continuation/nesting.
- Figures: `:::Figure[ht] Caption {#figure-label}` … `:::`.
- Theorems/proofs: `:::Theorem[Title] {#theorem-label}` / `:::Proof` … `:::`.
- Heading labels: `## Subsection {#section-label}`; references: `<#label>`.
- Math: `$...$`, with Unicode symbols and quotation marks mapped to the
  original TeX glyphs. Ordinary displays use indented `%mathpar` blocks;
  two displays nested in a list retain `\[ ... \]` to delimit their bodies.
- Raw math/grammar environments: `%mathpar`, `%align`, `%align*`, `%gather*`,
  `%multline*`, `%tikzcd` or `%bnf`, followed by an indented body. Starred
  names use the small documented local parser extension. Standalone diagram
  blocks provide their own math mode and centering.
- Prose macros: `%PTSrk{}`, `%textsc{Conv}`, `%rocqformalised{...}`.
- Source listings: fenced `coq`, `agda` or `text` blocks.

Keep badges on their prose line, not on a separate line that the hybrid
parser interprets as a line break. Space binary operators/relations and colons,
attach their scripts directly, and put spaces after commas, not before them;
this also applies inside parentheses. Use `\rk{r}` and `\chNat{j + 1}` for
indexed ranks and Church natural-number types. Run
`python3 tools/format-paper-math.py --check` to check source spacing, or omit
`--check` to apply it. Literal code listings are preserved.
Do not pad the inside edges of `:::` fences with blank lines. Raw math
displays cancel the preceding Markdown paragraph separator, leaving TeX's
normal display spacing instead of adding an empty line before the formula.
Inside figures, mathpar uses its paragraph layout with no display skips,
because the float and caption already supply external spacing. This binding
is local to each figure and does not alter ordinary displays.

The dialect treats theorem optional arguments as literal TeX, so citations
and badges **inside those arguments** retain TeX command spelling. Numbered
equation-row labels likewise remain `\label` inside the raw `%align` body.
The separate `\PTSrk` macro prints PTS-$rk$ throughout prose and headings;
the existing mathematical `\PTS` notation remains available in formulas.
Underscore emphasis is disabled to prevent it from consuming subscripted math;
prose uses asterisks. No mathematical statements are rewritten.

Run `python3 tools/check-markdown-paper.py` from the repository root after
editing either version. It compares the ordered body character stream after
removing formatting/whitespace/punctuation and separately compares all 809
ordered non-name math fragments, including TeX punctuation and grouping.
The check normalizes Unicode aliases, whitespace, equivalent multiline
display wrappers and the requested prose-name macro. Restoring the second
author's editorial version reduced the previous count of 818 to 809.
With `--rendered-dir DIR`, it also checks that the parser did not escape math
commands/dollars or turn prose into indented code. This is not a pixel or PDF
equivalence test.
The two source versions are maintained explicitly, not auto-synchronized.
Run `bash tools/check-markdown-class.sh` for the five metadata/layout regression
fixtures in [tests/markdown](../tests/markdown/README.md).

The separate [harmonized arithmetic manuscript](../PTS_rk_interprets_Tarski_Mostowski_Robinson_arithmetic_R_harmonized.tex)
describes the relational and functional interpretations. The
[original arithmetic TeX](../docs/direct-r-handoff/reference/Direct_interpretation_of_R_in_PTS_rk.tex)
is retained as handoff provenance.

Rocq developments live under [theories](../theories/README.md). Their READMEs
state the exact checked claims and remaining boundaries; textual paper claims
do not automatically constitute formalized theorems. In particular, consult
the normalization cost/input conventions and external-hardness boundary, and
the set-model BZC foundation audit.

[Rocq reference coverage](ROCQ_REFERENCES.md) maps the paper's statements to
pinned source declarations and explains unbadged or only partially checked
claims. Badges on scoped formalisation notes do not certify the stronger
theorems that precede them.
