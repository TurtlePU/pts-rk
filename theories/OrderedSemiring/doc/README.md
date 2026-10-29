# Building the proof note

From the repository root:

```sh
bash theories/OrderedSemiring/doc/build.sh
```

The source is the actual `../README.md`, beginning with
`\documentclass[preamble=doc/preamble.tex]{markdown}` and a YAML title/date.
LuaLaTeX reads `.md` directly; no alternate manuscript is maintained.
The script snapshots the source, preamble and vendored runtime in a fresh
directory under `/tmp`, runs three passes with `-no-shell-escape`, and retains
the exact command, versions, input checksums, all logs, recorder output and
exit code. A rendered-source guard rejects escaped TeX commands/math delimiters
and literal environment fences or empty mathpar blocks; the final log is checked for missing glyphs and
unresolved references. Only a successful PDF replaces `../README.pdf`. Failures and the
`--smoke` fixture never replace the existing note PDF.

## Requirements and dialect

A full TeX Live installation with LuaLaTeX and its standard packages is
required, together with Bash and `shasum`. Development testing uses TeX Live
2026 / LuaHBTeX 1.24.0; no network access or sibling repository is needed.
The runtime itself is pinned below. TeX packages and fonts come from the
installed TeX distribution, so byte-identical PDFs across TeX versions are
not claimed.

The small preamble uses article layout, AMS theorem/proof styles, parskip,
mathpartir, hyperlink support, titling/authblk and explicit Unicode mappings.
Fenced `coq` and other code blocks are **verbatim**, without a highlighter;
neither minted nor an external executable is needed. DejaVu Sans Mono, with
Latin Modern Math and DejaVu Sans fallbacks, covers mathematical Unicode
inside literal code. Font paths are resolved through the TeX distribution,
not through an optional user font installation.
The smoke fixture tests theorem fences, labels, source hyperlinks, mathpar,
the note's macros and Unicode code glyphs:

```sh
bash theories/OrderedSemiring/doc/build.sh --smoke
```

The PDF link renderer resolves relative source links against native proof commit
`5530d1e4130c28a741b48efbd902dd1127ac45c5`. Markdown source links remain relative
for repository browsing. File annotations contain absolute URLs, so they do
not rely on the reader supporting a document URI base. Local label references
retain the original renderer. The manuscript uses the local `smartHybrid` and
`fencedEnvs` extensions: percent macros, raw indented math environments,
`:::Theorem` / `:::Proof` fences, and `<#label>` references. Standard TeX Live's
Markdown package is not a drop-in replacement for this dialect.

## Runtime provenance and licensing

The eight runtime files in `runtime/` are byte-for-byte copies of `latex/`
from the original local `akuklev/pts-rk` checkout at commit
`ffa7131be99bcbef3f1a787fce23126c3d310811`, obtained on 2026-10-20. Those source
paths had no uncommitted changes. `runtime/SHA256SUMS` records and checks the
exact original bytes, including the non-UTF-8 Lua Unicode-data asset.

The retained [upstream provenance](runtime/markdown/PROVENANCE.md) records the
earlier copy from `akuklev/MLTT-S` at
`5879278756f8b80432467c1bbd23dc01b802d00b` and the subsequent local dialect fixes.
All existing copyright and MIT / LPPL notices remain in their original files.
The supplied `markdown.cls` states **no license**; this import records its
origin and does not invent or assign a license to it. No manuscript-specific
badges, bibliography, minted files, figures or other paper packages are copied.
