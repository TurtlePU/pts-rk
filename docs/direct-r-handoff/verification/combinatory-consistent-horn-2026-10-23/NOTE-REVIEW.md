# Constrained finite-model note: build and visual review

The final note replaces positive-only Horn satisfiability as consistency
evidence with explicit Void denials and a separately proved native consistency
bridge. It distinguishes exact finite ground models, signed completion on a
finite observation language, external table compilation to original PTS,
and exhaustive verification of supplied finite semantic candidates. Neither
the PTS/MM0 candidate construction nor uniform internal reflection is claimed.
The finite total-untyped-K equality obstruction is explicitly separated from
typed/graded application and directed reduction. Selinger's full primary
paper is reference 11, linked to the author's `papers/cmaa.pdf`.

## Commands and attempts

From the repository root, each fresh build used:

```sh
bash theories/CombinatoryLogic-rk/build-note.sh > docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23/note-driver-NN.log 2>&1
```

The script itself invokes
`latexmk -lualatex -interaction=nonstopmode -halt-on-error CombinatoryPTS-rk.tex`
inside a fresh temporary directory and validates missing references/glyphs,
overfull boxes and Pygments-highlighted Agda output before replacing the PDF.
Compiler commands, versions, times, full logs and numeric statuses are copied
in `note-build-01`, `note-build-02` and `note-build-03`.

1. `01`: `/tmp/pts-rk-combinatory-note.Qzw9fb`,
   06:43:50–06:44:05 UTC, compiler/script exit 0. The initial inspector also
   exited 0, but visual inspection FAILED: the signed-diagram display rendered
   as literal TeX because a line ended with a lone backslash. This was not
   accepted as a fully validated PDF. The source now uses `\quad\cup\quad`;
   the inspector additionally rejects literal display delimiters and raw
   `\setminus`, `\cup`, and `\Longleftrightarrow` in rendered prose.
2. `02`: `/tmp/pts-rk-combinatory-note.CegXnQ`,
   06:45:23–06:45:38 UTC, build and strengthened inspector exit 0.
   Corrected signed diagram visually reviewed. Preliminary PDF: 26 pages,
   29 Rocq badges, 27 Agda badges, 97 links. This predates the final quantified
   candidate-checker subsection and is superseded, not the final checkpoint.
3. `03`: `/tmp/pts-rk-combinatory-note.gKhpiC`,
   06:48:39–06:48:53 UTC, final build and strengthened inspector exit 0.
   **27 pages, 30 Rocq badges, 27 Agda badges, 44 Agda links, 98 links.**
   The complete MM0 appendix remains three pages. All page renders succeeded.

Each inspector invocation used the matching temporary build directory:

```sh
mkdir -p BUILD/inspection
swift docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf BUILD/inspection \
  > docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23/note-inspect-NN.log 2>&1
```

The inspector preserves the preceding checkpoint's heading-order, old
totality/model-soundness boundaries, full MM0 listing and three-page limit,
notation, reference/source-link existence and future-work requirements.
It additionally checks the constrained-model statements, negative completion
scope, external-only saturation compilation, finite-candidate caveat, equality
diagram boundary, new proof links and absence of the superseded all-true
consistency argument. Expected counts changed only to match the new badges.

Final visual review: pages **1, 18, 19, 20, 21, 23, 24**. The abstract,
K obstruction, denials, saturation, signed-diagram formula, Church programs,
all-valuations candidate checker and its scope, existing highlighted Agda
excerpt, future-work conclusion and new reference are legible; no clipping,
unprocessed math or missing glyphs was observed. Those selected renders,
all extracted text and link inventory are retained in `note-final/`.

Toolchain: Latexmk 4.88, LuaHBTeX 1.24.0/TeX Live 2026,
latexminted 0.7.0 and Pygments 2.19.2. Full versions are archived with each
build. No TeX/Markdown runtime or proof source changed for these builds.

## Final stability

The following all exited 0 after the final build and visual review:

```sh
bash -n theories/CombinatoryLogic-rk/build-note.sh
git diff --check -- theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex theories/CombinatoryLogic-rk/build-note.sh docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23/inspect.swift
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23/note-final-sha256.txt
```

Final source SHA256:
`c86f6e2e598e40b2aa8392af522e14de4e33f3250e37da681bed8c3bf267a0d0`.
Final PDF SHA256:
`d5caf0085914d39e8621409eaf9a617f8189d435fdae17d9aa3548bc5ec2ca92`.
The adjacent manifest also fixes the build script and inspector. No staging,
commit, push or cleanup was performed.
