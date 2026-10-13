# Repository guidance

## Project and layout

This repository studies a pure type system with ranks as sorts (PTS-rk).
The main formalisation is in Rocq/Coq; it is accompanied by Agda code and
a LaTeX paper and slides.

- `theories/`: Rocq sources, built as the `PTSrk` theory.
  - `Syntax.v`: finite indices, terms, renaming, and substitution.
  - `AbstractRewriting.v`, `Congruence.v`, `Reduction.v`, `Confluence.v`,
    `DefEq.v`: rewriting infrastructure and definitional equality.
  - `Context.v`, `Typing.v`, `Inversions.v`, `Preservation.v`: contexts,
    typing, inversion lemmas, and subject reduction.
  - `SN.v`, `Ranks.v`: strong normalisation infrastructure and the
    rank-based system's strong normalisation theorem.
- `rank.agda`: separate Agda development using the Agda standard library;
  it is not part of the Dune build.
- `latex/paper.tex`, `latex/slides.tex`, `latex/bibliography.bib`: research
  text, presentation, and references. The PDFs are tracked.
- `dune-project`, `theories/dune`: package, dependencies, and explicit
  Rocq module list.

## Build and validation

Run commands from the repository root unless noted otherwise.

- `dune build`: compile the Rocq development. The project declares Dune
  language 3.23 and Rocq extension 0.13, and requires Rocq's `Stdlib` and
  the Equations package (`rocq-equations`). Use a compatible toolchain.
- `agda rank.agda`: check the Agda development with the standard library
  installed and configured on Agda's library search path.
- From `latex/`, run `latexmk paper.tex` or `latexmk slides.tex` to build
  the corresponding document. The local `.latexmkrc` enables PDF output
  and directs auxiliary files to `../_build`. The paper uses biblatex
  with Biber; the slides require Russian language support.
- `git diff --check`: check patch whitespace before handing off changes.

There is no separate test suite or CI configuration in the current
repository. For proof changes, successful compilation of the full Rocq
theory is the primary validation. Validate Agda and LaTeX changes with
their respective tools. Report missing tools or dependencies explicitly;
do not describe an unrun check as passing.

## Editing proofs

- Preserve the existing Unicode notation, identifiers, and local proof
  style. Keep changes focused; avoid reformatting unrelated proofs.
- Reuse the existing substitution and renaming lemmas, hint databases,
  and tactics (such as `syntax_simp`) before introducing new machinery.
- Follow nearby imports and Equations usage, including dependent
  elimination and generated signatures where appropriate.
- Preserve theorem statements and assumptions unless changing them is
  part of the task. Do not make a proof compile by adding `Admitted`,
  `admit`, new axioms, or unchecked shortcuts.
- Add new Rocq modules to the explicit module list in `theories/dune`.
- Changes to shared syntax, contexts, or reduction can affect most of
  the theory; check downstream proofs through the full build.

## Research text and generated files

- Keep mathematical claims and notation consistent with the formal
  development. Preserve the language of the document being edited.
- Do not invent citations or silently fill research placeholders with
  unsupported claims.
- Do not hand-edit generated PDFs. Regenerate tracked PDFs only when
  relevant to the requested document update, and review the resulting
  diff for unintended artifacts.
- Keep build output out of source changes. `_build`, `*.synctex.gz`, and
  `*.agdai` are already ignored.
