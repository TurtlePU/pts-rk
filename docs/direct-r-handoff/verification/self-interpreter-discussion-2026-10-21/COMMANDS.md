# Brown--Palsberg comparison and CPS feasibility discussion

21 October 2026; base/published HEAD
`ade6387531ac460c791e375419ef5724154d2ea0`.
Documentation-only work: research note/PDF, development README and live
handoff. No new CPS Rocq theorem, proof build or full CI run is claimed.
The user subsequently requested commit and push. The enclosing scoped commit
contains the discussion/PDF, development README, this evidence/inspection script
and only the new discussion entries from shared handoff files. Unrelated local
work is preserved. Publication command: `git push origin main`; verify the remote
tip with `git ls-remote origin refs/heads/main`.

## Research and mathematical scope

Read the user-supplied original Brown--Palsberg paper in full through PDFKit
text extraction, then checked the relevant definitions and claims against
Sections 3, 5--8 and Figure 4. Its local source is
`/Users/akuklev/Downloads/2914770.2837623.pdf`; extracted text is in the ignored
raw directory `_build/self-interpreter-discussion.GAMEGX/`.
Primary references are linked in the note:

- [Brown and Palsberg, POPL 2016](https://doi.org/10.1145/2837614.2837623),
  [author full version](https://web.cs.ucla.edu/~palsberg/paper/popl16-full.pdf).
  Fixed unquote versus a family; Theorems 6.2, 6.3 and 7.4; deep folds;
  answer-type-polymorphic CBN CPS, implemented but without a semantic proof.
- [Barthe, Hatcliff and Sørensen, 1999](https://www.cs.ru.nl/~freek/courses/tt-2017/papers/10.1023-A-1010000206149.pdf),
  Definition 11 and Sections 5--6. PTS-rk has no sort satisfying their
  logical-sort self-product condition. This blocks direct theorem
  instantiation, not CPS in general.
- [Bowman, Cong, Rioux and Ahmed, 2018](https://www.williamjbowman.com/resources/cps-sigma.pdf),
  introduction, target rules and dependent application analysis. Its extra
  target typing/equivalence rules cannot silently be imported here.

Compared with actual `FullDependentInterpreter`, `RankObstruction`,
`PHOASAlgebra`, Tarski product-law families and checked equality construction.
The added discussion derives continuation ranks from the original product rule,
gives a typed simple-type CBN candidate and a CBV conversion counterexample,
and identifies the dependent law-filling obligations. These calculations are
explicitly paper-level, not additions to the closed assumption reports.

## Build and visual checks

Executed from `/Users/akuklev/air/pts-rk`:

```sh
bash tools/build-self-interpreter-note.sh > _build/self-interpreter-discussion.GAMEGX/note-01.log 2>&1
bash tools/build-self-interpreter-note.sh > _build/self-interpreter-discussion.GAMEGX/note-02.log 2>&1
bash tools/build-self-interpreter-note.sh > _build/self-interpreter-discussion.GAMEGX/note-03.log 2>&1
```

All three exit 0, recorded in adjacent `.exit` files. Fresh directories:

1. `/tmp/pts-rk-self-note.cgbL3m`: first expanded discussion, 42 pages.
2. `/tmp/pts-rk-self-note.3C2A9C`: fixed Markdown quotation marks and an
   accented name in a link, and reflowed a pre-existing 50.46411pt overflow
   in the original open-source endpoint summary.
3. `/tmp/pts-rk-self-note.pVKShq`: added the explicit source-rank-1 family
   whose translated ranks grow with arity; final 42-page PDF.

No build failed or timed out. Build script uses fresh `latexmk -lualatex`
with nonstop/halt-on-error, and checks unresolved references/missing glyphs
before replacing the root PDF. Versions: Latexmk 4.88 (9 March 2026),
LuaHBTeX 1.24.0, TeX Live 2026, development id 7724.
Full TeX/build/version logs remain in those ignored temporary directories.

```sh
swift docs/direct-r-handoff/verification/self-interpreter-discussion-2026-10-21/INSPECT.swift /Users/akuklev/air/pts-rk/PTS-rk_self_interpreter.pdf /Users/akuklev/air/pts-rk/_build/self-interpreter-discussion.GAMEGX
rg -n 'Overfull|LaTeX Warning:|Missing character' /tmp/pts-rk-self-note.pVKShq/PTS-rk_self_interpreter.log
git diff --check
git diff --name-only HEAD -- 'theories/self_interpreter/*.v' theories/self_interpreter/dune 'theories/*.v' theories/NormalizationComplexity
git diff --cached --name-only
```

PDFKit inspection exits 0, extracts all text and renders pages 35--41
to PNGs. First inspection checked all seven pages; after final changes the
updated discussion and reflow were inspected again. The log search exits 1
(no matches): no overfull boxes, LaTeX warnings or missing glyphs. Benign
underfull boxes remain. Whitespace check exits 0. Both Git listings are
empty, confirming unchanged proof/build/core sources and an empty index.
The complete earlier fresh Rocq audit remains the evidence for unchanged
proofs; this prose update does not rerun it.

Final SHA256:

```text
9bbbb3cd11fd1f6c94827d49084ea5917522beefd6df7bedb6273d8599d5baef  PTS-rk_self_interpreter.tex
76e5057a44fa70995873c5441a37334b48305c8bcffede0eba4ecebde3d22cfc  PTS-rk_self_interpreter.pdf
5fc3541041f88ebc02435e66acf40a86e1a42eeea2db1fe62b65038052ee33fa  theories/self_interpreter/FullDependentInterpreter.v
38559f389ca8c7e7d343ddd4f0dfa95eefa5b030b2b2d06ef13b1c8855afd2f2  theories/self_interpreter/RecursiveQuotation.v
e7320f3c45a1a6b3bf5deff9fb6d8e1cb34fc57718d1763ec3901442c491db6d  theories/self_interpreter/Audit.v
c55de89ec762064229071882dd8b6409b079da7d7f2d1d13135b6973f3c1aba9  theories/self_interpreter/dune
```

Proof/Dune hashes match the published final-review record. Next exact review:
`git diff -- PTS-rk_self_interpreter.tex theories/self_interpreter/README.md`.
Next research obligation: an originally typed continuation product/application
handler plus a nontrivial contextual equality instance. General dependent CPS
and rank-only uniformity are not settled by this discussion.
