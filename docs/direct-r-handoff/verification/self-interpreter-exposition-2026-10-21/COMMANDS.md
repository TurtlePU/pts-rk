# Concise exposition of the completed dependent interpreter

21 October 2026, base `2da7627ede1e78fc7bdf1a3d48068b2acac1e07b`.
User request: streamline the research note, omit development history and
side investigations, retain the final interpreter and Brown--Palsberg discussion.

## Scope and review

The note now has seven sections: introduction; calculus/main theorem;
representation/evaluation; structural quotation; Brown--Palsberg comparison;
CPS feasibility; formalization and remaining questions. It has 729 source
lines and 3,929 whitespace-delimited words, versus 2,992 and 17,474 before.
The PDF has 11 pages, versus 42. The full previous exposition is in the base
commit. No proof file, Dune file, original kernel, or normalization development
was edited. Historical evidence and the detailed development README remain.

Removed intermediate weak/shallow encodings, standalone STLC quotation,
canonical-context detours, auxiliary coherence investigations, implementation
inventories and repeated status/boundary paragraphs. Retained the essential
Tarski/equality construction, finite numerical plans, explicit evaluator,
faithful HOAS tag, annotation-normal packaging, structural recursion and
strong recovery. The simply typed CPS calculation remains as evidence relevant
to the requested comparison, alongside its dependent-law obstruction and limits.

Checked the main theorem against `FullDependentInterpreter.every_closed_original`
and its type-recovery/injectivity/open endpoints; checked the six-rule argument
against `RecursiveQuotation`; checked the explicit evaluator against
`FaithfulProgramDecoder.decoder`. Reviewed the fixed-head argument, rank formulas,
and distinction between checked interpretation and paper-level CPS. The note
does not strengthen the result to rank-only uniformity, canonical quotation,
all-inhabitant syntax canonicity, or a proved dependent CPS transformation.

## Build and PDF inspection

From `/Users/akuklev/air/pts-rk`, for each `NN` in `01 02 03 04`:

```sh
bash tools/build-self-interpreter-note.sh > _build/self-interpreter-exposition.aNUfvF/note-NN.log 2>&1
```

All four exit 0; adjacent `.exit` files record the status. Fresh directories:

- `01`: `/tmp/pts-rk-self-note.0nQKdh` — complete rewrite.
- `02`: `/tmp/pts-rk-self-note.BOnTnH` — explicit faithful evaluator, expanded
  PHOAS acronym and well-formed-context qualification in the abstract.
- `03`: `/tmp/pts-rk-self-note.GkV9Kc` — clarify that tag normality concerns
  constructed tags, not arbitrary inhabitants of their type.
- `04`: `/tmp/pts-rk-self-note.0KH9o2` — remove a repeated self-interpretation
  paragraph already covered in the comparison.

No build failed or timed out. All PDFs have 11 pages. Versions: Latexmk 4.88
(9 March 2026), LuaHBTeX 1.24.0, TeX Live 2026, development id 7724.
The fresh directories retain full build/TeX/version logs; ignored raw records
are under `_build/self-interpreter-exposition.aNUfvF`.

```sh
swift docs/direct-r-handoff/verification/self-interpreter-exposition-2026-10-21/INSPECT.swift /Users/akuklev/air/pts-rk/PTS-rk_self_interpreter.pdf /Users/akuklev/air/pts-rk/_build/self-interpreter-exposition.aNUfvF
rg -n 'Overfull|Underfull|LaTeX Warning:|Missing character' /tmp/pts-rk-self-note.0KH9o2/PTS-rk_self_interpreter.log
git diff --check
git diff --quiet HEAD -- 'theories/self_interpreter/*.v' theories/self_interpreter/dune 'theories/*.v' theories/NormalizationComplexity
git diff --cached --name-only
```

PDFKit exits 0, extracts all text and renders all 11 pages. Every page was
visually checked during review, with changed portions checked again after the
final edits. The final warning search exits 1 (no matches); whitespace and proof
source comparisons exit 0. The index listing is empty. Existing proof audit
evidence remains applicable; no new Rocq/CI build is claimed or needed for
the editorial-only change. Unrelated local changes are preserved.

Final SHA256:

```text
aa98ccd26a4af40e1ef6104995939eb0c6fc318b2a38876fa4f8fd130a0dc948  PTS-rk_self_interpreter.tex
addf66305e5d63389bc902a3d353315a9173097ad6274b9582f3e700ccb3ee67  PTS-rk_self_interpreter.pdf
5fc3541041f88ebc02435e66acf40a86e1a42eeea2db1fe62b65038052ee33fa  theories/self_interpreter/FullDependentInterpreter.v
38559f389ca8c7e7d343ddd4f0dfa95eefa5b030b2b2d06ef13b1c8855afd2f2  theories/self_interpreter/RecursiveQuotation.v
41d5c1d2cd985e8be2db019ed4eb966cdbcd6142a615814184440710a837f4da  theories/self_interpreter/FaithfulProgramDecoder.v
```

## Publication

The user subsequently requested commit and push. The enclosing commit contains
the note/PDF, this evidence and inspection script, and only the new exposition
entries in STATE.md, DECISIONS.md and BUILD.md. Unrelated worktree changes are
excluded. Review the staged diff and run `git diff --cached --check`, then
`git commit -m "Self-interpreter: streamline the research exposition"` and
`git push origin main`. Confirm publication with
`git ls-remote origin refs/heads/main` matching `git rev-parse HEAD`.
