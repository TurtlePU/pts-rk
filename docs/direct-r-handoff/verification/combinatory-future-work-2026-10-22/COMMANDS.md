# Future-work note update — 22 October 2026

## Commands

From the repository root:

```sh
bash theories/CombinatoryLogic-rk/build-note.sh
future_pdf_dir=$(mktemp -d /tmp/pts-rk-future-work-review.XXXXXX)
swift docs/direct-r-handoff/verification/combinatory-future-work-2026-10-22/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf "$future_pdf_dir"
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/source-before.log
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/agda-sources.sha256
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-future-work-2026-10-22/note-sources.sha256
git diff --check -- theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex \
  theories/CombinatoryLogic-rk/EVIDENCE.md docs/direct-r-handoff/STATE.md \
  docs/direct-r-handoff/BUILD.md docs/direct-r-handoff/DECISIONS.md
```

All final commands exit 0. New Markdown/Swift files were separately checked
for trailing whitespace. Raw logs retain their generated formatting.

## Results

- Final build: /tmp/pts-rk-combinatory-note.nY0x2K,
  09:30:31–09:30:45 UTC, build and validation exit 0. LuaHBTeX 1.24.0,
  TeX Live 2026, latexmk 4.88, latexminted 0.7.0, Pygments 2.19.2.
  No missing glyphs, overfull boxes, undefined references or highlighting
  failures. Existing MM0 footnote underfull diagnostic is unchanged.
- Final inspector: /tmp/pts-rk-future-work-review.ni5QCq, exit 0.
  22 pages, 3-page complete MM0 appendix, 23 Rocq badges, 11 Agda badges,
  21 Agda links and 66 total links. All pages rendered, future-work pages
  17–18 visually inspected. All previous checks remain, with additional
  checks for each new requirement, section order and the new paper link.
- First build .JxOvX1, 09:27:51–09:28:05 UTC, also passed. Visual inspection
  found an isolated final word of point 1 on the next page; shortening the
  sentence removed it. No mathematical content was removed.
- First inspector /tmp/pts-rk-future-work-review.f0eWtf exited 133 because
  extracted text hyphenated Noncollapsed across a line break. Normalizing
  PDF line-break hyphenation fixed the test without removing it. The
  intermediate .D6x1jK and final .ni5QCq inspections exited 0.
- All 24 Rocq sources and Dune match the prior fresh/pristine manifest;
  all 25 Agda sources match the prior safe-closure manifest. No proof code
  changed and no new native/Agda/MM0/full-CI run is claimed. Existing broad
  dirty work preserved; no staging, commit or push.

## Scope and source

Read the primary paper at https://arxiv.org/abs/2102.00905 and its full text,
especially Sections 2–3 and Theorem 7. The method removes implicit
definitional conversion in favour of explicit propositional computation.
Its adaptation to the rank system is a future theorem, not an existing one.
The complexity targets count full encoded input/certificate size.

The arithmetic proposal retains every requested condition: partial functions,
graph extension, computational completeness from a finite term basis,
reflexivity/transitivity/substitution and suitable induction, finite core
axioms plus exists_n, finite models for each schema truncation, and at-most-
quadratic proof checking. The collapse alternative is explicit; noncollapsed
finite approximations are separately marked as stronger. The interpretation
direction is from the objective PTS-rk variant into this arithmetic.
No new formal axioms, original-kernel changes or proved results are asserted.
