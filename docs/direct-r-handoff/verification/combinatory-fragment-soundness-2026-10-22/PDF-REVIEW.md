# Contextual fragment soundness: final PDF verification

Working directory: /Users/akuklev/air/pts-rk. Existing changes were
preserved; no staging, commit or push. Only the note, its build excerpt
list, the updated PDF and this review's artifacts were changed by the note
review task. Formal proof verification is recorded separately by the root.

## Final result

Final build directory: /tmp/pts-rk-combinatory-note.5WV08w.
2026-10-22 11:06:27–11:06:41 UTC; build and validation exit 0.
Inspector exit 0: 25 pages, complete three-page MM0 appendix,
23 Rocq / 27 Agda proof badges, 44 Agda links and 89 total links.
All linked proof-source targets exist. All 25 pages rendered into
/tmp/pts-rk-fragment-soundness-pdf.ZJ1BEm.

Visually inspected final pages 1, 12, 13, 16, 17, 18 and 19 with the image
viewer. These cover the abstract, total typed API, automatic rank coverage,
independent certificate grammar and interpreter snippets, joint finite
package bounds, external Void canonicity, the remaining fixed-finite-model
boundary and the corrected exact-quotient listing. All are legible, with
intact mathematical symbols and Agda highlighting and no clipped or
overlapping content. Copies are in rendered/page-N.png. Future work remains
on pages 20–21 and is checked requirement-by-requirement by the inspector.

No overfull box, missing glyph, undefined reference or highlighting fallback
remains. The unchanged underfull MM0 footnote diagnostic persists. No
validation check was disabled or loosened.

## Exact build and inspection commands

```sh
bash theories/CombinatoryLogic-rk/build-note.sh > docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/note-build.log 2>&1
swift docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/inspect.swift theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf /tmp/pts-rk-fragment-soundness-pdf.ZJ1BEm > docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/pdf-inspect.log 2>&1
bash -n theories/CombinatoryLogic-rk/build-note.sh
git diff --check -- theories/CombinatoryLogic-rk/CombinatoryPTS-rk.tex theories/CombinatoryLogic-rk/build-note.sh docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/inspect.swift docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/PDF-REVIEW.md
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/note-sources.sha256
```

Final exits: all 0. The builder's actual latexmk command, timestamps,
build/validation exits, full TeX/latexmk logs and tool versions are in the
adjacent note-* files. The exact extracted source snippets and the source
manifest used for this build are retained too. LuaHBTeX 1.24.0 / TeX Live
2026, latexmk 4.88, latexminted 0.7.0; the PDFKit inspector uses Swift 6.3.3.

## Failed attempts and repairs

1. First build /tmp/pts-rk-combinatory-note.7VWT2n: latexmk completed, but
   validation exited 1 for a 1.26472pt overfull vertical box on page 19.
   New pagination squeezed the unchanged exact-quotient listing and its
   link footnote. The old PDF was correctly retained. Shortening that
   introduction preserved its mathematical content and link while repairing
   the layout; the second full build passed. The initial build and TeX logs
   are note-attempt-01-build.log and note-attempt-01-tex.log.
2. Initial inspector exit 133: it read the retained OLD PDF and correctly
   rejected the missing contextual subsection. Its output is preserved as
   pdf-attempt-01-inspect.log.
3. Second inspector exit 133: the new scope check sought the contiguous
   text "internal reflection", split by a PDF line break. The inspector now
   applies its existing whitespace/hyphenation normalization to that scope
   check as well. All content assertions remain present; the subsequent
   full check passed. Output: pdf-attempt-02-inspect.log.

The updated inspector retains the prior Hilbert/MM0, BCKW, section ordering,
total typed API, Church compiler, references and every future-work check.
It replaces obsolete model-gap phrases with the proved contextual result
and explicit fixed-finite-model caveat, adds the new section and seven
proof badges, and verifies every Agda link target. The old compiler gaps
and internal-reflection boundary remain required. No compiler timeout.

## Final hashes

See note-sources.sha256 for the full manifest, including build scripts and
inspector. The TeX hash is
99154d57525bf12ee66dc19afcd223c916799b821f1da8984f89e40353980d42;
the PDF hash is
1a4a8881ec4a13704f2ed0acd038b4d5b88128ae45360a85007296a36898cc82.

No claim of fixed finite first-order model existence or internal PTS
consistency is introduced by this note update.
