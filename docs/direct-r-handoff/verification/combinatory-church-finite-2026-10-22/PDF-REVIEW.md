# Church finite compilation note: PDF inspection

Final build: `/tmp/pts-rk-combinatory-note.2lG4Vk`.
The published PDF is byte-identical to that build's PDF (`cmp`, exit 0).

Command, from the repository root:

```sh
swift docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/inspect.swift theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf /Users/akuklev/air/pts-rk/_build/combinatory-church-finite-pdf-final.DKzMEm
```

Exit 0, completed by 2026-10-22 09:04:36 UTC. The inspector checks required
headings and their order, compilation/consistency proof boundaries, source
and reference links, all local proof targets, appendix completeness, and
absence of literal unprocessed `\texttt{` commands. It renders every page.

- 21 pages, including the complete three-page MM0 appendix.
- 23 Rocq proof/source links and 11 explicitly detected Agda proof badges.
- 21 total Agda links and 65 links overall.
- ChurchFinite.v, ChurchFinite.agda, FiniteMachine.agda, and the Pakhomov
  arXiv:1907.00877v2 reference are present and linked.
- Pages 13–16 and 18 visually inspected after the final rebuild: formulas,
  source highlighting, wrapped Agda comments, footnotes and new references
  are readable and unclipped.

Final output: `_build/combinatory-church-finite-pdf-final.DKzMEm/`, containing
all 21 PNG renders, extracted text/links, and `inspect.log`. The one-line
result is also retained as `pdf-inspect.log` beside this review.

The earlier build `/tmp/pts-rk-combinatory-note.IKoScA` exposed four raw
`\texttt{...}` commands in Markdown prose on page 14. They were changed to
Markdown inline code by the root agent and verified fixed in the final PDF.
Earlier inspection/renders remain at `_build/combinatory-church-finite-pdf.2wldgi/`.
The final TeX log retains one underfull hbox associated with the long MM0
regression-source footnote. It reports no overfull box, missing glyph,
undefined reference, or warning diagnostic.

Final PDF SHA256:
`94b80b6ebb29761e3bcc94fbf81cfa42aa5ce5c8a3e2095fe42c2fdfa1bf833c`.

Inspector SHA256:
`67a4b72c191b1b271c2ea0f600c87973541740b8d27919301ee07f72863dd4fc`.
