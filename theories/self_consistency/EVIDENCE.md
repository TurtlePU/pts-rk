# Sources, theorem map and verification

## Provenance

This is a documentation-only research checkpoint, 22 October 2026, based on
repository commit `72c9f337224eef9922e3d1949e15bcd4148224b7`. Existing unrelated
documentation, CI and BZC work is preserved. No commit or push was requested
for this checkpoint. No new Rocq theorem, EA derivation or PTS consistency
inhabitant is claimed.

Input supplied by the user:
`/Users/akuklev/Downloads/Logical_and_computational_strength_of_PTS_rk_Zermelo_revision.tex`.
SHA-256:
`0c3a1cd7671abf61e980426e9174344946691d2c260c9c74bdcb1bacb68435c8`.
The original file is unchanged and is not copied into this directory.

Relevant draft labels, in dependency order:

- `eq:internal-target`, `def:bs`, `thm:conditional-self-consistency`,
  `prop:adequate-height` (lines 1068–1290).
- `lem:rank-compression` (1295–1327).
- `lem:ea-constant-separation`, `lem:tagged-projection`,
  `sec:graded-calculus` (1665–1920).
- `lem:source-tag-coherence`, `lem:source-elaboration` (1922–2218).
- `lem:structural-templates`, `lem:aux-one-step`, `lem:active-passes`,
  `lem:aux-terminal`, `thm:bs-proved` (2220–2468).
- `cor:internal-consistency-completed`, `sec:internal-sn-scope`,
  `prop:no-pi2-transfer` and review limitations (2470–2679).

The former WC formulation, quantitative residual joins, unrelated complexity
hardness and model appendices are excluded from the core proof dependency
chain. The note preserves the draft's status as an unformalized argument.

Primary external reference checked directly:
[Fedor Pakhomov, *A weak set theory that proves its own consistency*,
arXiv:1907.00877v2](https://arxiv.org/pdf/1907.00877v2).
Section 2 defines the higher-order theory; Lemma 3.11 (page 18) is the
predicate-only Pi1 transfer using S; Corollary 5.3 (page 22) uses 2S and
the first-order theory. Appendix A's comparison with R is first-order.
These results are identified as external mathematical dependencies, not Rocq
axioms. Checking the citation does not formalize its proof.

## Repository declarations inspected

- [BoundedNormalization.v](../NormalizationComplexity/BoundedNormalization.v):
  `fixed_rank_normalization`.
- [Normalization.v](../NormalizationComplexity/Normalization.v):
  `normalization_in_TOWER`, `rank_bound_in_linear_time`.
- [FullSource.v](../self_interpreter/FullSource.v): `derivation_iff`.
- [DirectRDerivationCertificates.v](../Interpretation_of_R/DirectRDerivationCertificates.v):
  `DerivationCertificates.derive_sound`, `derive_complete`.
- [OriginalTypecheck.v](../self_interpreter/OriginalTypecheck.v): `check_iff`.
- [FullDependentInterpreter.v](../self_interpreter/FullDependentInterpreter.v):
  `every_closed_original`, `every_original`.
- [CappedDependentInterpreter.v](../self_interpreter/CappedDependentInterpreter.v):
  `every_bounded_original`, `fragments_cover`, `quote_at`.
- [CappedInterpreter.v](../self_interpreter/CappedInterpreter.v): `rank_uniform`.
- [DependentProgramDecoder.v](../self_interpreter/DependentProgramDecoder.v):
  `evaluate_typed`, `decoder_typed`.
- [PlanNonuniformity.v](../self_interpreter/PlanNonuniformity.v),
  [FiniteCoherenceCatalogue.v](../self_interpreter/FiniteCoherenceCatalogue.v),
  [LiteralObstruction.v](../self_interpreter/LiteralObstruction.v): scope of
  plan, literal-field and sort-literal obstructions.
- [DirectRFunctionalDeduction.v](../Interpretation_of_R/functional/DirectRFunctionalDeduction.v):
  `FunctionalDeduction.sentence_preservation`.
- [DirectRTheorem7.v](../Interpretation_of_R/functional/DirectRTheorem7.v):
  `Theorem7.effective_deduction`, `theorem5_target`, `theorem7`.
- The normalization/self-interpreter/arithmetic READMEs and BZC foundation audit
  distinguish implemented results, unformalized elementary representability,
  native semantic agreement and material deduction.

No proof files or Dune files changed, so no new Rocq build or assumption audit
was run or claimed. Historical audits remain in the corresponding development
handoff records; they do not verify any new consistency proof.

## Document validation

Build command: `bash theories/self_consistency/build-note.sh`.
The script uses the existing repository Markdown runtime and development
preamble, retains intermediate output in a scoped temporary directory, and
publishes the PDF only after compilation and reference/glyph/overflow checks.
Tool versions: latexmk 4.88, LuaHBTeX 1.24.0, TeX Live 2026.

Recorded attempts:

- `/tmp/pts-rk-consistency-note.F85DFD`: exit 12, unsupported `\tag` inside
  the Markdown display renderer. Replaced by explicit parenthesized labels.
- `/tmp/pts-rk-consistency-note.NFldQl`: TeX exit 0, validation exit 1,
  overlong code-name prose in the roadmap. PDF not published.
- `/tmp/pts-rk-consistency-note.CQHNKd`: TeX exit 0, validation exit 1,
  overlong code-name prose in the theorem map. PDF not published.
- `/tmp/pts-rk-consistency-note.qZxUGL`: build and validation exit 0,
  ten pages; PDFKit text, source-link and render checks passed. The final
  provenance paragraph was subsequently shortened to avoid a sparse last page.
- `/tmp/pts-rk-consistency-note.KlGtoS`: final build and validation exit 0,
  nine pages. No overfull/underfull boxes, LaTeX warnings or missing glyphs.
  PDFKit text/section/source-link/render inspection exits 0; pages 1, 3, 5,
  7 and 9 were visually inspected. `bash -n build-note.sh` passes.

Final SHA-256 values:

```
4f12ef2c225d0f8f7db5fe8ea2850d5120b7094fcb8c73801487c6949076d382  README.tex
6a8fc111e750ad9e74a706cb2d24a2047dbb935bbf31d33105a46ebcf7a30a04  README.pdf
```

PDF inspection command:

```sh
swift _build/self-consistency-note-2026-10-22/inspect.swift \
  theories/self_consistency/README.pdf \
  _build/self-consistency-note-2026-10-22
```

Its text extraction, checked section/link coverage and sample page renders are
retained under `_build/self-consistency-note-2026-10-22`. This ignored directory
contains document-inspection artifacts, not proof evidence. The small temporary
TeX directories retain their build logs. No large new proof caches were created.

Three independent read-only reviews checked draft fidelity, repository theorem
contracts and the external transfer boundary. They prompted explicit tower-seed
comparison, higher-order comprehension/class-separation definitions, and the
internal link from the actual trace predicate to accepted PHOAS codes.
These reviews are mathematical/document checks, not formal verification.

Final repository checks: `bash -n` exit 0; tracked-document `git diff --check`
exit 0; proof/Dune comparison against HEAD exit 0; index empty. The four
new text files have no whitespace diagnostics from `git diff --no-index
--check /dev/null FILE` (exit 1 denotes the new-file differences). An initial
`set -e` wrapper stopped at that expected status; the checks were then run
individually. The final manuscript/PDF hashes still match the values above.
