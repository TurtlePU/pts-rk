# Sources, theorem map and verification

## Direct route without H or EA intermediaries

[DIRECT_ROADMAP.tex](DIRECT_ROADMAP.tex) and [its PDF](DIRECT_ROADMAP.pdf)
give the current recommended direct programme: independent native certificate
codes, elementary source-rank compression, guarded internal finite reasoning,
one fixed-type resource interface, internal bounded proof/history soundness,
terminal separation and negative resource elimination. Neither the guarded
soundness theorem nor a consistency inhabitant is reported as proved.

The roadmap corrects the starting-point distinction: current combinatory
soundness is external Agda soundness in graded finite syntactic carriers,
not yet internal PTS soundness or fixed finite first-order models. It also
distinguishes the new structural consistency sentence from the earlier
finite-ordinal target and includes the conditional incompleteness audit.
Three independent source/mathematical reviews checked these boundaries.

Final command `bash theories/self_consistency/build-note.sh DIRECT_ROADMAP`
exits 0, 12:01:53–12:01:58 UTC, in
`/tmp/pts-rk-consistency-note.O8CmUV`: eight pages, clean layout/reference/
glyph diagnostics. The PDFKit inspector exits 0, checks required text,
primary reference and mathematical rendering, and renders every page.
Changed formulas and final pagination were visually reviewed. An earlier
malformed equation tag was detected and corrected; all failed/successful
attempts and exact commands are retained in
[the direct-roadmap verification record](../../docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/COMMANDS.md).

```
37ee293ca952bac4a7507ad734be6d4f9c50b6266d211ef32e5eaff97bdf6a34  DIRECT_ROADMAP.tex
37c5618148dc74f12e797e5d21639e87ac6fda2e27c03d2f7d83d58cdb3119a3  DIRECT_ROADMAP.pdf
```

All 244 inspected proof/Dune sources match their before/after hashes.
No Rocq/Agda proof sources, original draft, or earlier README.tex/PDF were
changed in this turn; no new proof build, staging, commit or push. The new
optional build-script argument preserves the old no-argument behaviour.

## Follow-up: shared tag-free folds and structural codes

The shared-algebra continuation adds a short paragraph to the uniform-PHOAS
analysis: `UnifiedAlgebra` gives tag-free full-dependent execution, while
STLC and finite-dictionary combinatory folds supply actual alternative
interpretations. These results do not supply acceptance soundness, a
rank-only dependent signature, native combinatory completeness, or an
internal consistency inhabitant. Structural recoding must still match the
specified arithmetic sentence on all admitted certificates and traces.

`bash theories/self_consistency/build-note.sh` exits 0 in
`/tmp/pts-rk-consistency-note.7vQRc9`: ten pages, no overfull/underfull,
undefined-reference or missing-glyph diagnostics. The new fold-audit
`inspect.swift` exits 0, renders all ten pages and checks required text;
page 7's added passage was visually inspected. Raw logs and renders:
`_build/self-interpreter-fold-audit.7pRHdb/consistency-note.log` and
`consistency-pdf/`. Current document SHA256:

```
7c84b193ff70194c326fbed0ecff18c948d0ab2771bf5e15afa0f9cd5c0c7bf5  README.tex
a6b58a5e04fa80ebcb7cd5cdfb1b9a9d08355774106db49c3a917ab433dedfb6  README.pdf
```

No self_consistency Rocq library or theorem has been introduced.
Proof evidence belongs to the separate self-interpreter fold audit.

## Follow-up: fixed fragment execution interface

The original five-file documentation checkpoint below was committed as
`cb76553b03d536743e36c4e2c7e5a1c7c1669bef`, at the user's subsequent request.
No push was requested. The note now reflects the new fixed closure interface
and its precise difference from internal proof-code reification. This changes
the status of the second uniformity, not the internal consistency target.
The new proof evidence belongs to
[the self-interpreter continuation](../../docs/direct-r-handoff/verification/self-interpreter-uniform-interface-2026-10-22/COMMANDS.md),
not to a self_consistency Rocq library; none has been created here.

Follow-up declarations: `FragmentClosureInterpreter.every_bounded_original`,
`FixedInterface.inhabited_iff`, and
`BudgetInternalization.no_unbounded_internal_strong_reification`.

Document attempts: `/tmp/pts-rk-consistency-note.OmKWDX` failed overflow
validation (exit 1), preserving the preceding PDF; the long qualified theorem
name was split in prose. `/tmp/pts-rk-consistency-note.L5IDV1` built successfully
but had one underfull paragraph. `/tmp/pts-rk-consistency-note.7u3pxt` is the
final successful build: ten pages, no overflow/underflow/reference/glyph
warnings. PDFKit section/link/text/render validation passes. Inspection output
is under `_build/self-interpreter-uniform-interface-2026-10-22/consistency-note`.
Final follow-up SHA-256 values:

```
cb1b496a89d30d6edb8cc26ba3972ec54a717297acacf5dc5da66ec242e1e73b  README.tex
f37a83f973a114b6d6aa0c0287027a4c80c12334846b8786d6792ce89b66f149  README.pdf
```

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
