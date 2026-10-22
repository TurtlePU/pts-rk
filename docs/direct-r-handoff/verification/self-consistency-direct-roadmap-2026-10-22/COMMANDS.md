# Direct internal-consistency roadmap — 22 October 2026

## Scope and mathematical review

Documentation-only continuation at HEAD
cb76553b03d536743e36c4e2c7e5a1c7c1669bef. Added
`theories/self_consistency/DIRECT_ROADMAP.tex` and its eight-page PDF.
README links the recommended direct route; build-note.sh accepts an optional
validated `README`/`DIRECT_ROADMAP` stem and preserves its previous default.
The earlier README.tex/PDF and every proof development are unchanged in this
turn. Prior broad dirty/intent-to-add work is preserved. No staging, commit
or push; no new Rocq/Agda build or internal consistency theorem claimed.

Read the root/development READMEs, newest STATE/DECISIONS/BUILD, Dune and
pinned-toolchain records, current combinatory/self-interpreter notes, native
certificate/canonicity implementations and relevant draft sections. The
context-search skill was read; `jbcontext` is unavailable, so declaration
and adjacent-source discovery used rg and direct chunked reads.

Three independent read-only reviews checked native/external boundaries,
source-rank compression and fixed-rank packaging, and the primary Pakhomov
comparison. Incorporated corrections:

- The current fragment interpretation is external graded syntactic
  soundness, not an internal PTS proof or fixed finite first-order model.
- The direct target uses native certificates; the draft's typed-equality
  T^e target requires a separate comparison, not an asserted equivalence.
- GenericFold composition is syntactic; separately typed compatible
  operations, not heterogeneous composition typing, are available.
- Pakhomov transfer is restricted to predicate-only Pi1 sentences.
- Admission must cover rejected standard raw codes independently of
  checker acceptance; canonical acceptance needs actual proof terms.
- Raw terms inside conversion zigzags need not normalize; only typed
  subjects/types are normalized by the proposed soundness argument.
- The resource package can eliminate at Bottom:U1 without choosing a
  budget or extracting a positive witness from double negation. The
  schematic rank calculations were checked independently; they are not
  reported as new Rocq proofs.

## Primary references and source identities

Pakhomov, *A weak set theory that proves its own consistency*, v2:
https://arxiv.org/pdf/1907.00877v2. Inspected introduction, Lemma 3.11,
Lemma 4.1/Theorem 4.2/Remark 4.3, Lemma 5.2 and Corollary 5.3. These are
methodological references, not imported axioms or a claimed PTS transfer.

Original supplied draft:
`/Users/akuklev/Downloads/Logical_and_computational_strength_of_PTS_rk_Zermelo_revision.tex`
SHA256 0c3a1cd7671abf61e980426e9174344946691d2c260c9c74bdcb1bacb68435c8.
Relevant labels include eq:good, eq:delta, lem:internal-finite, eq:inv,
lem:inv, prop:adequate-height, lem:rank-compression, thm:bs-proved and
sec:internal-sn-scope. The original was neither edited nor copied.

Current CombinatoryPTS-rk.tex:
99154d57525bf12ee66dc19afcd223c916799b821f1da8984f89e40353980d42.
Current PTS-rk_self_interpreter.tex:
78e281fc4eaaacc27b89023af068abec7587e7c48988f5a67790ca1694c2fe55.
Complete reference hashes and proof manifests are in the raw directory below.

## Commands, attempts and final checks

Raw record: `_build/self-consistency-direct-roadmap.HYlErI`.
Toolchain: latexmk 4.88 (9 March 2026), LuaHBTeX 1.24.0/TeX Live 2026;
PDFKit via Apple Swift 6.3.3. Versions, individual UTC start/end, exit status
and driver logs are retained. Build command for each attempt:

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
```

Each generated directory retains complete build.log and DIRECT_ROADMAP.log.

| Attempt | UTC interval | Directory | Result |
| --- | --- | --- | --- |
| 01 | 11:56:03–11:56:08 | /tmp/pts-rk-consistency-note.thiN1S | build/initial validation 0 |
| 02 | 11:57:51–11:57:55 | /tmp/pts-rk-consistency-note.8axJaV | build/initial validation 0; PDF inspector found malformed displayed math |
| 03 | 11:59:11–11:59:14 | /tmp/pts-rk-consistency-note.RRRNN5 | exit 12: amsmath rejected tag in Markdown display renderer |
| 04 | 12:00:11–12:00:16 | /tmp/pts-rk-consistency-note.nypto3 | build 0, inspector 0 |
| 05 | 12:01:53–12:01:58 | /tmp/pts-rk-consistency-note.O8CmUV | final build 0, inspector 0 |

Attempt 02's nested math dollars in the equation tag caused literal TeX to
appear in the PDF. PDF inspection failed with exit 133 (Swift fatalError),
despite successful LaTeX compilation. Replacing the tag's contents exposed
the display renderer's unsupported tag (attempt 03). Removed the tag and
placed its name in surrounding prose; no mathematical claim changed.
An inspector invocation after failed attempt 03 correctly rejected the
retained old PDF again; both error logs are preserved. Attempt 05 only
removes duplicate manual/automatic subsection numbering. No check weakened.

Exact final inspection:

```sh
mkdir -p _build/self-consistency-direct-roadmap.HYlErI/pdf
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-direct-roadmap.HYlErI/pdf
```

Exit 0: eight nonempty pages, four links, primary citation present, required
scope/target/caveat text, no unrendered mathematical commands, every page
rendered. Pages 2/3/5/6/8 were reviewed visually at attempt 04; final
pages 1/4/5/7 reviewed after numbering cleanup. Equations, symbols, page
breaks and boundary statements are readable. Final TeX log has no overfull,
underfull, missing-character or LaTeX warning diagnostics.

`bash -n theories/self_consistency/build-note.sh` exits 0.
`bash theories/self_consistency/build-note.sh NOT_A_NOTE` exits 2 as intended,
before building or replacing any file. Scoped final whitespace passes.
244 proof/Dune source hashes covering the original kernel, normalization,
self-interpreter and combinatory Rocq/Agda sources compare byte-for-byte
before/after (cmp exit 0). No new theorem/kernel verification follows from
this documentation check; earlier proof audits remain distinct evidence.

Final SHA256:

```
37ee293ca952bac4a7507ad734be6d4f9c50b6266d211ef32e5eaff97bdf6a34  DIRECT_ROADMAP.tex
37c5618148dc74f12e797e5d21639e87ac6fda2e27c03d2f7d83d58cdb3119a3  DIRECT_ROADMAP.pdf
```

First next proof task: native certificate interface and complete-certificate
rank compression, with guarded internal finite-table correctness developed
in parallel. The main unresolved milestone is ONE fixed-rank internal
resource-bounded soundness term; an external per-bound family is insufficient.
