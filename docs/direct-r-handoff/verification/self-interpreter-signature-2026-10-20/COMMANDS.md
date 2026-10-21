# Finite dependent Tarski signature — checkpoint 2026-10-20

Base HEAD remains e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. This continuation
made no commit, push, merge or index mutation. The previous local Tarski
milestone and this extension remain uncommitted; unrelated existing work is
preserved. git diff --cached --stat produces no staged diff. This is evidence
for the actual current worktree, not a remote CI or publication claim.

## Constructive milestone and exact boundary

Five new modules, 1634 lines, construct the following in the ORIGINAL
annotated PTS with Typing.typ and RankSorts:

- TarskiLawFamily: one polymorphic product-law field per rank pair, exact
  declaration sort c+2 (c=max(a+1,b)), normal closed identity inhabitant,
  direct application typing and literal beta specialization.
- TarskiPalette: four finite layers for C_r, El_r, universe codes and their
  laws, r=0..k+1. Exactly 4(k+2) normal original declarations, lookup typings,
  constructive identity TypedSub and literal field substitution equations.
- TarskiSignature: append product constructors and law families for a,b<=k.
  Exactly 4(k+2)+2(k+1)^2 normal declarations. All six field classes have
  original lookup typings, including inherited universe fields. Actual
  identity TypedSub is proved without existence or law-inhabitation premises.
  Telescope closure preserves original typing, normality and syntax; actual
  identity application is directly typed and beta-recovers the replaced body.
- TarskiOperations: applied product/law fields and casted Abs/App are
  originally typed. Actual replacement by the finite identity substitution
  recovers plain dependent product, literal identity law, replaced f and
  its application to replaced u. Input redexes are retained; no semantic
  normal-form payload or eta expansion. Cast normality explicitly requires
  a normal decoded product annotation, not merely a normal family argument.
- IndexedCoherence: homogeneous equality composition and NONDEPENDENT map
  congruence at the same predicate level. Exact replacement and reflexivity
  computation are proved; arbitrary-proof identity equations are applied-only,
  without eta contraction or function extensionality.

This constructs the finite interface, not a complete dependent PHOAS quoter.
The pair budget only includes a,b<=k, whose output c is <=k+1; it does not
promise product closure for all available carrier ranks or out-of-range
selectors. Literal labels must also fit an independently sufficient ceiling.
Closing an independently typed body does not construct a body representing
every source derivation. Existing raw-HOAS/STLC syntax injectivity remains
unchanged, not silently extended to a new full-dependent translation.

First remaining goal: define derivation-directed full-dependent quotation
over this interface and generate internal substitution/conversion coherence,
particularly under binders. Prove annotation normality and identity recovery
for that construction. Neutral casts do not cancel definitionally; pointwise
family equality is not automatically equality of object-language functions.
No general dependent-PHOAS impossibility theorem has been claimed.

## Fresh integrated verification

Fresh absolute Dune build /tmp/pts-rk-self-signature-audit.qlUK8l: exit 0,
**527 closed assumption reports** = previous 418 + 68 new module reports
(8+12+11+22+15) + 41 new aggregate endpoints. Audit has 167 endpoints total.
Recursive core and aggregate checks pass; core inventory is byte-identical
to retained pristine upstream. Only unchanged upstream
functional_extensionality_dep occurs in the loaded-library inventory;
new theorem reports are closed and unsafe/type-in-type/positivity inventories
are empty. All 42 proof/Dune files are hash-stable through verification.

Original kernel, frozen PR #1 ZFC and NormalizationComplexity source
comparisons pass. Full local CI: exit 0, actionlint and **226/226 stages**,
including a fresh pristine upstream archive build. No checks weakened.
Final drivers had no failure or timeout. All module failures are retained.
Independent code/API and note reviews pass; post-review prose explicitly
states the annotation-normality premise and object-language function boundary.

Exact commands, versions, timings, hashes, source-safety scans and recursive
inventories: [final review](final-review/COMMANDS.md). Raw local-only ignored
evidence: _build/self-interpreter-signature-final-review.rFr76B. Its runners
were invoked as:

```sh
bash _build/self-interpreter-signature-final-review.rFr76B/AUDIT.sh
bash _build/self-interpreter-signature-final-review.rFr76B/CI.sh
```

The first uses fresh Dune @theories/self_interpreter/audit and recursive
rocq check; the second invokes literal bash tools/check-local-ci.sh. Pinned
versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1. All attempted module builds and exact contracts:
[law family](law-family/COMMANDS.md), [palette](palette/COMMANDS.md),
[coherence](coherence/COMMANDS.md), [signature](signature/COMMANDS.md),
[operations](operations/COMMANDS.md). No admissions, axioms or unsafe checks.

## Research note and actual PDF inspection

The note adds the six-layer context, field counts/sorts, polymorphic-law
inhabitant, constructive finite-signature theorem, actual operation equations
and internal composition/congruence. Abstract/status/programme and development
README match the proved boundary. The source remains in the pinned
LaTeX-Markdown dialect; no preamble or build-rule change was needed.

Three `bash tools/build-self-interpreter-note.sh` invocations all exit 0:

| Fresh directory | Actual PDF | Subsequent action |
| --- | --- | --- |
| /tmp/pts-rk-self-note.tG2lLY | 24 pages, 296404 bytes | Added precise local-normality caveat after independent prose review. |
| /tmp/pts-rk-self-note.TeNTK6 | 24 pages, 296653 bytes | Visual inspection found unsupported Markdown pipe table rendered as literal pipes; replaced it by a mathematical array. |
| /tmp/pts-rk-self-note.QLXAnK | 24 pages, 296163 bytes | Final checked PDF; six-layer table renders correctly. |

Final versions: Latexmk 4.88, LuaHBTeX 1.24.0, TeX Live 2026. No overfull
boxes, missing glyphs or unresolved references; five retained underfull
boxes have badness 1314, 2111, 1231, 1629 and 1348. Full build, engine and
version logs remain in each build directory. Final SHA-256:

```text
86307426b323cef3ae9619409a9ba74cd626b2380cf6482d279ce103d341fd5c  PTS-rk_self_interpreter.tex
d1fb93eb7bc961532e6393c257e22e12afbce6ef1adcb681f135c9a9060fbdb0  PTS-rk_self_interpreter.pdf
```

PDFKit extracted every page to pdf-text.txt; pages 18,19,20,24 were rendered
and visually inspected for table/equations, the theorem, coherence/boundary
and final status. The repeated inspection command (exit 0) is:

```sh
swift _build/self-interpreter-signature-final-review.rFr76B/INSPECT.swift /tmp/pts-rk-self-note.QLXAnK
```

Generated images and extracted text remain local to that fresh build folder.
The exact inspection source is retained in the ignored raw directory.

## Next exact fresh check

After the next meaningful proof change, use a NEW absolute build directory:

```sh
next_build=$(mktemp -d /tmp/pts-rk-self-next.XXXXXX)
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir="$next_build" --display=short --no-buffer @theories/self_interpreter/audit
```

Do not infer fresh Print Assumptions from cached success. Preserve both
uncommitted self-interpreter milestones and all unrelated changes.
