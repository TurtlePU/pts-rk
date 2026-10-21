# Object-language Tarski infrastructure checkpoint — 2026-10-20

Base HEAD and confirmed origin/main:
e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. The previously pending ordinary
push completed with exit 0; an independent git ls-remote confirmed the same
hash. This subsequent proof continuation is uncommitted, with an empty
index. Unrelated pre-existing BZC, documentation, tool and log changes remain
preserved. No further publication is claimed.

## Checked mathematical milestone

Seven new modules construct actual annotated original PTS terms and prove
their original Typing.typ judgments, exact ranks and computation laws:

- IndexedEquality: predicatively rank-indexed Leibniz equality, reflexivity,
  actual application transport and substitution/normality laws.
- TarskiProducts: genuine dependent product-code interface at rank a+2,
  decoded product at c=max(a+1,b), actual closed normal identity constructor.
- TarskiUniverses: universe-code law of rank 2 with actual normal identity
  witnesses at EVERY external rank, not a finite set of examples.
- TarskiCasts: both type-transport directions using arrow motives at rank
  c+1, law rank c+2, directly typed dependent Abs/App and universe casts.
- TarskiIdentity: actual reflexivity product-law witness at the common
  reduct and literal Abs/App recovery to f and f u, without eta or payloads.
- ClosedTarskiCasts: closed normal programs over S,T and evidence, program
  type rank c+3, direct application typing and reflexivity computation.
- EtaBoundary: pointwise beta agreement does not entail original beta
  conversion, including dependent indices in an actual valid context.

The new interface does not assume arbitrary decoders preserve products
definitionally. Typed local equality arguments have actual proved identity
inhabitants. Neither same-level predicative symmetry nor extensionality is
added. Existing raw HOAS syntax injectivity and finite STLC PHOAS results
are unchanged. No full dependent quoter or interpreter has been completed.

First remaining construction: close the local declarations over a finite
rank palette; represent dependent families and generate internal coherence
witnesses from independent original derivations. Prove their identity
computation and normality, including all lambda annotations. Generic neutral
casts do not definitionally cancel; pointwise family evidence is not itself
an equality of host functions. The eta regression is a limited warning, not
an impossibility proof for dependent PHOAS.

## Verification, failures and exact evidence

Fresh absolute aggregate build /tmp/pts-rk-self-tarski-audit.OveK1T exits 0
with **418 closed reports**: previous 326 + 63 new module reports + 29 new
aggregate endpoints. Recursive core/aggregate kernel checks and pristine
core inventory comparison pass. Loaded-context inventory contains only
unchanged upstream functional_extensionality_dep; all new theorem reports
are closed, with no unsafe/type-in-type/assumed-positivity entries.

Original kernel, frozen PR #1 ZFC and NormalizationComplexity source checks
pass. All 36 self-interpreter sources plus Dune are hash-stable through the
audit. Full local CI exits 0, **226/226 stages**, including actionlint and a
fresh upstream archive build. This concerns the current dirty worktree,
including independent prior work; it is not a new remote-CI claim. No CI or
proof rule was weakened. Final drivers have no failure or timeout.

Exact commands, before/after source hashes, UTC timing, tool versions,
recursive inventories, scoped checks and the auxiliary shell-wrapper typo
and successful rerun are in [final review](final-review/COMMANDS.md).
Raw local-only artifacts remain ignored under
_build/self-interpreter-tarski-final-review.VnAQed. Principal commands:

```sh
bash _build/self-interpreter-tarski-final-review.VnAQed/AUDIT.sh
bash _build/self-interpreter-tarski-final-review.VnAQed/CI.sh
```

The first runner invokes fresh Dune @theories/self_interpreter/audit and
recursive rocq check with the pinned load paths; the second runs the literal
bash tools/check-local-ci.sh. Versions: Rocq 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1, opam 2.6.1.
All intermediate compiler failures are retained in the module reports:
[equality](equality/COMMANDS.md), [products](products/COMMANDS.md),
[universes](universes/COMMANDS.md), [casts](casts/COMMANDS.md),
[identity](identity/COMMANDS.md), [closed casts](closed-casts/COMMANDS.md),
[eta boundary](eta/COMMANDS.md). No admissions or theorem weakening.

## Research note and PDF

The note adds the object-language Tarski section and identity-realization
theorem, exact ranks and remaining full-dependent obligations. The abstract,
formalization status, research programme and development README agree with
the checked boundary. Independent mathematical/API and prose reviews pass.
The theorem explicitly requires the original typings of f and u; its
universe reflexivity uses proved beta conversion. Rebuild instructions are
retained in the development README rather than on an otherwise empty page.

Two invocations of `bash tools/build-self-interpreter-note.sh` both exit 0:

| Build directory | Result | Editorial outcome |
| --- | --- | --- |
| /tmp/pts-rk-self-note.TIFamY | 23 pages, 285497 bytes | Initial new section; final page held only rebuild instructions. |
| /tmp/pts-rk-self-note.dAmCLX | 22 pages, 284951 bytes | Explicit f/u hypotheses, beta-conversion clarification, no orphan instruction page. |

Final versions: Latexmk 4.88, LuaHBTeX 1.24.0, TeX Live 2026.
No overfull boxes, missing glyphs or unresolved references. Four retained
underfull boxes have badness 1314, 2111, 1629 and 1648. Build/engine/version
logs are in each fresh build directory. Final hashes:

```text
70f12e066e65238f007217057a77afdf5e217f6d3fde7eb44ef1272ace113a26  PTS-rk_self_interpreter.tex
cb492457e59a8d91394f518586cf35c9a06bd33fbb2a16882b3bc8e6c5a7deef  PTS-rk_self_interpreter.pdf
```

PDF inspection used Swift Foundation/PDFKit/AppKit: PDFDocument.pageCount
confirms 22; page.string extracted every page to pdf-text.txt; thumbnails
of pages 16,17,18,22 were rendered at 1050x1485 into pageNN.png in the final
build directory. All four images were visually inspected: equations,
identity theorem, scope boundary and closing status render without clipping.
The earlier orphan page was likewise inspected before the editorial fix.

## Next fresh command

After the next meaningful proof change, use a new absolute directory:

```sh
next_build=$(mktemp -d /tmp/pts-rk-self-next.XXXXXX)
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir="$next_build" --display=short --no-buffer @theories/self_interpreter/audit
```

Do not infer fresh Print Assumptions output from a cached no-op. Preserve
the uncommitted continuation and all unrelated existing work when publishing.
