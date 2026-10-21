# Dependent sort/context/binder checkpoint — 20 October 2026

Working directory: `/Users/akuklev/air/pts-rk`.
Base and final HEAD: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
No commit, push, merge or index mutation was performed. Existing unrelated
work and both preceding uncommitted Tarski milestones were preserved.

## Verified development

Four new modules, with original PTS syntax, typing, RankSorts and beta
conversion unchanged:

- `TarskiSorts.v`: actual universe code/term casts and normal closed sort
  quotations; direct original identity-application typing and literal U_r
  recovery, for every label in the finite budget. 17 own closed reports.
- `TarskiContext.v`: typed variable environments and concrete independent
  dependent extensions; computed identity context and variable-preserving
  TypedSub, original wf and fresh-scope operation typing/recovery. 34 reports.
- `TarskiBinders.v`: smart fresh-variable family application; exact renaming
  and one-way replacement reduction; normal decoded annotations, typed normal
  local Abs/App and actual dependent lambda-family binder. Literal recovery
  and local input/conversion injectivity. 19 reports.
- `TarskiRoundtrip.v`: actual typed normal nonconvertible neutral cast
  roundtrip, including dependent type indices, uniformly over external c;
  positive reflexivity recovery. 10 reports.

The smart binder repairs a local annotation-normality problem. It does not
construct a quotation for every original derivation. The roundtrip theorem
rules out silent beta-cancellation of the existing neutral casts, not internal
equality witnesses or all indexed PHOAS. No source domain assumes the target
quotation or recovery result. Existing raw-HOAS and STLC syntax fidelity is
retained; new injectivity is explicitly local to fixed binder inputs.

## Build and proof evidence

The exact commands, all intermediate failures and final source hashes are
recorded in the module subdirectories:

- [Sorts](sorts/COMMANDS.md), five attempts; final exit 0.
- [Contexts](context/COMMANDS.md), eight attempts; final exit 0.
- [Smart binders](binders/COMMANDS.md), eleven attempts; final exit 0.
- [Roundtrip boundary](roundtrip/COMMANDS.md), three attempts; final exit 0.

[Final aggregate review](final-review/COMMANDS.md) records a fresh absolute
Dune build in `/tmp/pts-rk-self-binders-audit.xrjN04`, recursive original and
aggregate kernel checks, pristine original-core inventory agreement, frozen
source comparisons and source-hash stability. All checks exit 0. The fresh
aggregate prints **646** closed reports: 527 preceding +80 new module +39 new
aggregate reports; Audit now has 206 Check/Print pairs. All 46 proof/Dune files
remained hash-stable. Unsafe/type-in-type/assumed-positivity inventories are
empty; loaded-library extensionality is only the unchanged upstream declaration,
not a new assumption in the printed theorems.

Full `bash tools/check-local-ci.sh` exits 0: actionlint and **226/226** stages,
including a new pristine-upstream build. No stage was removed or weakened.
Raw ignored evidence: `_build/self-interpreter-binders-final-review.r6pl8m`.
Aggregate interval 14:41:35–14:43:10 UTC; CI 14:41:36–14:42:28 UTC.
Neither final runner failed or timed out. Independent mathematical reviews
pass. Pinned Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1; full package inventory retained in raw evidence.

## Next proof boundary

Construct independent full-original source derivation data and a recursive
translation through the finite dependent context. Source terms/types, their
substitutions and conversion proofs must generate the required object-language
coherence. In particular, do not turn pointwise family equality or the proved
identity specialization into beta equality for abstract neutral casts.

The smart constructor commutes exactly with renaming, but only by reduction
with arbitrary substitution. Global normality, strong source recovery and
faithful source syntax must be proved for the recursive translation itself.
The new context/sort/binder lemmas are inputs to that work, not its conclusion.

## Research note and PDF

Updated `PTS-rk_self_interpreter.tex` and the development README, retaining
the repository's LaTeX–Markdown dialect. New sections distinguish source-sort
quotation, independently sorted context extensions, fixed-signature smart local
binders and the precise cast-conversion counterexample. Original typing premises
are stated separately from normality premises. Smart operations have not yet
been generalized/composed with the arbitrary dependent-spine operations.
Independent final prose review passes.

```sh
bash tools/build-self-interpreter-note.sh
swift _build/self-interpreter-binders-final-review.r6pl8m/INSPECT.swift \
  /tmp/pts-rk-self-note.pGxQyu
rg 'Overfull|Underfull|Missing character|undefined references|Output written' \
  /tmp/pts-rk-self-note.pGxQyu/PTS-rk_self_interpreter.log
shasum -a 256 PTS-rk_self_interpreter.tex PTS-rk_self_interpreter.pdf
```

Build and Swift inspection exit 0. Fresh build directory:
`/tmp/pts-rk-self-note.pGxQyu`; full build/inspection status and wrapper logs
are in `_build/self-interpreter-binders-final-review.r6pl8m`. The build uses
Latexmk 4.88, LuaHBTeX 1.24.0 / TeX Live 2026; exact version output retained in
the temporary build's `versions.log`.

Final PDF: **26 pages, 322023 bytes**. No overfull boxes, missing glyphs or
undefined references. Four mild underfull boxes (badness 1314, 2111, 1231,
1629) remain; no typesetting failure. All-page text extracted to `pdf-text.txt`;
rendered pages 19, 20, 21, 22, 23 and 26 were visually inspected for formulas,
new subsections, source-contract boundaries and the closing obligations.
All inspected content renders correctly, with no unsupported pipe tables.

```text
41680036262736d11611bd0511d979426268735a2cdcc599d2b0ed5a2ff7e7aa  PTS-rk_self_interpreter.tex
32b5d1e766205b3843e7efd9ccec3a48f2479de34bcef8a4b0464e8fa9cd90ab  PTS-rk_self_interpreter.pdf
```

Scoped whitespace checks pass; no staged changes. Generated caches, raw logs,
PDF inspection images and tool scripts remain ignored/local-only. The PDF
research artifact is updated in the worktree, not committed or pushed.
