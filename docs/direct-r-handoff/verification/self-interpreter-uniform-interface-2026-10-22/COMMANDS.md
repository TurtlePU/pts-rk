# Fixed fragment closure interface and internal numeric budgets

## Scope and publication

The five new self_consistency documentation files were committed first, as
requested, in `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`:
`Self-consistency: document bounded soundness and formalization routes`.
No push was requested or performed. The subsequent proof/document continuation
is uncommitted. Unrelated BZC, CI, root documentation and handoff changes were
preserved; they are not part of that commit.

New proof modules use original `Syntax.Term nat`, `Typing.typ`, `RankSorts`
and beta reduction. No original kernel, normalization or ZFC reference source
is modified. No CPS translation is formalized.

## Mathematical contracts

- `FixedInterface`: actual original normal closure decoder with hidden domain,
  normal program and normal executor. Rank is `max(a+4,s+3)`; application
  computes the executor applied to the program without precomputing its value.
  Typed introduction/evaluation and their beta roundtrip prove `inhabited_iff`.
- `RankPadding`: exact common sorts without cumulativity, normal embeddings,
  neutral-variable runner adaptation and literal recovery.
- `FragmentClosureInterpreter.every_bounded_original`: k is fixed before the
  independent source fragment witness. The one normal head has exact type-sort
  k+10; its ordinary spine is padded nf(T), normal faithful closure code, and
  fixed d_k. The whole spine has original type T and reduces to literal t.
  Syntax and conversion injection are retained across budgets. Only the source
  type is normalized; the runner still depends on plan and represented type.
  No generic forcing operation for arbitrary R:U_(k+1) is claimed. Underlying
  capped literal type-program recovery remains a separate theorem.
- `BudgetInternalization`: fixed reifier/evaluator terms with uniformly
  literal-bounded ordinary inputs cannot strongly recover all original sorts.
  Arbitrary numbers of encoded certificate/budget fields are allowed. This
  does not rule out fixed fragments or Bottom-specific internal soundness.
- `FiniteLiteralBank.one_head_for_bounded_sorts`: normal literal-zero selectors,
  one rank-2 normal original decoder and exact recovery of every finite-bank
  sort. This external finite selector interface is not a certificate checker.
- `NumericLiteralBank.numeric_sort_recovery`: an actual original term consumes
  a monomorphic Church numeral i and reduces to U_min(i,k), hence U_i when
  independently i<=k. The numeral state carrier depends externally on k;
  saturation is not bounds checking or proof acceptance. Normal numeral inputs
  have literal ceiling zero. The normal head's type-sort is 4.

The internal acceptance predicate, arithmetic domain, trace witnesses and
resource selection are still to be independently specified and realized.
Code(Bottom) reification already contains soundness; it cannot be assumed as
an encoding premise. A closure execution interface is not a shared PHOAS
constructor algebra.

## Reproducible proof checks

Pinned environment:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

OCaml 4.14.2, Dune 3.23.1, Rocq 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2. Full installed versions are retained in the raw directory
`_build/self-interpreter-uniform-interface-2026-10-22`.

`AUDIT.sh` records exact escaped commands, UTC start/end times, stdout/stderr
and exit status for each stage. The fresh absolute Dune directory is
`/tmp/pts-rk-self-uniform-audit.ZjpFUy`.

```sh
bash docs/direct-r-handoff/verification/self-interpreter-uniform-interface-2026-10-22/AUDIT.sh pristine
bash docs/direct-r-handoff/verification/self-interpreter-uniform-interface-2026-10-22/AUDIT.sh prebuild
bash docs/direct-r-handoff/verification/self-interpreter-uniform-interface-2026-10-22/AUDIT.sh interface
bash docs/direct-r-handoff/verification/self-interpreter-uniform-interface-2026-10-22/AUDIT.sh
bash docs/direct-r-handoff/verification/self-interpreter-uniform-interface-2026-10-22/AUDIT.sh ci
bash docs/direct-r-handoff/verification/self-interpreter-uniform-interface-2026-10-22/SOURCE-CHECKS.sh
```

The first two stages have passed: capped dependency prebuild (1032 closed
reports including the unchanged upstream report), and the five new stable
interface/obstruction modules plus additional dependencies (74 closed reports).
The prebuild alone is not the final audit. Complete local CI, including
actionlint and the pristine upstream archive build, **passes all 226 stages**,
exit 0, from 00:18:35 to 00:24:56 UTC on 22 October. The current shared worktree
driver was used without modification by this continuation; unrelated existing
CI/BZC changes were not committed. Its self-interpreter stage reports all
1112 public endpoints closed. Raw stage table and result are in `full-ci/`.
Fresh aggregate compilation passes (00:18:36--00:27:35 UTC): the three fresh
build stages together report **2706 own closed reports plus one unchanged
upstream report** (1032 + 74 + 1601 total). There are 1112 public Check/Print
pairs and 129 source/Dune manifest entries.

Both recursive kernel checks pass: core 00:27:35--00:27:42, interpreter
00:27:42--00:36:42 UTC, exit 0. The loaded inventory has only unchanged
upstream functional extensionality; no type-in-type, unsafe (co)fixpoint or
assumed-positivity entries. The initial core comparison matches the retained
pristine report from 20 October. `pristine` mode additionally builds/checks
the actual upstream archive afresh and makes future reproduction independent
of that historical log. Original frozen-source comparison, all 129 source
stability checks and tracked/untracked whitespace/safety checks pass.

The additional pristine archive build/check also passes:
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`, temporary snapshot
`/tmp/pts-rk-uniform-pristine.68AZJl`, build 00:37:56--00:37:59 UTC and kernel
check 00:37:59--00:38:05, all exit 0. `fresh-pristine-inventory` matches the
current core report byte-for-byte. Concurrent unrelated Combinatory work
appeared after the full-CI run; that run reports its 226 driver stages, not
verification of later unrelated edits. Those files/handoff entries are preserved.

After successful verification, `CLEAN-CACHES.sh` removed only this run's
generated fresh Dune directory and pristine snapshot, using explicit validated
paths. The working build, sources, toolchain, PDF builds and all raw audit logs
are retained. `cache-cleanup.log` records their sizes and available space.
The removed directories are recoverable by rerunning the documented builds;
their retained paths identify historical evidence, not currently live caches.

## Targeted development attempts

Targeted commands used `opam exec -- dune build theories/self_interpreter/NAME.vo`.
These early agent calls returned compiler output only to the tool transcript;
no dedicated raw log files were retained. The limitation is recorded explicitly;
the fresh parent build provides the durable success evidence.

- RankPadding: Boolean normality induction and unsupported `syntax_simp in H`
  grammar failed (exit 1); final compilation exited 0, 12 closed reports.
- FixedInterface: initially missing registered integration source, selector
  binder-renaming bookkeeping, and a remaining reflexive RTC goal failed.
  First successful build had 13 closed reports; final introduction/roundtrip
  extension exited 0, 16 closed reports.
- FragmentClosureInterpreter: explicit realization inference and identity
  unfolding were needed; after an intermediate successful section build,
  `repeat split` closed a normality goal and shifted bullets. Explicit splits
  fixed it. Final compilation exited 0, 23 closed reports.
- BudgetInternalization: missing registered integration source and minor
  decidability/reflexivity proof details were corrected; final compilation
  exited 0, 9 closed reports.
- FiniteLiteralBank: context lookup, Boolean normalization, min/max arithmetic
  and run-expression rewriting were corrected; final compilation including
  `one_head_for_bounded_sorts` exited 0, 9 closed reports.
- NumericLiteralBank: initial scaffold attempts were likewise transcript-only.
  Later raw `numeric-attempt-01`/`02` record typing-normalization/context
  failures (exit 1); `03` compiles the numeric operation and beta theorem
  (exit 0). `04` records an incomplete focused literal-induction proof
  (exit 1). `05` is final, exit 0, ten closed reports. These five log/exit
  pairs are retained in the raw evidence directory. No polymorphic numeral
  wrapper, certificate checker or arbitrary-code soundness is claimed.

No theorem statement or CI check was weakened to bypass these errors.

## Documents

`bash tools/build-self-interpreter-note.sh` initially passed in
`/tmp/pts-rk-self-note.mCZB4C`: 15 pages, no layout/reference/glyph warnings.
`inspect.swift` checks extracted section text, original-paper link and renders
the first, comparison and final pages. Pages 1,13,14,15 were visually inspected.
The final source/PDF state follows below.

The numeric-adapter version built successfully in
`/tmp/pts-rk-self-note.hTnzcF`, but visual inspection showed a nearly empty
sixteenth page. The final paragraph was shortened without losing its scope
conditions. Final build: `/tmp/pts-rk-self-note.PKoaj6`, exit 0, **15 pages**,
no layout/reference/glyph warnings. PDFKit validation passes; the first,
comparison and final pages were rendered and visually checked. Final hashes:

```
e3ecd10d3d2476b0f12fc15e98d74bd09b384686d3b4329b0829ad4fe3a235d7  PTS-rk_self_interpreter.tex
df8458a2708d6b8e04b096e50c0f2eb002e2fd9d65a8cf1a4c3d91d41944ea73  PTS-rk_self_interpreter.pdf
```

The consistency summary was updated to distinguish the now-proved closure
interface from still-open internal reification. Its final document build is
`/tmp/pts-rk-consistency-note.7u3pxt`: ten pages, no layout/reference/glyph
warnings; PDFKit section/link/text/render checks pass. Its own EVIDENCE.md
records the two preceding layout attempts and final hashes. It remains a
documentation-only consistency development, not a new internal proof.

## First remaining goal

Define independent certificate arithmetic and the exact accepted-trace domain;
construct internal reification at Bottom with explicit resource admission.
Start with the original sort-leaf rule, then scoped variables and dependent
binders/conversion. Correctness on standard numeral inputs is not a universal
internal acceptance-soundness proof. No CPS work is required for this path.
