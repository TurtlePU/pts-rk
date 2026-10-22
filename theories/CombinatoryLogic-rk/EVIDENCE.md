# Combinatory exploration — evidence, 22 October 2026

## Current checkpoint: contextual certificate soundness and finite packages

Thirteen new Agda modules prove independent decidable certificates for all
six original rules, context/valuation soundness, automatic semantic rank
coverage, alphabet coverage/coherence, arbitrary typed-substitution
normalization and joint finite context/type/value/substitution carriers.
`FragmentModelSoundness.model-soundness` interprets every accepted raw input
at computed bounds, preserving exact substituted typing and forward beta
reduction. Its acceptance predicate contains no native typing, well-formedness
or normalization premise. Every original derivation can be certified.
Decoded normal outputs respect conversion and valuation composition;
proof witnesses and sufficient budgets do not affect them.

`NativeCanonicity.Void-empty` excludes every original closed inhabitant of
`Π X : U₀. X`, hence accepted closed Void certificates and finite Void fibres.
This is an external Agda metatheorem, not an internal PTS consistency proof.
Regressions start with raw certificates for closed identity, dependent X↦U₀,
and open-target X↦Y; package recovery and two malformed-input rejections pass.

Final fresh --safe closure /tmp/pts-rk-combinatory-agda.xZU85m,
11:04:13–11:04:58 UTC, exit 0: all 52 project modules, no warnings,
ignored interfaces, isolated configuration/data and stable copied sources.
Agda 2.8.0-3d04bac; clean Cubical v0.9 b150186d. Earlier 51-module fresh
closure also passed. All 38 prior Agda files except import-only Everything,
and all 24 Rocq files/Dune, match their previous audited manifests.
No new Rocq/MM0/full-CI run, stage, commit or push.

Final note /tmp/pts-rk-combinatory-note.5WV08w,
11:06:27–11:06:41 UTC, build/validation and inspector exit 0:
25 pages, 3-page MM0 appendix, 23 Rocq / 27 Agda badges, 89 links.
All pages rendered; changed pages visually checked. Initial layout and
inspector failures, fixes, exact commands, source hashes and raw logs:
[verification record](../../docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22/COMMANDS.md).

**Remaining:** these are graded syntactic interpretations, not fixed finite
first-order models. Construct total operations on fixed finite domains for
an explicitly specified fragment, coherent dependent semantic fibres and
all axioms under every semantic valuation. Increasing syntax grades does not
supply closure; even single-label rank-one normal types have unbounded size.
Internal checker/compiler correspondence, reflection and the separate native
Hilbert/QIIRT adequacy and binary Church compiler obligations remain open.
Package cardinalities do not bound arbitrary proof trees or runtime memory.

## Previous checkpoint: total typed Agda normalization and fragment soundness

`applyTypedWithin : (inputs : TypedInputs a) → TypedResult inputs` is total.
It returns an IIR normal representative, truncated bounded beta trace and
original typing at exactly Y[y]. No normalization or output-typing premise
is added. Fourteen new modules establish the original substitution,
confluence, inversion, preservation, rank safety/descent/preservation,
normalization/coherence metatheory, graded fragment operations and tests.
The unchanged NativeTyping rules are not replaced by a checker.

NativeNormalization proves full normalization from original typing and a
semantic redex-rank bound, conversion iff equality of normal outputs,
idempotence, sufficient-budget independence and reachable-state type/rank
invariants. FragmentEmbeddings proves finite typed normal fibres and coherent
injective size inclusions. FragmentApplication proves exact dependent
application in an enlarged grade, conversion compatibility, input-embedding
coherence and reachable-state soundness. FragmentMachineSoundness proves
the existing finite-state execution decodes to these genuinely typed normal
forms; clipping is excluded by numerical budgets, not a target assumption.

Final fresh --safe closure: /tmp/pts-rk-combinatory-agda.vPyHLe,
10:08:50–10:09:32 UTC, exit 0, all 39 project modules, no warnings,
ignored interfaces and isolated configuration/data, stable copied sources.
Agda 2.8.0-3d04bac; clean Cubical v0.9 b150186d. Earlier fresh 38-module
closure also passed before adding the finite-machine bridge. Regressions
cover dependent application, converted inputs and annotation reduction.

Final PDF .FofOTf, 10:11:02–10:11:16 UTC, build/validation and inspector
exit 0: 23 pages, 3-page MM0 appendix, 23 Rocq / 20 Agda badges, 77 links.
All pages rendered; changed pages visually checked. The note states the
total API and proved graded laws, retaining the future-work programme.
All 24 Rocq modules/Dune match the prior audited manifest byte-for-byte;
no new Rocq/MM0/full-CI run. No stage/commit/push or unrelated changes.
Commands, raw failures, final logs, hashes and review:
[verification record](../../docs/direct-r-handoff/verification/combinatory-total-agda-2026-10-22/COMMANDS.md).

Next model obligations: bounded type/universe carriers and alphabet-extension
coherence; interpretation under arbitrary valuations/substitution and
all-rule/axiom soundness for an independent certificate system. These are
finite fibres and sound graded operations, not a complete model hierarchy or
an internal consistency theorem. QIIRT/Hilbert adequacy and binary Church
compiler correspondence remain separate. Whole-runtime bounds are not proved.
Older checkpoint statements below record their then-current status.

## Note update: future work

The note now specifies three research directions: a quadratically checkable
objective PTS-rk variant, a finitely based logic-free partial-function
arithmetic with extension judgments and locally finite models, and an
interpretation of the former into the latter. The cited objective-type-theory
result is not claimed for PTS-rk; all three directions remain proposals.
Final PDF build/validation and inspection pass: 22 pages, 3-page MM0 appendix,
23 Rocq / 11 Agda badges, 66 links. Formal sources and their previous audit
status are unchanged. See the
[note verification record](../../docs/direct-r-handoff/verification/combinatory-future-work-2026-10-22/COMMANDS.md).

## Previous checkpoint: finite Church compilation at explicit ranks

[ChurchFinite.v](ChurchFinite.v) proves original typing, formation ranks and
forward beta computation of all finite selectors, unary table maps and their
finite iterations. Nonempty selector types have rank r+1, map types r+2;
continuations are reindexed at the same answer type. Carrier types and
selectors are normal with exactly 2m+3 annotated nodes. All 17 new assumption
reports are closed. This uses original Term/Typing.typ/RankSorts, no new rules.

[FiniteMachine.agda](agda/FiniteMachine.agda) gives total finite pass and
application tables with a clipping fallback, proving exact decoded agreement
on inputs satisfying the numerical tower budget. The fallback is never used
on those bounded runs. [ChurchFinite.agda](agda/ChurchFinite.agda) emits actual
annotated PTS programs for the two tables, d-fold reduction and apply/reduce.
Agda proves all-index selector typing/normality/size and executable small
unary/binary regressions. No final-normal-answer table is precomputed.

The all-index binary map theorem and the cross-language Agda–Rocq generator
correspondence are NOT proved. This is code-to-code computation, not a general
Agda compiler or semantic Y[y] inhabitant. The prior total typed Agda result
still needs subject reduction and rank descent. Generated program sizes are
not bounded by the original source N; finite tables do not bound all runtime
allocations. Canonical selectors are not identified with all inhabitants.

The note adds explicit ranks/encodings, literal highlighted generated-program
source, linked proof badges and a conditional internal-consistency programme.
The latter follows the existing predicate-only, resource-cut self_consistency
plan; fragment closure/embeddings, certificate soundness, internal finite-case
principles and an actual interpretation J remain proof obligations. No model
hierarchy or internal consistency theorem is claimed.

### Verification

[Commands and remaining goals](../../docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/COMMANDS.md)
record exact checks, versions, raw logs and failures.

- Fresh native audit exits 0, 19/19, 08:59:33–09:00:25 UTC:
  _build/combinatory-church-finite-audit.0ceAEs. 24 modules, 241 own / 242 aggregate
  closed reports. Recursive assumptions match a separately rebuilt pristine
  upstream byte-for-byte, only unchanged functional_extensionality_dep.
  Original kernel unchanged; safety/source stability pass. No full-CI claim.
- Fresh safe Agda closure exits 0, 08:59:00–08:59:34 UTC:
  /tmp/pts-rk-combinatory-agda.4jl4SO. All 25 project modules, no warnings,
  ignored interfaces/isolated configuration/stable copied sources.
- Final PDF exits 0, 09:03:29–09:03:43 UTC:
  /tmp/pts-rk-combinatory-note.2lG4Vk. Inspector exits 0: 21 pages, 3-page MM0
  appendix, 23 Rocq / 11 Agda badges, 65 links. All pages rendered and new pages
  visually inspected; see PDF-REVIEW.md. No glyph/layout/reference errors.
  One unchanged underfull MM0 footnote diagnostic remains.
- Scoped whitespace and source manifests pass. No staging/commit/push;
  HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef, unrelated work preserved.

## Previous checkpoint: finite IIR normal syntax and bounded Agda reduction

The 23-module Cubical Agda closure checks with `--safe`, without warnings.
`NormalForms.agda` defines Nf, NonLamNf and erase inductive-inductive-
recursively; erasure is injective and covers every normal annotated raw term.
`TypedNormalFibres.agda` gives exact-length, type-rank-bounded fibres of the
literal original typing relation, with propositionally truncated typing/rank
certificates. Its `typed-normal-bound` is an actual injection into
`Fin ((4*N+4) ↑↑ (d+3))`, not merely an arithmetic estimate.

The alphabet `labels : Fin a → Nat` is fixed and a≤N is essential. Without
this restriction the one-node normal terms U_i:U_0 refute finiteness. N counts
all original annotated syntax nodes, not BCKW atoms. A normal family's d
bounds the type's rank; TypedInputs.d is the function product's exact sort
rank. For application N=1+|f|+|y|.

BoundedReduction, RawSizeBounds and BoundedTrace implement the original
annotated substitution/greedy strategy and prove forward reduction, output
size and EVERY single-beta intermediate's size unconditionally. FiniteTrace
computes the same path as a walk with states Fin(capacity); state-bound proves
the requested tetration cardinality. Whole walks are not asserted finite.

FiniteApplication.applyWithinFinite and TypedApplication.applyTypedWithin
are executable bounded attempts. Successful outputs are actual bounded IIR
normal forms with truncated bounded-reduction evidence. The size bound is
proved, not tested. The function still returns Maybe(Result inputs), NOT
TypedResult. The precise Y[y] output fibre and its cardinal bound are defined
and proved, but its inhabitance/result typing is not. Original Agda subject
reduction, typed rank descent and the normal-application rank lemma remain
open. No input hypothesis assumes those targets. Trace construction still
uses Raw internally: carrier-only execution and whole-runtime bounds are
separate obligations. The requested total typed Agda normalizer is therefore
NOT completed by this checkpoint.

The note now places “Elementary normalization and finite syntax carriers”
immediately after QIIRT and includes literal Pygments-highlighted source
excerpts and nine linked Agda proof badges. The PDF is rebuilt. No original
Rocq source, Dune stanza, MM0 theory, or BCKW QIIRT was changed in this step.

### Verification

[Commands and remaining obligations](../../docs/direct-r-handoff/verification/combinatory-finite-agda-2026-10-22/COMMANDS.md)
record the final evidence and all retained incremental attempts.

- Fresh safe closure: /tmp/pts-rk-combinatory-agda.7UFFIh,
  08:12:27–08:13:03 UTC, exit 0, all 23 project modules; no warnings.
  Agda 2.8.0-3d04bac, pristine Cubical v0.9 b150186d.
  Copied-source and final-source SHA256 stability checks pass.
- Final note: /tmp/pts-rk-combinatory-note.5X2knp,
  08:17:32–08:17:45 UTC, build/validation exits 0. LuaHBTeX 1.24.0,
  TeX Live 2026, latexmk 4.88, latexminted 0.7.0, Pygments 2.19.2.
  No missing glyphs, overfull boxes, undefined references or highlighting
  fallback. Latin Modern Math supplies Agda's missing double-bar glyph.
- New inspector: exit 0, 18 pages, 3-page complete MM0 appendix,
  22 Rocq badges, 17 Agda links (including 9 proof badges), 58 links total.
  All source targets checked and pages rendered in
  _build/combinatory-finite-pdf.6WaFbZ; changed pages visually inspected.
- The 23 existing Rocq sources and Dune file match the previous fresh audit
  manifest byte-for-byte. Its 224 own/225 aggregate closed reports and pristine
  assumption comparison remain applicable; no new Rocq/full-CI run is claimed.
  Scoped whitespace, shell syntax and source safety scans pass.

The first PDF attempt /tmp/pts-rk-combinatory-note.bB5vJG compiled but failed
validation (exit 1) on missing ≤ in inline code and ∥ in the monospaced font.
Math-mode prose and a local font fallback fixed the actual glyph defects;
no validator was removed. The intermediate .Nltp4k build passed before the
final nonbreaking layout adjustment. No timeout, staging, commit or push.
HEAD remains cb76553b03d536743e36c4e2c7e5a1c7c1669bef; unrelated dirty work is
preserved.

## Previous checkpoint: BCKW arithmetic and independent BCKW QIIRT

The note's section 2 now gives conventional rank-typed B,C,K,W,I, Church
0/1/2 and successor/addition/multiplication. The requested abstract sentence
and affine-generator section are removed. Duplication is W throughout the
live exposition and code; the supporting AffineDuplication constructor is
renamed accordingly. No original PTS rules or annotations were changed.

BCKW.v proves original typing of intrinsic simple-type-indexed codes over
U_i, exact numeral counts n W and 7n+2 atoms, forward reduction to unapplied
annotated Church normal forms, normality and all three arithmetic laws.
Operation atom counts are 8/9/1; the Church type has rank 2 and the operation
types rank 3. This counts I as one atom and fixes type-index shapes independent
of n. Arbitrary type-index payloads are not free in the complexity statement.

KnuthBounds.v proves that the executable seeded binary tower is bounded
by max(2,N) ↑↑ (d+1). The note consistently uses this tetration notation,
including height 2d+2 for abstract cost and d+3 for the finite carrier.
The original, tighter bounds remain unchanged. The carrier claim explicitly
requires a closed input and its finite universe-label alphabet.

agda/BCKW.agda independently defines the six B/C/K/W/I/P numeric families,
literal telescopes, guarded saturation laws, structural diagonal and its
type-reindexing equation, without importing the dependent substitution atom.
It is 435 lines and checks safely. The note's highlighted excerpts now come
from this source. The established dependent-core Agda files remain independently
checked supporting constructions, not an implementation dependency of BCKW.
Structural contraction and shared-context application are not a closed
annotation-preserving dependent BCKW compiler.

The full dependent Hilbert/MM0 catalogue is retained. Archived tests check two
classical BCKW substitution expressions at simple types, but reject their
straightforward dependent typings with scope errors, even with dependent-result
B/C/W. These are failed specific constructions, NOT a nondefinability theorem.
Consequently the user's conditional wholesale replacement is not claimed.
General BCKW dependent completeness, native Hilbert completeness, logical
QIIRT guard admissibility/adequacy and MM0/native adequacy remain open.

### Verification

[Focused evidence](../../docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/COMMANDS.md)
records the exact 23-module/pristine audit:

```sh
bash docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/AUDIT.sh
```

Exit 0, all 19 stages, 06:36:36–06:37:27 UTC. Logs:
_build/combinatory-bckw-audit.Hukon3; fresh build
/tmp/pts-rk-combinatory-bckw.bnSrlP; independent pristine
/tmp/pts-rk-combinatory-bckw-pristine.p0tvSU. There are 224 own closed
reports and 225 aggregate reports. Recursive kernel inventories match
pristine byte-for-byte: unchanged upstream functional_extensionality_dep only,
no unsafe features or new assumptions. Source stability, original-kernel
comparison, safety and whitespace pass. This is not a new full-CI run.
Toolchain: Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Stdlib 9.1.0,
Equations 1.3.2+9.2.

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh
MM0_RS=/tmp/pts-rk-mm0.lhphPY/upstream/mm0-rs/target/release/mm0-rs \
MM0_C=/tmp/pts-rk-mm0.lhphPY/mm0-c \
bash theories/CombinatoryLogic-rk/check-mm0.sh
bash theories/CombinatoryLogic-rk/build-note.sh
swift docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-bckw-pdf.RO8PaR
```

All final commands exit 0. Fresh ten-module safe Agda closure:
06:31:13–06:31:36 UTC, /tmp/pts-rk-combinatory-agda.Td8Ru5, Agda 2.8.0
and Cubical v0.9 b150186d. The separate archived dependent-basis regression
exits 0 with its required individual exits 0/42/42/42; it does not suppress
unexpected failures. MM0 passes all four stages, 06:39:23–06:39:24 UTC,
logs /tmp/pts-rk-combinatory-mm0.FNFzjw; its theory hash is unchanged.

Final note build: /tmp/pts-rk-combinatory-note.2GZNlI,
06:40:24–06:40:36 UTC. No layout/glyph/reference/highlighting warnings;
Pygments output is checked. PDF inspector: 15 pages, 3 appendix pages,
22 proof badges, 43 links, source targets checked and all pages rendered.
Arithmetic, bounds, QIIRT excerpts and appendix were visually inspected.
First note build .yvUk4c exited 1 at layout validation: inserted display
delimiters had become single dollars. Restoring double-dollar delimiters
fixed this; the validator retained the previous PDF during failure.
The first inspector exited 133 because its expected text omitted spaces in
“7n + 2”; the corrected exact PDF text check passes. No validation was removed.

BCKW incremental command/failure ledger and final compile/kernel logs are
archived in verification/combinatory-bckw-2026-10-22/native; final compilation
has 23 closed reports. KnuthBounds direct attempts:
 /tmp/pts-rk-knuth.OOiOgw/attempt-01.log exited 1 (base case needed pow_1_r);
attempt-02.log exited 0 with two closed reports. The fresh joint audit
supersedes these reused-dependency checks. The independent BCKW Agda attempt
/tmp/pts-rk-bckw-agda.dgwU0T/attempt-01.log failed on a local name clash;
attempt-02 and fresh /tmp/pts-rk-bckw-agda-final.exaPYE/check.log passed.
No timeout, unsafe workaround, staging, commit or push occurred.
HEAD remains cb76553b03d536743e36c4e2c7e5a1c7c1669bef.
Final scoped whitespace and shell syntax checks exit 0; all 23 Rocq sources
plus Dune, all ten Agda sources, and the MM0 specification/examples still
match their successful audit hashes.

Final hashes:

- note: 78d79e0135c6e8b38abe8276c2a3084ebd87dd599ae8d6c99bc50998be035de5
- PDF: 45394ae3e973ce8d5df745dc95ce42e8a4c9f19844b1b83d2a10e8e33893b4f1
- BCKW.v: 69968bff1bae46c37e3d9cac51987ff6e8b2ae082e5c6b6dc4dd2f960297dbc9
- KnuthBounds.v: a9f652344be762e12c795c206485bd591f54fe7d2293d6da7a21caa78110ad29
- BCKW.agda: c4d8e32d57e309c4aee0ef79a3eccf964af51c7bcd4d24c9a6aeef54805c731f

Earlier checkpoints below preserve provenance; their notation and current-state
statements are superseded by this checkpoint.

## Current checkpoint: affine numerals, peak bounds and finite carriers

The requested substitution-index subsection is removed from the note. The
underlying safe two-index Agda signature and TargetView are unchanged except
for removing two extra EOF blank lines from SCanonical/SCoherence.

Four new original-calculus modules are registered in the existing namespace:

- AffineDuplication: all-index B/J0/J1 typing, n duplications and 2n+1 atoms,
  forward unapplied reduction to Church normal form, and normality (15 reports).
- QuantitativeNormalization: single-beta intermediate bounds for a deterministic
  sequentialization of greedy passes, preservation of the global redex-rank
  bound, normalized dependent application and an outer-rank obstruction
  (8 reports).
- FiniteNormalForms: preservation of the input universe-label alphabet, finite
  complete raw/normal enumerations with elementary cardinal bounds, application
  membership, and failure of rank/length-only finiteness (14 reports).
- GroundHorn: generic Horn derivability iff consequence, singleton all-true
  model and finite-fragment satisfiability (3 reports).

For N syntax nodes and global redex-head bound d, peak size is tower d N,
abstract cost is at most tower (2d+1) (N+5d+2), and the raw finite carrier over
the input labels has capacity at most tower (d+2) (4N+4). Normal application
uses the function's type rank as d. These are bounds on original annotated
subject syntax, not on arbitrary typing witnesses or externally supplied
convertible types, machine memory, or a compiled normal BJ output. The note
defines typed normal families as predicate fibres of finite syntax carriers;
it does not count arbitrary derivation witnesses as separate inhabitants.

The note's explicit untyped universal affine J packaging gives n B and
49n+7 total atoms for Church n, without eta. Its beta calculations were
independently checked by a capture-avoiding de Bruijn normalizer and manually;
they are NOT Rocq universal-J compiler theorems. The checked native fragment
uses two fixed affine tags. A wholesale dependent BJ replacement is not made:
dependent S's split arguments have incompatible fibres, and annotations
already make polymorphic zero non-affine. The original 65-shape Hilbert,
MM0 and QIIRT presentations remain the supported complete/exploratory systems
with their previous stated proof boundaries.

The effective Horn grounding preserves and reflects ground-query derivability
in an infinite recursive vocabulary. Its finite fragments have singleton
models independently of the normalization results. The generic structural
theorem is checked; effectiveness and the Hilbert instantiation are mathematical
arguments, using finite reduction certificates rather than an untyped conversion
oracle. This is not a finite-signature interpretation of all quantified formulas,
a faithful finite syntax model, or an MM0/native adequacy theorem.

### Fresh joint proof verification

```sh
bash docs/direct-r-handoff/verification/combinatory-bj-bounds-2026-10-22/AUDIT.sh
```

Exit **0**, all **19 stages**, **05:25:45–05:26:34 UTC**. Logs:
`_build/combinatory-bj-bounds-audit.4WaD8n`, including exact escaped commands,
status.tsv, versions, source hashes, build output and recursive kernel output.
Fresh absolute Dune build: `/tmp/pts-rk-combinatory-bj-bounds.TgqGUp`.
Separately rebuilt pristine archive: `/tmp/pts-rk-combinatory-bj-bounds-pristine.de3PBe`,
from `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

All **21 modules**, **199 own closed reports**, **200 aggregate** including
the unchanged upstream report. Recursive kernel inventories match the newly
built pristine inventory byte-for-byte: only unchanged upstream dependent
functional extensionality; no unsafe entries or new assumptions. Original
kernel comparison, all source/Dune stability, safety and whitespace pass.
The previous seventeen Rocq sources also hash-match their earlier audit.
Toolchain: Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Stdlib 9.1.0,
Equations 1.3.2+9.2. This is a focused audit, not a new full-CI run.

First joint audit `_build/combinatory-bj-bounds-audit.E63DNW`,
05:23:33–05:24:22 UTC, passed all proof/kernel checks but exited 2 at the final
whitespace stage on two pre-existing extra Agda EOF blank lines. Removing
only those blanks and rerunning the unchanged full script gave the final pass.
No test or CI rule was weakened, and no timeout occurred.

Quantitative development logs and exact commands are retained in
`/tmp/pts-rk-quantitative-log.5gL4w9/COMMANDS.md`: attempts 1–4, 6 and 8–9
had ordinary tactic/namespace errors; final attempt 10, Dune and kernel checks
exit 0. A temporary source-tree AffineDuplication.glob caused one earlier
Dune failure; the owner moved its generated .vo/.glob recoverably to
`/tmp/pts-rk-affine-duplication.VNkDAE`. Its confirmed generated .aux was
likewise moved to `_build/combinatory-bj-artifact-recovery.BIB1Pf`.
Finite enumeration/Horn development logs are retained in
`/tmp/pts-rk-finite-normal.fn6A0S`; `final.log` and `horn-02.log` succeed.
These incremental checks are superseded by the fresh joint audit.
The finite-development compiler exits were not separately retained for
attempts 01–08 (the shell wrapper ended in sed): 01–07 contain compiler
errors, and 08 completed with seven closed reports. Propagated exits for
09–17 are respectively 1,1,1,0,1,1,0,0,0; final.log exits 0 with fourteen
closed reports. Both horn-01 and horn-02 exit 0; the latter moves the three
assumption reports outside the section so they print closed rather than
section parameters. Dependency quantitative.log exits 1 for a missing Core
namespace; quantitative-02/final exit 0 with then-current seven/final eight
reports. There were no timeouts or interruptions.

Affine development raw output was retained only in tool output, not standalone
log files. Eight attempts had exits 127,1,0,1,1,1,0,0; successful checkpoints
printed 13,14,15 closed reports. The shell failure was unquoted PATH; compiler
failures concerned the typ_app argument name and reduction/substitution
matching, fixed with ordinary proofs. The quoted command was the pinned
environment prefix followed by:

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-combinatory-completeness.0GagN7/default/theories PTSrk \
  -Q theories/CombinatoryLogic-rk PTSrk.Combinatory \
  theories/CombinatoryLogic-rk/AffineDuplication.v
```

Attempts 7–8 added `-o /tmp/pts-rk-affine-duplication.VNkDAE/AffineDuplication.vo`;
attempt 8 additionally mapped the prior build's NormalizationComplexity to
`PTSrk.NormalizationComplexity`. These used prior dependency binaries and
are not fresh-upstream checks. Their module-name masking warning is superseded
by the final Dune audit. The recovered earlier .vo was reused by later compiles,
so it is not a separately retained historical binary.

Initial root toolchain probes failed with exit 127 (bare opam, then an
unquoted PATH containing spaces); the documented quoted pinned environment
resolved both. The semantic-search command was unavailable (127), so source
exploration used rg and file reads. These were not proof failures.

### Agda, MM0 and final PDF

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh
MM0_RS=/tmp/pts-rk-mm0.lhphPY/upstream/mm0-rs/target/release/mm0-rs \
MM0_C=/tmp/pts-rk-mm0.lhphPY/mm0-c \
bash theories/CombinatoryLogic-rk/check-mm0.sh
bash theories/CombinatoryLogic-rk/build-note.sh
swift docs/direct-r-handoff/verification/combinatory-bj-bounds-2026-10-22/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-bj-bounds-pdf-final.Ge5Gtk
```

All exit **0**. Fresh safe Agda import-closure check, all nine sources,
05:28:49–05:29:10 UTC: `/tmp/pts-rk-combinatory-agda.LMgEkR`.
Agda 2.8.0-3d04bac, pinned Cubical v0.9 b150186d, fresh copied sources,
isolated data/configuration and ignored interfaces; source stability passes.
Unchanged MM0 specification and ten regressions pass all 4 stages,
05:28:50 UTC: `/tmp/pts-rk-combinatory-mm0.asWdz6`.

Final PDF build `/tmp/pts-rk-combinatory-note.DRrwv0`,
05:31:05–05:31:18 UTC: LuaHBTeX 1.24.0/TeX Live 2026, latexmk 4.88,
actual minted/Pygments Agda. No layout/glyph/reference/highlighting warning.
Inspector verifies **15 pages, 3 appendix pages, 23 proof badges, 46 links**,
section order, removed heading, new content and all source-link targets;
every page rendered, changed pages 3 and 7–9 plus references visually inspected.
Earlier successful PDF drafts `.P5ofEp` and `.k44KJN` are retained; the final
version removes an orphan reference page without changing mathematical content.
Shell syntax, scoped git diff --check and final proof hash rechecks pass.

Final note SHA-256:
`e595cc74ad3cc5985ffed8ab7ae903296a1c229c027aac15408b5b9be2c56c3d`.
Final PDF SHA-256:
`4010705d1c27cd6c8f805a7925acee8e564057f98107a4a9e7d78471cfe1ac53`.
The joint audit's source-after.log records all proof/Dune hashes.

HEAD remains `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`; no staging, commit or
push. Existing unrelated work and intent-to-add entries are preserved.
First remaining goal for a full BJ result: an annotation-preserving dependent
affine/contraction compilation with original typing and controlled output size.
The unconditional native PTS-to-Hilbert theorem, general Agda logical-guard
admissibility/adequacy and MM0/native bridge remain independently open.
Next exact proof verification command is the fresh joint audit above.

## Current checkpoint: linear note and safe Cubical implementation

The note now presents the finite-basis obstruction immediately after the
calculus. The literal catalogue precedes MM0 inside the complete Hilbert
section. The exposition is self-contained and omits development history.
Its Agda excerpts are extracted from actual checked files, not pseudocode.
Con/Sub precede Ty/Tm; RankedTy replaces AnyTy, with comments explaining the
four sorts. TargetView proves both round trips for a source-only substitution
view with computed ctxOf. Fixed extended-target projections require equality
and transport, so the shorter two-index core API is retained. No separate
source-indexed QIIRT is claimed.

Nine Agda modules implement the independent contextual I/K/S/P signature,
structural coherence, literal S telescope and canonical annotation guards,
guard irrelevance, relative exact quotient, target-index comparison and
regressions. The seven S fields are exclusively path proofs at a fixed
telescope. Their canonical inhabitants and irrelevance are proved, so the
public S family has only three numerical indices. No arbitrary type, body or
source-typing oracle enters the independent signature. Fixed-head logical
beta laws and application naturality still carry their actual type-coherence
premises. **General logical-guard admissibility, native interpretation and
equality reflection remain open.** Safe syntax checking is not adequacy,
consistency or source completeness. The separate exact quotient is relative
to supplied native data, without an assumed adequacy theorem.

### Final verification

Official Agda 2.8.0 ARM64 executable: `2.8.0-3d04bac`; archive SHA-256
`9a35071eb9747f984177f48e1ba7008a9cebccfc259a40a0a84b29ffc2ec2db6`.
Cubical v0.9 commit: `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.
Provenance, official download URL, initial toolchain failures and recovery:
`/tmp/pts-rk-agda-2.8.0.MvVO53/TOOLCHAIN.md`.

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh
```

Exit **0**, **04:41:14–04:41:34 UTC**. Full logs, command, versions, all nine
source hashes and copy/stability checks: `/tmp/pts-rk-combinatory-agda.M1bpnK`.
The script rejects changed/untracked Cubical source, copies project modules
to a fresh directory and checks the entire import closure with `--safe`,
`--ignore-interfaces`, isolated configuration/data and no default libraries.
Cubical mode comes from source pragmas, not a global flag. No postulates,
holes, unsafe casts or disabled termination/positivity/universe checks are
used. No opaque or optimization-flag workaround remains. The paper's safe
syntax was inspected, but its unchecked eliminators and postulated models
are not imported. Earlier fresh runs `.ViNmqG` and `.LsgtLi` passed the
three-atom I/K/P checkpoint only; the final run supersedes them.

`bash theories/CombinatoryLogic-rk/build-note.sh` exits **0** in
`/tmp/pts-rk-combinatory-note.c58OXY`, **04:42:55–04:43:06 UTC**. LuaHBTeX
1.24.0/TeX Live 2026 and latexmk 4.88; restricted shell escape, actual
minted/Pygments output and installed DejaVu Sans Mono for Unicode Agda.
No layout, missing-glyph, unresolved-reference or minted warning.

```sh
swift docs/direct-r-handoff/verification/combinatory-agda-2026-10-22/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-agda-pdf.QaZM2w
MM0_RS=/tmp/pts-rk-mm0.lhphPY/upstream/mm0-rs/target/release/mm0-rs \
MM0_C=/tmp/pts-rk-mm0.lhphPY/mm0-c \
bash theories/CombinatoryLogic-rk/check-mm0.sh
shasum -a 256 -c _build/combinatory-completeness-audit.fG2a7B/source-after.log
```

All exit **0**. PDF inspection checks section order, current Agda notation,
source links, MM0 excerpt/full source and all nineteen Rocq badges. Result:
**13 pages, 3 appendix pages, 19 badges, 40 links**. All pages rendered;
changed Agda pages visually inspected, and both long code blocks kept
unbroken. MM0 compilation/reference checking passes **4/4** stages in
`/tmp/pts-rk-combinatory-mm0.ITdtk4`, including the ten prior proof regressions.
The MM0 source and all seventeen Rocq files plus Dune are unchanged.
The preceding fresh Rocq audit remains the assumption evidence: no new
Rocq audit or full CI is claimed. Shell syntax, scoped whitespace checks
and Agda source safety scan pass.

### Failed attempts and their resolution

Toolchain initialization with a global `--cubical` flag caused primitive
mode mismatch (2.8.0 exit 154; exploratory 2.8.0.2 exit 42). Isolated data
and source-only Cubical pragmas fixed it; final verification uses 2.8.0.
An initially created version-specific default data directory was identified
by creation time and moved intact to the toolchain's `recovered-default-data`;
existing user data were preserved. Exact's first individual check lacked the
required guardedness import flag and exited 42; its corrected safe check
passed. Those Exact diagnostics were tool output, not archived raw logs.

Early main-schema checks exited 42: generic `isSetΣ` inside recursive tyOf
obscured positivity; generic path composition in singleton substitution did
likewise; a recursive `tyOf (runAp d)` law guard failed termination checking.
The fixes are guarded truncation with sethood derived outside the mutual
block, the A[id] primitive application guard with an ordinary public wrapper,
and separately computed apTy. These early diagnostics were tool outputs,
not archived raw logs.

Full S development has an exact scratch ledger at
`/tmp/pts-rk-agda-2.8.0.MvVO53/S-DEVELOPMENT-LEDGER.md`.
Direct mutual integration and generic/opaque/specialized path-composition
variants all failed positivity (exit 42); their four `combinatory2*.log`
files are retained. The finite literal builder itself checks rapidly, but
fresh seven-field record/data bundles caused excessive elaboration. Initial
run PID 61334 was terminated after 51 seconds/~16 GB (143); PID 61643 ended
137 (cause not independently confirmed, last observed 62 seconds/~11 GB);
PID 68003 was terminated after 55 seconds/~29 GB (143). These three runs had
only initial Checking output and no retained raw log. A duplicate canonical
run was also terminated (143); its log was later overwritten, as the ledger
explicitly records. Subsequent bisections used 15-second timeouts and a 4 GB
heap cap. Fresh record/data bundles and no-forcing trials timed out (124).
Nested built-in Sigma pairs avoid the expansion: the complete bundle checks
in about 0.69 seconds; all seven canonical proofs in about 0.87 seconds.
No forcing flag or opaque workaround is retained. Final fresh verification
has no timeout or memory failure.

PDF attempts: `.8MYT1g` passed the initial rearrangement; `.rCFf2w` compiled
but validation exited 1 for missing Unicode glyphs and an overfull formula;
`.wHjnp5` exited 12 because fontspec had not been explicitly loaded. A local
Unicode font/fontspec and corrected Markdown math fixed these. `.UgN2ms`,
`.1rZpSL` and `.WBsiwY` passed; visual inspection then motivated keeping both
long code blocks unbroken. Final `.c58OXY` passes all checks. All are retained
under `/tmp/pts-rk-combinatory-note.*`; final renders/text/links are in the
verification directory above.

Final SHA-256:

```text
744ee50fffca33e664aab57a1371370ab3a05d23a47c31afa01bcd281bbf5500  CombinatoryPTS-rk.tex
077ac6f4498d9b0c09a7b59e69712953556ffce7e05e9b9071a3742adfc1d905  CombinatoryPTS-rk.pdf
05cc2c8acc85a3c90a26910123f3e7a3463e728706727745a98b923d9a88c2f5  check-agda.sh
ef3a5484f745a5cf5ac8d3debde9e39e9d7aa160ed5b68c545b8559098e845d2  agda/Combinatory.agda
9fa380e41b85b290d5c6931b4a4fae678a728da913e50aea3eb67b84bac13428  agda/SCanonical.agda
40d1b58f5e600a1407abf0bb7de62c22fd702edcfd7a667eeb4ef69d0eb74f3d  agda/SGuardIrrelevance.agda
```

HEAD remains `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`. No staging, commit
or push; all unrelated changes and IDE intent-to-add entries are preserved.
Next proof obligation is logical-coherence guard admissibility, then native
interpretation/reflection. The original Rocq major-chain/completeness goal
is unchanged. Next exact check is the fresh Agda command above.

## Current checkpoint: executable MM0 Hilbert specification

`CombinatoryPTS-rk.mm0` is a 156-line, many-sorted Horn specification of the
65-shape Hilbert system. It explicitly defines numerical graphs, annotated
de Bruijn shifting/substitution, contextual beta reduction, fixed ranked
telescopes and the six Hilbert rules. A syntax-only `form` graph produces
exactly P11/I7/K17/S30 through fixed catalogue rows, not an original typing
oracle. The 65 count concerns shapes, not distinct parameter instances.
The mathematical correspondence argument is an induction through these
graphs, then Hilbert derivations; **no MM0/Rocq adequacy bridge has been
machine-checked**. MM0 axioms specify this theory; no Rocq axiom was added.

### Actual MM0 checks

The official tools were built in an isolated temporary directory from
`digama0/mm0` commit `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` (clean checkout).
Compiler: mm0-rs 0.1.0, built with isolated Rust 1.99.1; independent reference
checker: mm0-c, compiled with Apple Clang 21.0.0. No global tool installation
or user security allowlist was changed. Exact tool-build commands, versions,
limitations and negative-test commands are in `/tmp/pts-rk-mm0.lhphPY/AUDIT.txt`.
Initial successful build outputs were tool responses, not retained log files.
The later recorded Rust build is explicitly CACHED, exit 0; repeated fresh C
compilation exits 0 with 23 upstream printf warnings and a linker alignment
warning. These are not clean-warning builds of our own source.

```sh
MM0_RS=/tmp/pts-rk-mm0.lhphPY/upstream/mm0-rs/target/release/mm0-rs \
MM0_C=/tmp/pts-rk-mm0.lhphPY/mm0-c \
bash theories/CombinatoryLogic-rk/check-mm0.sh
```

Exit **0**, all **4/4** stages at **03:15:15 UTC**. Retained logs, exact
commands, source hashes and certificates: `/tmp/pts-rk-combinatory-mm0.Bl222O`.
Both specification compilation and mm0-c verification pass. The compiler
reports four sorts, 36 terms/definitions and 55 axiom declarations; the
catalogue's 65 indexed shapes are compressed into 17 fixed catalogue rules.

The companion
`docs/direct-r-handoff/verification/combinatory-mm0-2026-10-22/CombinatoryPTS-rk-examples.mm1`
has ten actual local theorem proofs and two local definitions, no added
axioms. Its binary certificate passes mm0-c against the SAME public .mm0
specification (four sorts, 38 terms/definitions, 65 axioms/theorems).
Tests cover rank-zero universe and identity, both identity applications and
their beta reductions, and the capture-sensitive substitution
`sub z v1 (lam v0 (app v1 v0)) (lam v1 (app v2 v0))`.
The annotation is substituted, the free argument shifts, and bound v0 stays.
In temporary negative source `capture-bug.mm1`, replacing that v2 by v1 is
rejected: compiler exit **1**, mm0-c exit **3**. The compiler emits an invalid
error-marked certificate; the independent checker rejects it. Negative logs
`capture-bug.compile.log` and `capture-bug.check.log` are retained beside
the tool-build manifest, not included as project proofs. No timeout occurred.

Checking the axiom-only specification establishes declaration well-formedness,
not consistency or completeness. The ten proofs are useful regression tests,
not an all-index adequacy or original-PTS-to-Hilbert completeness proof.

### Note and unchanged Rocq development

Section 4.1 explains the first-order interpretation, proof terms, bounded
template generation and common-reduct conversion, with a highlighted literal
excerpt. The complete source appears on appendix pages **12–14**, exactly
three pages; both listings read the one .mm0 source file. Pygments 2.19.2 has
no bundled MM0 lexer, so a local `listings` language highlights declarations,
comments and math strings. Existing minted/Pygments Agda highlighting remains.

`bash theories/CombinatoryLogic-rk/build-note.sh` exits **0**, final build
`/tmp/pts-rk-combinatory-note.rwsq7f`, finished **03:16:56 UTC**. Toolchain:
latexmk 4.88, LuaHBTeX 1.24.0 (TeX Live 2026). No layout, glyph, unresolved
reference or minted warning. Earlier drafts compiled/validated with exit 0
but text inspection caught missing listings: `.FXOv9p` rendered raw commands
literally (03:11:30–03:11:41); `.3ZS6Of` had an empty excerpt range
(03:12:38–03:12:49). Both are `/tmp/pts-rk-combinatory-note.*` directories
with retained logs. Percent macros and an explicit TeX space in the range
prefix fixed them. `.WVeDbs` (03:14:30–03:14:40) was already correct, then
superseded by the final common-reduct explanation and proof-example link.

```sh
swift docs/direct-r-handoff/verification/combinatory-mm0-2026-10-22/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-mm0-pdf.B8Ovnb
shasum -a 256 -c _build/combinatory-completeness-audit.fG2a7B/source-after.log
```

Both exit **0**. The PDF check requires the Section 4 excerpt, complete-source
appendix of at most three pages, MM0 source/example/reference links and all
19 existing Rocq badges. Result: **14 pages, 3 appendix pages, 19 badges,
35 links**. All pages rendered; changed prose and appendix pages were visually
inspected. Final text/link/render evidence is `_build/combinatory-mm0-pdf.B8Ovnb`.
All seventeen Rocq modules and their Dune file match the preceding fresh
kernel-audit hashes; `rocq-unchanged.log` is in the MM0 verification directory.
No Rocq proof or CI rule changed; the preceding audit remains the assumption
evidence, not a new audit claimed for this documentation/MM0 change. Shell
syntax and scoped `git diff --check` pass. No new full CI run was needed.

SHA-256:

```text
07e6954ee3f8f046ed12ee05f64a276e6e5c9e488678e791b05e2943a5a95e0b  CombinatoryPTS-rk.mm0
3b3f8bc6a4fb8d5a9ebd319ffbdb7304f038c0523ad99f83a8acc1c2239b3b54  CombinatoryPTS-rk.tex
acbcd23410a0f029bf29c6f96055a37c38838fab44b94f415b3387806e064faa  CombinatoryPTS-rk.pdf
b55d18bb8113acccebe62fb2dca56d8ca0264bccb664659038184d413bb9d587  CombinatoryPTS-rk-examples.mm1
```

HEAD remains `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`; no commit, push or
staging. Existing unrelated work and IDE intent-to-add entries preserved.
Original-PTS-to-Hilbert Rocq completeness, four-core completeness and
intrinsic equality reflection remain open as described below.

## Current checkpoint: contextual Hilbert proofs and ranked QIIRT

The note now gives an explicit mathematical completeness corollary for the
literal 66/65 catalogues: finite symbolic-template inclusion into our catalogue,
followed by Bunder–Dekkers Theorem 9.4 and the checked 65/66 simulation. This is
an EXTERNAL mathematical proof, not a new Rocq theorem or axiom. Neither the
symbolic inclusion nor the general shortness/deduction argument is formalized.
In particular, there is still no unconditional Rocq theorem
`typ ε M A -> CatalogueEconomy.Derives M A`.

Six new modules provide genuine internal proof steps:

- `ContextualHilbert`: 21 closed reports. H+ derivations have universe/scheme
  leaves at the empty context and start, weakening, application, conversion
  and both reduction rules. No abstraction/product rule or native-typing
  constructor premise. Soundness supplies native context validity; the start
  lemma supplies an INTERNAL declaration-sort derivation. Empty-context H+
  is equivalent to both concrete closed catalogues. Convertible application
  reduces the two domains to a common reduct, without assuming correctness
  of Hilbert types.
- `ContextualSubstitution`: seven closed reports. General simultaneous
  substitution and its single-variable specialization use H+-certified images,
  not a native checker. No deduction theorem is needed.
- `ProductExposure`: eleven closed reports. Exposure preserves the exact
  schema type prefix, commutes with substitution and simulates each original
  beta step. Catalogue exposure therefore follows arbitrary application
  spines to the lambda with the SAME annotated domain and body. This does not
  select or type an exposed head for an arbitrary Hilbert product derivation.
- `CatalogueShapes`: four closed reports. Exactly seven neutral-ended shapes,
  with literal native terminal bodies, have (binders, body applications)
  P6=(3,1), I1/I4=(2,0), K1/K6=(4,0), S1/S8=(6,3). Other tails are sorts or
  products. The numerical decrease is not alone a typed shortening theorem.
- `HilbertAbstraction`: eighteen closed reports. Exact I/K abstraction,
  product formation from a supplied family abstraction, and dependent-S
  application abstraction from supplied domain/result-family abstractions.
  These explicit inputs are not claimed to have been constructed in general.
- `HilbertReplay`: six closed reports. A finite acyclic application program
  references shared H+ premises. Its typing elaborates into H+; the local
  dependent-S six-to-three contraction preserves exact result type Cx(gx),
  forward native beta reduction, and the same input pool. The repeated x is
  one pool vertex. Interleaved weakening/conversion in arbitrary chains is
  not covered by this local theorem.

The first remaining Rocq obligation is arbitrary major-premise-chain
shortening with a genuinely well-founded sharing measure, followed by
length-controlled typed product exposure, internal type correctness and
deduction admissibility. Ordinary tree size duplicates S's x proof; maximum
proof height can also increase during its contraction. No discarded measure
is asserted sufficient, and no conditional theorem assumes completeness.

The Agda specification now follows Chen–Nordvall Forsberg–Tsai (CPP 2026):
terms lose their type index, `tyOf` recursively returns a ranked type pair,
constructor equalities retain intrinsic typing, and term paths have explicit
recursive type-path clauses. Ordinary Agda retains a typed setoid rather than
silently deleting quotient equations. Cubical set-truncation coherence and the
exact native-expansion quotient are stated separately. No lambda, function
eta, unrestricted quotation, postulate, or unchecked eliminator is added.
The snippets remain PSEUDOCODE, not Agda-verified definitions. Minted/Pygments
highlighting is local to this note; the build checks actual highlighted output.

### Fresh seventeen-module audit and complete CI

```sh
bash docs/direct-r-handoff/verification/combinatory-completeness-2026-10-22/AUDIT.sh
```

Final exit **0**, **19/19** stages, **02:24:10–02:25:00 UTC**. Logs
`_build/combinatory-completeness-audit.fG2a7B`; fresh absolute build
`/tmp/pts-rk-combinatory-completeness.0GagN7`; separate pristine archive/build
`/tmp/pts-rk-combinatory-completeness-pristine.9z34Nq`, upstream
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`. Exact commands, versions, timestamps,
source manifests and stage logs are retained in the audit directory.

There are **159 own closed reports**, **160 aggregate** including the unchanged
upstream report. Recursive checking of all seventeen modules passes and its
complete assumption inventory is byte-identical to freshly checked pristine
upstream: only unchanged upstream functional extensionality, no unsafe entries.
Original-source, source-stability, safety and scoped whitespace checks pass.
Comparing the preceding audit manifest confirms all eleven earlier proof
modules remain byte-identical. Pinned OCaml 4.14.2, Dune 3.23.1, Rocq 9.2.0,
Stdlib 9.1.0 and Equations 1.3.2+9.2 are unchanged.

```sh
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/combinatory-completeness-full-ci.1noh6m \
  bash tools/check-local-ci.sh
```

Exit **0**, actionlint and **227/227** stages pass without retry; exit file
timestamp **02:24:40 UTC**. Driver log/exit, stage logs, `stages.tsv`, versions
and `result.txt` are retained. This is full CI coverage with mostly cached
unrelated targets, not fresh assumption evidence for those developments.
No CI stage was removed or weakened; only the existing combinatory Dune alias
was extended.

### Final note, PDF and Agda compatibility check

```sh
bash theories/CombinatoryLogic-rk/build-note.sh
```

Final build `/tmp/pts-rk-combinatory-note.xQ0lm0`, exit **0**, finished
**02:30:59 UTC**. Ten pages, no overfull boxes, missing glyphs, undefined
references or minted warnings. Actual Pygments output is checked by the build,
not inferred from merely loading minted. The local renderer resets percent's
catcode while reading Pygments files; an earlier visual draft exposed that
Markdown/minted interaction and it was corrected without changing shared
LaTeX infrastructure. Whole signature blocks are kept together.

```sh
swift docs/direct-r-handoff/verification/combinatory-completeness-2026-10-22/inspect.swift \
  /Users/akuklev/air/pts-rk/theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-completeness-pdf.mMbycs
```

Exit **0**: ten rendered pages, **19** valid local proof links and **11**
reference links. The inspector checks the new source links and the supplied
CPP 2026 paper URL. Text/link inventories, all page renders and exit/log are
retained in that directory. Newly changed pages 5–10 were visually inspected;
no clipped code or leaked Pygments comment characters remain. Build command,
versions, timestamps and build/validation exit codes are in the build directory.

Final source SHA-256:
`79b65c323671f00a4b2b4d588667ec3e37b5cd9348bed9eccea8aa75a205479d`.
Final PDF SHA-256:
`0356b7a15806dafe361a83e3fae3980278415eda34aa62fa5666b177b676e2e5`.

The read-only paper-artifact compatibility probe ran from
`/tmp/pts-rk-qiirt-research.4OTKCJ/TTasQIIRT/src`, artifact commit `8db0830`:

```sh
agda --cubical -i . Theory/SC+El+Pi+B/QIIRT-tyOf/Syntax.agda
```

Exit **1** under installed **Agda 2.6.0.1**, at bundled `Prelude.agda:47`:
`Malformed syntax declaration: syntax must alternate holes ... and non-holes`.
The artifact targets 2.8.0. Its source and the paper were inspected, but no
new toolchain was installed, no unsafe artifact eliminators were imported,
and neither the artifact nor the proposed snippets is claimed checked here.
Raw command/version/diagnostic/exit files were copied into
`_build/combinatory-completeness-pdf.mMbycs/agda-*` for retained evidence.

### Retained failures and targeted evidence

- Initial focused audit `_build/combinatory-completeness-audit.Ko2LoS`:
  exit 1 in fresh-build at 02:21:32 UTC, `CatalogueShapes.v` line 112,
  `b is already used`. Its tactic's names were made fresh; a subsequent
  targeted attempt needed `cbn` before `lia`. No theorem statement changed.
- `CatalogueShapes` attempts 01–03 are retained under
  `_build/catalogue-shapes.rmYggN`; final targeted build
  `/tmp/pts-rk-catalogue-shapes.9FGoYT` exits 0, four closed reports.
- Contextual/Hilbert-abstraction iterations and final recursive checks:
  `_build/contextual-hilbert.pIQ6Ep`, fresh builds
  `/tmp/pts-rk-contextual-hilbert.UeQtHY` and
  `/tmp/pts-rk-hilbert-abstraction.ZQCbF7`. Early errors were explicit native
  context-lookup reduction, dependent empty-index elimination, binder/parser
  names and reduction normalization. Final builds and kernel inventories pass.
- `HilbertReplay`: exact commands and early failures in
  `_build/hilbert-replay-2026-10-22/COMMANDS.md`, fresh build
  `/tmp/pts-rk-hilbert-replay.x7Ci6e`. Explicit return-reference selection and
  conjunction splitting fixed the first errors; final six reports and
  recursive check pass.
- Root's targeted commands used `opam exec -- timeout 300 dune build
  --build-dir /tmp/pts-rk-completeness-dev-20261022 --display=short --no-buffer
  -j 2` followed by the corresponding `.vo` targets. Initial ProductExposure
  compilation failed at a renamed dependent-elimination hypothesis `HE`;
  initial ContextualSubstitution failed at the eliminated index name `i`.
  Explicit hypothesis/index patterns fixed both. Final targeted builds exit 0.
  These early root diagnostics were interactive; the final fresh audit above
  is the durable complete source/assumption evidence. No timeout occurred.

HEAD remains `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`; no staged content,
commit or push. Existing unrelated work and IDE intent-to-add entries are
preserved. Historical checkpoint entries below retain their original paths
and counts; they do not override this current status.

## Previous checkpoint: algebraic syntax and a checked 65-shape catalogue

The note now specifies a first-order contextual generalized algebraic theory
and idealized Agda-shaped QIITs. The weak independent signature has contexts,
rank-indexed types, terms, substitutions and typed I/K/S/P equations. It has
no lambda, function eta or unrestricted type-to-term quotation. A separate
exact typed-image quotient uses ORIGINAL typing and annotated beta equality
at both endpoints, with transport between type fibres. This is explicitly a
relative specification, not a replacement checker or a completeness proof.
Neither pseudocode signature is claimed machine-checked. New primary references
are Kaposi–Kovács–Altenkirch (2019) and Altenkirch–Kaposi (2016).

Five new Rocq modules close the next concrete catalogue obligations:

- `IdentityCatalogue`: seven numerical shapes, five closed endpoints for
  original typing, exact sorting and literal type/exposure maps.
- `ConstantCatalogue`: eighteen numerical shapes, the same five endpoints.
  This is a conservative explicit reconstruction; the paper's unlisted count
  of seventeen is not silently asserted to match it or declared a typo.
- `SubstitutionCatalogue`: thirty numerical shapes, six closed endpoints,
  including exact sorting of the represented declared types. Fixed telescope
  builders only factor these fixed shapes; scheme indices contain no source
  terms, derivations or arbitrary bodies.
- `CatalogueHilbert`: combines P11/I7/K18/S30 into 66 shapes; eleven closed
  endpoints. `derive_declared_type` derives every atom's type INTERNALLY;
  `derive_exposure` handles catalogue atom subjects. Soundness and typed
  forward-beta extraction have no catalogue-soundness hypothesis left.
- `CatalogueEconomy`: fourteen closed endpoints. The explicit 65-shape datatype
  omits local K13 and derives it by `K_(0,0) U_1 U_a (P5(b,c))`, with exact
  annotated beta recovery. `derives_iff` proves identical Hilbert judgments
  for the 65/66 systems by replacing axiom leaves with independent derivations.
  It does not identify the paper's numbering or preserve its shortness measures.

There are **92 own closed reports** (51 previous + 41 new). Source-PTS-to-
Hilbert completeness remains open, as do four-core completeness and intrinsic
equality reflection. Literal finite-catalogue closure is not the general
symbolic fresh-sort-substitution theorem. No original rule, annotation or
conversion was changed; the preceding six proof modules remain byte-identical.

### Fresh proof audit and complete local CI

```sh
bash docs/direct-r-handoff/verification/combinatory-gat-2026-10-22/AUDIT.sh
```

Exit **0**, **19/19** stages, 2026-10-22 01:36:23–01:37:09 UTC. Logs:
`_build/combinatory-gat-audit.FoWhA6`; `commands.txt`, `status.tsv`, version
inventory, before/after manifests and every stage's raw log are retained.
Fresh absolute build `/tmp/pts-rk-combinatory-gat.hDbC80`; separately archived
and built pristine upstream `/tmp/pts-rk-combinatory-gat-pristine.bwllE6`,
commit `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

Fresh compilation prints **93** closed reports: 92 own plus one unchanged
upstream. Recursive checking of all eleven modules succeeds, and its complete
inventory is byte-identical to freshly checked pristine upstream. Only the
unchanged upstream functional-extensionality axiom is loaded; no unsafe,
type-in-type or assumed-positivity entries. Original-source comparison,
source/Dune stability, admission/unsafe scan and scoped whitespace checks pass.
Existing duplicate same-source dependency warnings in NormalizationComplexity
are retained. Pinned versions are unchanged: OCaml 4.14.2, Dune 3.23.1,
Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2.

```sh
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/combinatory-gat-full-ci.ZhCicn \
  bash tools/check-local-ci.sh
```

Exit **0**, actionlint and **227/227** stages pass without retry,
01:36:24–01:36:53 UTC. The existing combinatory stage now includes all eleven
modules; no CI stage was weakened or removed. This is complete driver coverage
with mostly cached unrelated targets, not fresh assumption output for those
developments. Driver output/exits/timestamps, stage logs, versions and
`stages.tsv`/`result.txt` are retained in that directory.

### Development attempts

- I/K: `/tmp/pts-rk-ik-catalogue.XYnVar`, logs `_build/ik-catalogue.kJFzas`.
  Dependency build, first direct compiles, ordinary Dune `dune-01.log` and
  recursive kernel check all exit 0. Direct output went into the fresh build,
  never the source directory. Inventory matches retained pristine upstream.
- S30: `/tmp/pts-rk-substitution-catalogue.FTVerP`, logs
  `_build/substitution-catalogue-2026-10-22`. `direct-01.log`, `build-01.log`,
  `kernel.log` all exit 0. Direct output-path masking warning disappears with
  the ordinary Dune build; no diagnostic was suppressed.
- Combined catalogue: `/tmp/pts-rk-catalogue-hilbert.FTYqQS`, logs
  `_build/catalogue-hilbert-2026-10-22`. First Dune compile and kernel check
  exit 0, complete inventory matches pristine upstream.
- Economy: `/tmp/pts-rk-catalogue-economy.5vwM7f`, logs
  `_build/catalogue-economy.od5cw7`. `attempt-01.log` exits 1 because a local
  Ltac matcher needed to recognize the unfolded derivation alias. Corrected
  without a mathematical change; `attempt-02.log` and `kernel.log` exit 0.
  Fourteen own reports closed, inventory matches pristine upstream.

Normal targeted commands use the pinned environment and
`opam exec -- timeout 300 dune build --build-dir DIR --display=short --no-buffer
-j 2 theories/CombinatoryLogic-rk/NAME.vo` (I/K ordinary build did not need
the timeout wrapper). Kernel checks use `rocq check -silent -o` with the fresh
PTSrk and Combinatory load paths. The fresh audit records complete exact
commands independently of these incremental attempts. No timeout occurred.
An exploratory read of CatalogueEconomy before its creation returned file-not-
found; this was not a compilation failure and did not change files.

### Note verification and scope

`bash theories/CombinatoryLogic-rk/build-note.sh` exits 0 in final
`/tmp/pts-rk-combinatory-note.B5iS8i`. Nine pages, no LaTeX, overfull/underfull,
reference or missing-character warnings. The exact QIIT signature is kept
together on page 8 and references on page 9. Thirteen proof badges target
local Rocq sources; eight reference URLs are present. Mathematical review
checks rank sorting, dependent transports, typed quotient endpoints and the
weak/exact equality distinction. No formalization badge is attached to the
unimplemented QIIT signatures.

All note builds succeeded: `TXUCbj` (eight-page draft), `gH3cza` (review
clarifications), `WeI9Ok` (samepage did not prevent verbatim splitting),
`J5bJVP` (whole-signature minipage), final `B5iS8i` (references together).
These are suffixes of `/tmp/pts-rk-combinatory-note.` and retain exact command,
exit, version and TeX logs. Versions: latexmk 4.88, LuaHBTeX 1.24.0,
TeX Live 2026. No shared LaTeX runtime was modified.

The PDF inspector is
`docs/direct-r-handoff/verification/combinatory-gat-2026-10-22/inspect.swift`;
it checks required GAT/QIIT content, source and reference links, and renders
every page. Final inspection and visual evidence are recorded in the live
BUILD entry and `_build/combinatory-gat-pdf-final.wm5Jze`; all final pages were
inspected, including both signatures. Exact successful inspection command:

```sh
swift docs/direct-r-handoff/verification/combinatory-gat-2026-10-22/inspect.swift \
  /Users/akuklev/air/pts-rk/theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-gat-pdf-final.wm5Jze
```

| New/current source | SHA-256 |
| --- | --- |
| IdentityCatalogue.v | `1db9f4dee89476e6c29b016f3635bf75d233eec6efa7346d37eb9aacbae859fb` |
| ConstantCatalogue.v | `4cd7e8e52fccd76447151af2d5f7ae693e44101d125e8cca94bf1882c1b88250` |
| SubstitutionCatalogue.v | `7ae9977eff62fbc5e2352ed1e51e2ee3443aa70350b19db89e07b517b8a3c123` |
| CatalogueHilbert.v | `7d54bd8c066a5870c5a20d90e7591a640c5333590813bce55e46ebe8d8328b59` |
| CatalogueEconomy.v | `f77a79debcc0e7a0050d4f992467e9d73bceda6265e8a56862790c7b133226b6` |
| dune | `399dfea9436280dd694fdf0ab7b4f2eeb96c6338c3f4d573c1da336986b645b2` |
| CombinatoryPTS-rk.tex | `e308f4ab4d1eea65ab5085913f5d0e26e45af6d422c1dee2cb36bec73b070c24` |
| CombinatoryPTS-rk.pdf | `18a3b7cd0e4d2025e4d02134fa74814d0a8479948ebd33147ab17852afdecfae` |

HEAD remains `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`, with no staged
content, commit or push. Existing unrelated edits and IDE intent-to-add entries
are preserved. First remaining completeness goal: define contextual Hilbert
derivations H+ and prove length-controlled exposure for arbitrary derived
products, not only atoms. This supports internal correctness of types and
deduction admissibility; original native typing cannot supply those missing
Hilbert witnesses. Next exact check is the new fresh audit command above.

## Previous checkpoint: Hilbert proof codes and the product catalogue

The physical directory is now `theories/CombinatoryLogic-rk`; the library
remains `PTSrk.Combinatory`. Core, Presentation and FiniteBasis are unchanged.
The new modules establish the following contracts in original annotated PTS-rk:

- `ProductCatalogue.scheme_typed` and `scheme_type_sorted`: all eleven
  numerically indexed Bunder–Dekkers product shapes and their exact type ranks.
  `type_code_exact` and `exposure_exact` are literal syntax equalities for
  declared-type and product-exposure closure, not eta conversion or a general
  fresh-sort-substitution metatheorem. `p4_code_typed`, `p5_code_typed`,
  `p4_code_beta`, `p5_code_beta` compile two auxiliary shapes into the existing
  four-family `Presentation.Expression`, with independent `HasType` proofs.
- `Hilbert.Derives`: an independent closed Hilbert inference system, with
  universe/scheme leaves, application, conversion, subject reduction and type
  reduction. `derives_sound` and `derivation_extract` require separately proved
  catalogue typings only as a metatheorem premise. Extraction produces a
  binder-free code whose originally typed expansion reduces forward to the
  derivation's subject; it does not give all extracted codes a separate
  combinatory typing judgment. Types retain original annotated syntax.
- `ProductHilbert`: the concrete numerical I/K/S plus eleven-product catalogue
  discharges that premise. `derives_sound` and `derivation_extract` are
  unconditional apart from the independent Hilbert derivation.
  `derive_product_type` establishes every product atom's type formation inside
  that Hilbert system, with literal and typed product type codes.

There are **51 own closed assumption reports**: the previous 32, eight in
ProductCatalogue, four in Hilbert, and seven in ProductHilbert. No full
65-shape catalogue, PTS-to-Hilbert completeness, four-core completeness or
intrinsic strong equality completeness is claimed. The complete Hilbert
presentation in the note uses the explicitly external Bunder–Dekkers theorem;
it is not imported as a Rocq axiom.

### Fresh proof and full-CI verification

```sh
bash docs/direct-r-handoff/verification/combinatory-hilbert-2026-10-22/AUDIT.sh
```

Exit **0**, all **19** stages pass, 2026-10-22 00:59:24–01:00:00 UTC.
Raw logs: `_build/combinatory-hilbert-audit.H87sn7`; exact shell-escaped
commands, exits/timestamps, versions, manifests and output are in
`commands.txt`, `status.tsv`, `packages.log`, `source-before.log`,
`source-after.log`, `fresh-build.log` and the per-stage logs.
Fresh absolute build: `/tmp/pts-rk-combinatory-hilbert.ZBLheh`.
Separately archived and built pristine upstream:
`/tmp/pts-rk-combinatory-pristine.iMsccY`, commit
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

Fresh compilation prints **52** closed reports (51 own, one unchanged
upstream). Recursive checks of all six modules and pristine upstream pass;
the complete inventories compare byte-for-byte equal, containing only the
unchanged upstream functional-extensionality axiom and no unsafe entries.
Original kernel source comparison, source/Dune stability, safety scan and
scoped whitespace checks pass. Same-source dependency-path warnings from
NormalizationComplexity are retained, not hidden. Toolchain: OCaml 4.14.2,
Dune 3.23.1, Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2.

The staged driver adds `01-combinatory` without removing any existing stage.
Complete local CI, including actionlint and pristine upstream, passes all
**227** stages, exit **0**, 00:59:31–01:00:01 UTC, with no retry:

```sh
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/combinatory-hilbert-full-ci.OO1Ub7 \
  bash tools/check-local-ci.sh
```

That directory retains `driver.log`, `driver.exit`, `start.txt`, `end.txt`,
`stages.tsv`, `result.txt`, version inventory and all stage logs. Most existing
targets were cached; this is full driver coverage, not fresh assumption output
for unrelated developments. The separate focused fresh audit above supplies
new assumption evidence for this development.

### Note and PDF

`CombinatoryPTS-rk.tex` uses the repository's LaTeX–Markdown class and shared
development preamble. The five-page `CombinatoryPTS-rk.pdf` explains the logical
system, proof objects, the Hilbert rules and the external completeness boundary.
Its nine badges link to adjacent Rocq sources; no unpublished GitHub target is
invented. The bibliography includes Bunder–Dekkers, Definition 7.3/Theorems
7.2 and 9.4, and the suggested Jones overview.

```sh
bash theories/CombinatoryLogic-rk/build-note.sh
swift docs/direct-r-handoff/verification/combinatory-hilbert-2026-10-22/inspect.swift \
  /Users/akuklev/air/pts-rk/theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-hilbert-pdf.dyMANc
```

Final TeX build `/tmp/pts-rk-combinatory-note.Y2Kfbl`, exit 0; no LaTeX,
overfull/underfull-box, reference or missing-character warnings. Versions:
latexmk 4.88, LuaHBTeX 1.24.0, TeX Live 2026. PDFKit inspection exits 0,
checks all nine source links and three reference links, extracts text and
renders all five pages. All five rendered pages were visually inspected.
Raw text, links, images and inspection result are in the inspection directory
above. Script syntax and final scoped whitespace checks pass.

### Development attempts and limitations

- ProductCatalogue: fresh `/tmp/pts-rk-product-catalogue.cMCnPq`, logs
  `_build/product-catalogue.Jj3S1b`. Attempts 01–05 exit 1: rank-normalization
  tactic, expression inference, two implicit term-scope arguments, then an
  incorrect product-congruence lemma name. Attempt 06 and recursive kernel
  check exit 0, eight own reports closed.
- Hilbert: fresh `/tmp/pts-rk-hilbert-calculus.j4rOZh`, logs
  `_build/hilbert-calculus-2026-10-22`. Build 01 exits 1 before compilation
  because the concurrently registered ProductCatalogue file did not yet exist;
  build 02 (first actual Rocq compilation) and kernel checks exit 0. Four own
  reports closed; the rechecked retained pristine inventory matches.
- ProductHilbert: fresh `/tmp/pts-rk-product-hilbert.REddtN`, logs
  `_build/product-hilbert-2026-10-22`. Build 01 and recursive kernel check exit
  0, seven own reports closed. An early inventory comparison before the
  checker finished exited 1 on an empty log; comparison after completion exits
  0. No source correction or retry was needed.
- Note: first build `/tmp/pts-rk-combinatory-note.lvAHPN` exits 12 because the
  Markdown class requires a literal document-class declaration in its local
  preamble. Fixed in the wrapper, without changing shared LaTeX code. Builds
  `tuRi6n`, `gqAhHp` and final `Y2Kfbl` under the same temporary prefix exit 0;
  the latter two incorporate the new proofs and scope-review refinements.

Targeted proof commands use `opam exec -- dune build --build-dir DIR
--display=short --no-buffer -j 2 theories/CombinatoryLogic-rk/NAME.vo`
(ProductHilbert additionally `timeout 300`). Kernel checks use `rocq check
-silent -o` and the corresponding fresh PTSrk/Combinatory load paths.
The fresh audit records complete exact commands independently of these
development attempts. No timeout occurred.

| New/current source | SHA-256 |
| --- | --- |
| ProductCatalogue.v | `fec19bbb0a7e0468a55c9555fa109016b2c222c8ebcf7eefa565774e3dff1d34` |
| Hilbert.v | `c7069fadd23eefed1905803fd97b88f75cec0785a6acef8bc7619ced98cf2778` |
| ProductHilbert.v | `6ce269001009f96e2811365f0114a3ef33257b77f3713abd605cf8e11e73f1e1` |
| dune | `61bdd9cd5bf1aa9bfc8145a31e592318444a65ad01ca61ccfec23757d6633202` |
| CombinatoryPTS-rk.tex | `58897a29fce86935a73a15a7479706bea994b92cf824f78ce03d9105aa740fa6` |
| CombinatoryPTS-rk.pdf | `6a8428b9763c2a6998c7f9925078a165bbabba527e29cd99f55668edcf9a5dea` |

HEAD remains `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`; no staged content,
commit or push. Existing unrelated changes were preserved. Some earlier
untracked files have IDE intent-to-add entries; this turn did not stage them.
The old directory appears deleted and its replacement untracked until Git
records the rename. Historical logs below deliberately retain old paths.

First remaining proof goal: the auxiliary I/K/S catalogues and their internal
type/exposure derivations, then the converse original-PTS-to-Hilbert theorem.
Compiling the remaining product and I/K/S shapes into the smaller four-family
grammar is a separate economy question. Do not assume the dependent
abstraction recursion is well-founded. Next exact verification command is the
new fresh audit script above.

## Initial checkpoint (historical, before the rename)

The remaining sections record the preceding checkpoint and its original paths;
its status and next-step statements are superseded by the current checkpoint.

### Initial contracts

- `Core.Core`: five arbitrary-index original term families (I, ordinary K,
  dependent K, dependent S, P), with original typings, exact type-sort
  theorems and literal beta laws: 15 closed assumption reports.
- `Presentation.Presentation`: binder-free subjects and an independent mixed
  typing relation; original typing soundness, expansion equality and weak
  reduction simulation: 9 closed reports. Types are original PTS terms;
  equality uses original annotated beta conversion. No completeness theorem.
- `FiniteBasis.no_finite_typed_basis`: no finite fixed typed applicative basis,
  even with all universe atoms and merely beta-convertible recovery. The
  expanded expression must be originally typable. Eight closed reports.

The complete finite-scheme Hilbert result in FORMULATION.md is a specialization
of an external theorem, not a Rocq assumption or a result proved here. The
proposed four telescope families have no implementation/completeness theorem.

## Final fresh audit

Exact reproducible driver:

```sh
bash docs/direct-r-handoff/verification/combinatory-2026-10-22/AUDIT.sh
```

Driver exit **0**, 2026-10-22 00:35:48--00:36:22 UTC. It records escaped
commands, UTC start/end times, exits, versions, source hashes and raw output.
All 17 recorded stages pass. Raw evidence:

- `_build/combinatory-audit.ZXAnfW/status.tsv`
- `_build/combinatory-audit.ZXAnfW/commands.txt`
- `_build/combinatory-audit.ZXAnfW/fresh-build.log`
- `_build/combinatory-audit.ZXAnfW/kernel.log`
- `_build/combinatory-audit.ZXAnfW/upstream-kernel.log`
- `_build/combinatory-audit.ZXAnfW/source-before.log`
- `_build/combinatory-audit.ZXAnfW/source-after.log`

Fresh absolute Dune directory: `/tmp/pts-rk-combinatory-audit.vEp9MB`.
Pristine upstream checkout: `/tmp/pts-rk-combinatory-upstream.AkuTX9`, archived
from `723cf2ec61c737ae82ba33d2e7db44f650122b0e` and compiled separately.

The aggregate build has **33** closed reports: 32 new reports and one unchanged
upstream normalization report. Recursive kernel checks of all three modules
and pristine upstream exit 0. Their complete assumption inventories compare
byte-for-byte equal: only upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`, no
type-in-type, unsafe fixpoints, or assumed positivity. All new printed theorem
dependencies are closed. Original kernel source files also compare unchanged
against that upstream commit. Source/Dune hashes are stable across the audit.

Rocq dependency discovery reports duplicate paths to the same Core source,
and analogous existing warnings in NormalizationComplexity. They are retained
in the log; compilation and kernel verification succeed. No warning is hidden.

Pinned toolchain: OCaml 4.14.2, Dune 3.23.1, Rocq 9.2.0,
Stdlib 9.1.0, Equations 1.3.2+9.2. The script sets the documented local opam
root and `pts-rk-ci` switch and records the installed package inventory.

This was a **focused** audit, not a new complete staged local-CI run. The
existing user-owned full-CI/self-interpreter activity was not interrupted.
The new independent Dune audit is not yet added to the staged CI driver.

## Development attempts

Core and Presentation used `/tmp/pts-rk-combinatory-core.CMUv8g` with retained
logs in `_build/combinatory-core-2026-10-22`:

- `attempt-01.log`: exit 1, the local constructor-producing tactic needed
  beta unfolding; fixed without changing the judgment.
- `attempt-02.log`, `attempt-03.log`, `attempt-04.log`: exit 0, successively
  adding ordinary K and exact type-sort reports. Final own count 15.
- `kernel.log`: recursive Core check exit 0.
- `presentation-01.log`: exit 1, missing typeclass discharge for application
  congruence of beta equality; fixed explicitly.
- `presentation-02.log`: exit 0, 9 closed reports.
- `presentation-kernel.log`: recursive Presentation check exit 0, inventory
  matches Core.
- `versions.log`: installed toolchain inventory.

FiniteBasis used `/tmp/pts-rk-combinatory-finite.GMUFkK`, with retained logs in
`_build/combinatory-finite-basis-2026-10-22`:

- `build-01.log`: exit 1 before compilation because the concurrently registered
  Core module had not yet been created.
- `build-02.log`: exit 1, an application-rank invocation needed explicit
  arguments; corrected.
- `build-03.log`: exit 0, 8 closed reports.
- `kernel.log`, `core-kernel.log`: recursive checks exit 0; inventories also
  matched the retained pristine-upstream inventory from 20 October.
- `versions.log`: installed toolchain inventory.

Development build commands were `opam exec -- dune build --build-dir DIR
theories/Combinatory/NAME.vo`; the FiniteBasis calls used `timeout 300`,
`--display=short --no-buffer`. Recursive checks used `rocq check -silent -o`
with the fresh PTSrk, Combinatory and, for FiniteBasis, NormalizationComplexity
load paths. No timeout occurred. The final script above supplies a single
fully recorded fresh verification independent of those incremental attempts.

An attempted semantic bootstrap, `jbcontext search`, exited 127 because the
command is unavailable. Source exploration continued with `rg` and file reads.
Two early exploratory reads used nonexistent guessed builder/common-code
paths, exited 1, and were corrected by inspecting actual filenames. Neither
was a proof build.

## Audited source hashes

| Source | SHA-256 |
| --- | --- |
| Core.v | `882d92e73f5b645d76502a43e09d0f7fb7a42cd43c7c308665585719bbe8179c` |
| Presentation.v | `ce6f0102834b139d534bb7d0f72b2bcedf242d2542dff7ca2bfef7924fc05b82` |
| FiniteBasis.v | `09b22cb13feb263818c7454a0e6d1b7039781b74925b0b501a121f7a45317731` |
| dune | `86c46597dae6bc70de03af37b695e32fc17a53f86b94f7ac72af4a52b4ab6ce1` |

## Worktree and next step

Base HEAD: `cb76553b03d536743e36c4e2c7e5a1c7c1669bef`; index empty.
No commit or push was requested or performed. Existing unrelated dirty
sources/docs/logs were preserved. This work adds Combinatory, its audit
script, repository index links, and prepended handoff entries.

First mathematical goal: uniform original typings and beta recovery for the
auxiliary product-exposure/type-family catalogue in the proposed telescope
grammar, before claiming four-family completeness. The independent strong
equational presentation remains a separate question. Next exact verification
command is the fresh audit script above.
