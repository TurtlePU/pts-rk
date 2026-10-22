# Combinatory formulations of PTS-rk

This development uses the original annotated `Syntax.Term nat`,
`Typing.typ`, `Ranks.RankSorts`, and beta conversion. It does not extend the
original calculus with constants or eta conversion. Combinator names denote
closed original terms.

The concise [LaTeX–Markdown note](CombinatoryPTS-rk.tex) and
[compiled PDF](CombinatoryPTS-rk.pdf) give rank-typed BCKW arithmetic, a full
dependent Hilbert catalogue, and generalized algebraic presentations. The Rocq
namespace is `PTSrk.Combinatory`. The PDF's proof badges link to adjacent Rocq
and Agda files; keep the PDF with those sources.

[BCKW.v](BCKW.v) checks numerals containing exactly **n occurrences of W**
and **7n+2 combinator atoms**. B is composition; W is duplication. Successor,
addition and multiplication use **8, 9 and 1 atoms**, respectively. Their
expansions have original PTS typings and forward beta computation; numeral
types have rank 2 and arithmetic-operator types rank 3 over each carrier U_i.
These results do not establish a BCKW compiler for arbitrary dependent terms.
The full 65-shape dependent Hilbert catalogue remains a separate presentation.

The independent [BCKW QIIRT](agda/BCKW.agda) defines `Con`, `Sub`, `Ty`, `Tm`
and computed `tyOf`/`RankedTy`, with literal B/C/K/W/I/P families and guarded
equations. The note's highlighted excerpts come directly from this source.
Its safe checking is not a native interpretation, equality-reflection theorem
or dependent-completeness proof. The [exact expansion quotient](agda/Exact.agda)
is separately parameterized by original syntax, typing and equality data.

The Rocq quantitative proofs bound **every single-beta intermediate** of a
deterministic strategy while preserving original typing and global
redex-rank bound d.
Writing N for the annotated input's node count, the note uses Knuth's bound
`max(2,N) ↑↑ (d+1)`; [KnuthBounds.v](KnuthBounds.v) checks its comparison
with the executable binary-tower bound. Here d bounds all redex heads, not
just the outer type rank. Rank/length alone does not imply finiteness: all U_i
are distinct rank-zero, one-node normal terms. Fixing the input's finite
universe-label alphabet gives a syntax carrier of capacity at most
`(4*N+4) ↑↑ (d+3)`. For application of normal typed inputs, d is the function's
type rank. These bounds concern annotated syntax states, not binder-free
normal output or a whole dependent typechecker's memory.

The checked Agda presentation gives genuine inductive-inductive-recursive
normal syntax, retaining annotations and de Bruijn scope. Its exact-length
typed fibres use the original six PTS rules, not a replacement checker.
Fix an alphabet `labels : Fin a → Nat` with `a ≤ N`; N counts every node of
the annotated term, including its type annotations. `AtMost A k` supplies an
actual injective map `A → Fin k`. The closed normal and typed-normal families
of length N inject into `Fin ((4*N+4) ↑↑ (d+3))`; typing and rank certificates
are propositional fibres, so different proof derivations are not counted as
different terms. The alphabet restriction is essential.

For application, `N = 1 + nodes f + nodes y`. The Agda raw proofs establish
the size bound for d greedy passes and **every single-beta state** of their
deterministic reduction path, without assuming typing or normalization.
`FiniteTrace` compiles that path into a walk whose states are actual finite
indices; its state type has the same Knuth bound. This does not bound the
whole walk type, proof objects or every Agda runtime allocation.

`applyTypedWithin` accepts normal IIR terms with original certificates for
`f : (x : X) → Y(x)`, `y : X`, and the function type's rank d. It returns
`TypedResult inputs`: an actual bounded normal form, a bounded forward-beta
trace, and original typing at exactly `Y[y]`. There is no optional result or
normalization premise. Original typed substitution, confluence, inversion,
subject reduction, rank uniqueness/safety and strict greedy descent are
proved in the `Native*` Agda modules. The raw untyped `applyWithinFinite`
remains a bounded attempt; it is distinct from this total typed interface.

[NativeNormalization.agda](agda/NativeNormalization.agda) also normalizes any
original typed term with a supplied semantic redex-rank bound, retaining its
exact type, rank bound, elementary size bound and bounded beta trace. It
proves conversion iff equality of normal outputs, budget independence and
idempotence. Every reachable state retains original typing and rank.
[NativeRankCoverage.agda](agda/NativeRankCoverage.agda) computes a sufficient
bound from every original typing derivation in a well-formed context, so
`normalize-typed` needs no externally supplied rank or termination witness.

[FragmentEmbeddings.agda](agda/FragmentEmbeddings.agda) gives finite typed
normal carriers per fixed type, with injective size embeddings satisfying
identity/composition and respecting conversion. [FragmentApplication.agda](agda/FragmentApplication.agda)
proves dependent application into the enlarged grade `tower d (1+s+t)`,
native equality for convertible inputs, and coherence under input embeddings.
[FragmentMachineSoundness.agda](agda/FragmentMachineSoundness.agda) certifies
the existing finite-state normalizer/application executor at the exact native
type. The finite alphabet and numerical budget premises exclude clipping;
they do not assume normalization.

[FragmentModelSoundness.agda](agda/FragmentModelSoundness.agda) interprets
independently checked certificates for **all six original rules**, under
arbitrary well-typed syntactic substitutions. Context and valuation checking
derive their native well-formedness/typing; these judgments are absent from
the raw input and its recursive acceptance predicate. The interpretation
computes a sufficient rank and finite alphabet, normalizes subject and type,
and retains exact substituted source typing. `check-and-interpret` rejects
only invalid certificates, never a normalization failure. Every native
derivation has a certificate. Normal outputs respect conversion and
substitution composition, independently of proof witnesses and budgets.

[FragmentPackages.agda](agda/FragmentPackages.agda) counts contexts, types,
values and substitutions jointly, with actual injections into finite sets
at each fixed grade. Every typed valuation has a package at computed bounds.
Alphabet inclusions are coherent and injective; finite prefix alphabets
cover arbitrary native inputs. Their size can exceed node count, so the
general normalization seed includes the alphabet size. These package bounds
do not bound arbitrary proof trees or host runtime allocations.

[NativeCanonicity.agda](agda/NativeCanonicity.agda) proves external exclusion
of `Void = Π X : U₀. X`, hence rejection of accepted closed Void certificates
and emptiness of the finite Void fibres. This is an Agda metatheorem, not an
internal PTS consistency proof. The interpretation is graded and syntactic:
it is **not yet a fixed finite first-order model**. Total operations on fixed
finite domains, coherent dependent semantic fibres and all chosen axioms
under every semantic valuation remain to be constructed. Increasing grades
does not supply that closure.

For each fixed nonempty alphabet and budgets, [FiniteMachine.agda](agda/FiniteMachine.agda)
defines total finite-indexed pass/application tables and proves that their
iteration decodes to the original raw reducer whenever the source size fits
the tower budget. Overflow fallback is never used on those bounded runs.
[ChurchFinite.agda](agda/ChurchFinite.agda) generates literal original PTS
syntax for the tables and their compositions, including apply-then-reduce.
Finite Church data have rank r+1 and maps rank r+2, independently of arity:
the map reindexes continuations at the same answer type. At r=0 these are
ranks 1 and 2; generated program/type size grows with the source budgets.
This is an explicit finite-table specialization, not a general Agda compiler.

[ChurchFinite.v](ChurchFinite.v) proves original typing, ranks and forward
beta computation of every selector, unary table and finite iteration.
Agda separately checks selector typing/normality and exact size 2K+3.
Binary table generation has executable regressions; its generic native
typing/beta theorem and the Agda–Rocq compiler correspondence remain open.
Code-to-code normalization does not construct an internal semantic inhabitant
of Y[y] or bound the generated program by the source N. The external Agda
typed-totality theorem above is separate from compiler correctness.
The note describes fixed finite fragment models and Pakhomov-style internal
consistency as a programme. The checked contextual certificate interpretation
is external; its internal translation and reflection theorem remain open.
Canonical code equations are not internal finite induction.

Grounding the Hilbert rules gives an effective ground-query reduction to a
positive Horn theory with singleton models. The generic derivability/least-model
argument is checked separately. This uses an infinite recursive vocabulary;
it is not a finite-signature interpretation preserving all quantified formulas,
nor a finite faithful model of free syntax. It holds independently of the
quantitative normalization results. The MM0/native adequacy boundary remains.

Contexts and substitutions precede types and terms. `Sub Γ Δ` replaces
Δ-variables by terms in Γ. The supporting [source-only view](agda/TargetView.agda)
computes `ctxOf` and proves round trips for the dependent-core signature;
it is not a second source-indexed QIIRT.

The tested Agda toolchain is 2.8.0 (`3d04bac`) with Cubical v0.9 at
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. With that checkout available:

```sh
AGDA_BIN=/path/to/agda CUBICAL_DIR=/path/to/cubical \
  bash theories/CombinatoryLogic-rk/check-agda.sh
```

The script copies the sources into a fresh directory, isolates compiler
data/configuration, ignores interfaces and checks the complete import closure
with `--safe`. Cubical mode is specified in source pragmas, not globally.
All 52 project modules and their dependency closure pass this fresh safe check
without warnings with the pinned toolchain; see [EVIDENCE.md](EVIDENCE.md).
No postulates, holes, disabled termination/positivity checks or unsafe paper
recursors are imported. The BCKW signature proves its structural coherence
guards and contextual diagonal's type-reindexing equation. General
admissibility of logical beta/application-naturality guards remains open, as
do native interpretation, equality reflection and dependent combinatory
completeness. The supporting [dependent-core signature](agda/Combinatory.agda),
[canonical annotation guards](agda/SCanonical.agda) and
[guard irrelevance](agda/SGuardIrrelevance.agda) remain checked independently.
These QIIRT signatures do not establish an interpretation in the native
calculus. The separate [NativeTyping.agda](agda/NativeTyping.agda) reproduces
its syntax-based typing and rank relations; the `Native*` modules prove the
metatheory used by the normalizer without assuming a QIIRT interpretation.

The [MM0 specification](CombinatoryPTS-rk.mm0) presents the full **65-shape
Hilbert system**, not just the four-family core. It is included verbatim in
the note's appendix, with its rules explained under “A complete Hilbert presentation”.
This is a first-order Horn presentation with four strict sorts (`nat`, `tm`,
`tel`, `judgment`), interpreted by finite syntactic derivations. It does not
assert that arbitrary first-order models are initial or standard.

`lift`, `sub` and `red` explicitly implement de Bruijn shifting, binder-aware
substitution and original annotated beta reduction. `form e L D E M T` is
only a syntax-building graph: it folds a fixed ranked telescope `L` over
`D:E`, using `e` initial lambdas and then products. Only the fixed `ax` rows
can introduce Hilbert axioms; there is no general typing rule for `form`.
Numerical parameters, finite prefixes and exposures generate exactly
P11/I7/K17/S30, omitting the locally redundant K13. No native typing oracle,
arbitrary-body scheme, eta law or arbitrary-telescope scheme is added.
The scheme count is a count of templates, not distinct numerical instances.

For ground syntax, induction on the computational graph derivations gives
their intended operations. `prefix` bounds its output by the input length;
`form` bounds the exposure by that length. The fixed rows then reproduce the
catalogue subjects and declared types (S's ranks use associativity of max).
The final six rules are the independent Hilbert rules; conversion uses an
original common beta reduct. This explains the encoding mathematically,
but is **not a machine-checked MM0/Rocq adequacy bridge**. In MM0, `axiom`
specifies these rules, not new Rocq assumptions. An MM0 derivation certifies
a typing judgment; the PTS term in its subject position is the object-level
proof of the type in its second position.

With `mm0-rs` and the independent reference checker `mm0-c` on `PATH`, run:

```sh
bash theories/CombinatoryLogic-rk/check-mm0.sh
```

Alternatively set `MM0_RS` and `MM0_C` to the two executable paths. The
tested upstream commit is `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` of
[digama0/mm0](https://github.com/digama0/mm0). The script checks both the
specification and the [local proof regressions](../../docs/direct-r-handoff/verification/combinatory-mm0-2026-10-22/CombinatoryPTS-rk-examples.mm1)
against that same public specification. A checked axiom-only specification
does not establish consistency, source completeness or adequacy; the local
proof examples are regressions, not all-index correspondence proofs.
MM0 highlighting uses a local `listings` language; Agda uses Pygments with
DejaVu Sans Mono with a Latin Modern Math fallback for mathematical delimiters.

- [BCKW.v](BCKW.v): rank-typed B/C/K/W/I codes, original typed expansions,
  exact numeral and operation counts, forward beta computation of successor,
  addition and multiplication, and normalization to annotated Church numerals.
- [BCKW.agda](agda/BCKW.agda): independent BCKW(I)/product QIIRT with computed
  types, literal numerical atom families, guarded equations and structural
  contraction. This is a signature, not a dependent-completeness theorem.
- [FiniteSyntax.agda](agda/FiniteSyntax.agda) and
  [NormalForms.agda](agda/NormalForms.agda): original annotated scoped syntax,
  IIR normal forms, exact correspondence with raw normality, and exact-length
  and size-bounded normal families.
- [FiniteBounds.agda](agda/FiniteBounds.agda),
  [ExponentialBounds.agda](agda/ExponentialBounds.agda) and
  [FiniteCarriers.agda](agda/FiniteCarriers.agda): elementary capacity
  inequalities, concrete finite syntax codes, and injective cardinality bounds.
- [BoundedReduction.agda](agda/BoundedReduction.agda),
  [RawSizeBounds.agda](agda/RawSizeBounds.agda),
  [BoundedTrace.agda](agda/BoundedTrace.agda) and
  [FiniteTrace.agda](agda/FiniteTrace.agda): annotated substitution and greedy
  reduction, soundness, bounds on every single-beta intermediate, and actual
  finite-indexed walks. These raw theorems do not assert typed normality.
- [NativeTyping.agda](agda/NativeTyping.agda) and
  [TypedNormalFibres.agda](agda/TypedNormalFibres.agda): original PTS typing,
  semantic redex ranks and finite typed-normal fibres.
  [FiniteApplication.agda](agda/FiniteApplication.agda) and
  [TypedApplication.agda](agda/TypedApplication.agda): raw bounded attempts
  and total typed application, respectively, with exact dependent output
  typing and finite cardinality. [ApplicationExamples.agda](agda/ApplicationExamples.agda)
  checks dependent application, converted inputs and annotation reduction.
- [NativeAlgebra.agda](agda/NativeAlgebra.agda),
  [NativeSubstitution.agda](agda/NativeSubstitution.agda),
  [NativeConfluence.agda](agda/NativeConfluence.agda),
  [NativeInversion.agda](agda/NativeInversion.agda) and
  [NativePreservation.agda](agda/NativePreservation.agda): binder algebra,
  weakening/substitution, confluence, type uniqueness and exact preservation.
- [NativeRanks.agda](agda/NativeRanks.agda),
  [NativeSafety.agda](agda/NativeSafety.agda),
  [NativeDescent.agda](agda/NativeDescent.agda),
  [NativeRankPreservation.agda](agda/NativeRankPreservation.agda) and
  [NativeNormalization.agda](agda/NativeNormalization.agda): original
  rank bounds, substitution safety, strict descent, single-step rank
  preservation and total normalization with uniqueness/idempotence.
- [NativeRankCoverage.agda](agda/NativeRankCoverage.agda): computes a sufficient
  semantic redex-rank bound and normalizes every original typed term in a
  well-formed context without an external rank witness.
- [NativeCertificates.agda](agda/NativeCertificates.agda) and
  [CertificateContexts.agda](agda/CertificateContexts.agda): independent
  decidable proof, context and valuation certificates, native soundness and
  certificate completeness for all six original rules.
- [NativeValuations.agda](agda/NativeValuations.agda) and
  [ContextualNormalization.agda](agda/ContextualNormalization.agda): original
  substitution/comprehension laws, normalized interpretation, conversion,
  witness independence and composition coherence.
- [FragmentAlphabet.agda](agda/FragmentAlphabet.agda) and
  [AlphabetCoverage.agda](agda/AlphabetCoverage.agda): coherent injective
  alphabet maps and exact finite coding of native terms/contexts/valuations.
- [FragmentUniverses.agda](agda/FragmentUniverses.agda),
  [FragmentInterpretation.agda](agda/FragmentInterpretation.agda) and
  [FragmentPackages.agda](agda/FragmentPackages.agda): finite type/value,
  context and substitution carriers, joint package bounds and automatic
  coverage at computed grades.
- [FragmentModelSoundness.agda](agda/FragmentModelSoundness.agda): independently
  checked contextual interpretation with exact typing and finite packaging.
  [FragmentModelExamples.agda](agda/FragmentModelExamples.agda) tests closed
  and dependent/open substitutions, recovery and malformed-input rejection.
  [NativeCanonicity.agda](agda/NativeCanonicity.agda) proves external Void
  exclusion and certificate rejection, not internal self-consistency.
- [FragmentEmbeddings.agda](agda/FragmentEmbeddings.agda),
  [FragmentApplication.agda](agda/FragmentApplication.agda) and
  [FragmentMachineSoundness.agda](agda/FragmentMachineSoundness.agda): finite
  typed normal fibres, coherent embeddings, dependent application and
  original soundness of finite-state execution; not a full model hierarchy.
- [Core.v](Core.v): I, K, dependent S and product combinators, plus an optional
  dependent K; original typings, exact type ranks and beta laws for all indices.
- [Presentation.v](Presentation.v): binder-free subjects, independent typing
  soundness and weak-reduction simulation. Types retain original PTS syntax;
  equality is annotated beta conversion of expansions. Completeness is not claimed.
- [FiniteBasis.v](FiniteBasis.v): no finite collection of fixed typed
  combinators is beta-complete, even with every original universe atom available.
- [ProductCatalogue.v](ProductCatalogue.v): all eleven Bunder–Dekkers product
  schemes, exact original typings/type ranks, literal type/exposure closure,
  and typed four-core compilation with beta recovery for P4 and P5.
- [Hilbert.v](Hilbert.v): independent Hilbert derivations and applicative proof
  codes, with soundness and typed forward-beta extraction for any separately
  verified catalogue.
- [ProductHilbert.v](ProductHilbert.v): the concrete I/K/S plus eleven-product
  catalogue discharges that premise, proving unconditional soundness and
  applicative recovery for this subcatalogue.
- [IdentityCatalogue.v](IdentityCatalogue.v),
  [ConstantCatalogue.v](ConstantCatalogue.v) and
  [SubstitutionCatalogue.v](SubstitutionCatalogue.v): seven I, eighteen K and
  thirty S shapes; all-index original typings, exact ranks and literal
  declared-type/product-exposure closure. K18 is a conservative extra shape,
  not an identification with the paper's unlisted seventeen K shapes.
- [CatalogueHilbert.v](CatalogueHilbert.v): combines all 66
  shapes; internally derives every declared type and exposed product scheme,
  with original soundness and typed forward-beta proof-code extraction.
- [CatalogueEconomy.v](CatalogueEconomy.v): removes one redundant K shape to
  give an explicit **65-shape** numerical catalogue, with exactly the same
  Hilbert derivability as the 66-shape system. Its source-PTS completeness is
  not a Rocq theorem; this equivalence does not preserve shortness measures.
- [ContextualHilbert.v](ContextualHilbert.v): independent contextual H+ with
  no abstraction/product rule or native typing premise; context validity,
  internal start and variable lemmas, convertible-domain application, and
  empty-context equivalence with the 65/66 systems.
- [ContextualSubstitution.v](ContextualSubstitution.v): simultaneous and
  single-variable substitution with H+-certified images, entirely internally.
- [ProductExposure.v](ProductExposure.v): literal subject/type-prefix
  compatibility of catalogue exposure and its forward beta simulation through
  arbitrary application spines, preserving all annotations. This does not
  select or type an exposed head for an arbitrary derived product.
- [CatalogueShapes.v](CatalogueShapes.v): exactly seven neutral-headed
  catalogue cases; each contracted body has fewer application nodes than
  arguments consumed. Other terminal bodies are universes or products.
- [HilbertAbstraction.v](HilbertAbstraction.v): exact I/K abstraction,
  product formation from a supplied family abstraction, and dependent-S
  application abstraction from supplied type-family abstractions. Their
  general existence is not assumed or proved here.
- [HilbertReplay.v](HilbertReplay.v): acyclic application programs over shared
  premises, H+ elaboration, and the local six-to-three dependent-S contraction
  at the same exact type, with forward original beta reduction.
- [AffineDuplication.v](AffineDuplication.v): supporting numeral fragment with
  W and two fixed affine tags, original typing, exact counts and forward
  reduction to unapplied Church normal forms. Its tagged count is 2n+1;
  the expanded BCKW code count is proved separately in BCKW.v.
- [QuantitativeNormalization.v](QuantitativeNormalization.v): deterministic
  greedy-pass sequentialization with bounds on every intermediate, preservation
  of the global redex-rank bound, an outer-rank counterexample, and normalized
  dependent application with elementary peak-size/abstract-cost bounds.
- [KnuthBounds.v](KnuthBounds.v): tetration and comparison of the executable
  binary-tower bounds with the note's Knuth double-arrow bounds.
- [FiniteNormalForms.v](FiniteNormalForms.v): beta preservation of the input
  label alphabet, complete finite syntax/normal enumerations and elementary
  capacities, normalized-application membership, and the rank/length-only
  finiteness counterexample. Bounds count syntax, not typing-proof objects.
- [GroundHorn.v](GroundHorn.v): generic finite Horn derivability iff least-model
  consequence, singleton all-true model, and finite-fragment satisfiability.
  Effectiveness and the Hilbert instantiation are mathematical arguments in
  the note, not new claimed machine-checked bridges.

The library depends only on the original kernel and the normalization
development, not on the interpreter, arithmetic or set model.
The staged CI driver includes this library's audit. The note separates the
mathematical Bunder–Dekkers argument from kernel verification. The remaining
Rocq obligation is arbitrary major-chain shortening with a valid sharing
measure, then length-controlled product exposure, internal type correctness
and deduction admissibility. Neither ordinary tree size nor maximum proof
height handles S's duplicated minor premise. No theorem assumes these missing
results as its own premise. Completeness of either small combinatory signature,
an annotation-preserving dependent BCKW compiler and intrinsic equality
reflection are separate obligations. The
[safe Agda factorization tests](../../docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/dependent/README.md)
check ordinary BCKW substitution formulas and their specific dependent typing
failures; they do not prove general nondefinability.

In the pinned environment described in [DirectR-CI](../../docs/DirectR-CI.md):

```sh
dune build @theories/CombinatoryLogic-rk/audit
bash theories/CombinatoryLogic-rk/build-note.sh
```

Use a fresh absolute Dune build directory to regenerate assumption reports.
The focused [audit script](../../docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/AUDIT.sh)
also builds pristine upstream and compares recursive kernel assumption inventories.
See [EVIDENCE.md](EVIDENCE.md) for actual verification and limitations.
