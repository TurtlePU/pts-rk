# Combinatory formulations of PTS-rk

This development uses the original annotated `Syntax.Term nat`,
`Typing.typ`, `Ranks.RankSorts`, and beta conversion. It does not extend the
original calculus with constants or eta conversion. Combinator names denote
closed original terms.

The concise [LaTeX–Markdown note](CombinatoryPTS-rk.tex) and
[compiled PDF](CombinatoryPTS-rk.pdf) give a rank-typed SK interface, a full
dependent Hilbert catalogue, and generalized algebraic presentations. The Rocq
namespace is `PTSrk.Combinatory`. The PDF's proof badges link to adjacent Rocq
and Agda files; keep the PDF with those sources.

The introduction states the six goals of the second PTS-rk paper: three
principal Agda presentations (Church-encodable natural-model QIIRT,
binder-free normal-first model, and cumulative bounded fragments),
Hilbert/MM0 correspondence, internally sound partial finite models toward
the specified consistency target, and indexed self-interpretation with
source folds and CPS. The [second-paper plan](SECOND-PAPER-PLAN.md) gives
the staged work, acceptance criteria and unresolved encoding/uniformity
questions. These are targets, not completed results; this planning revision
does not start new formal development.

[SK.v](SK.v) proves typing and forward native beta correctness of intrinsic
simply typed SK codes and deterministic bracket abstraction without eta.
The surface has only S and K; identity is derived as S K K. The note gives
a checked linear numeral family of 10n+4 atoms, with rank and arithmetic
computation theorems. Arbitrary dependent compilation is
not inferred: the full 65-shape Hilbert catalogue is a separate presentation.

The independent [SK QIIRT](agda/Combinatory.agda) defines `Con`, `Sub`, `Ty`, `Tm`
and computed `tyOf`/`RankedTy`, with dependent S/K/P families and guarded
equations. The note's highlighted excerpts come directly from this source.
Its safe checking is not a native interpretation, equality-reflection theorem
or dependent-completeness proof. The [exact expansion quotient](agda/Exact.agda)
is separately parameterized by original syntax, typing and equality data.

The independent binder-free experiment has a total SK normalizer in
[BinderFreeCore.agda](agda/BinderFreeCore.agda), with intrinsic simple typing,
forward reduction certificates and irreducible outputs. It uses neither
lambda expansion nor fuel. [BinderFreeBidirectional.agda](agda/BinderFreeBidirectional.agda)
decides an independent declarative typing relation and composes checking
with normalization. [BinderFreeCoherence.agda](agda/BinderFreeCoherence.agda)
proves weak conversion iff equality of normal forms;
[BinderFreeEquality.agda](agda/BinderFreeEquality.agda) decides that equality,
retaining every atom's type parameters. [BinderFreeQuotient.agda](agda/BinderFreeQuotient.agda)
identifies the actual weak-conversion set quotient with normal forms and
reuses the same normalizing application. Primitive identity is unnecessary;
the normal family has only S/K spines and inert ground labels. These six
modules total 1,021 lines, including proofs, comments and executable tests.

[SKNativeCanonical.agda](agda/SKNativeCanonical.agda) supplies the native-beta
reference and its actual quotient. The canonical SK pipeline
returns binder-free representatives of that stronger equality.
[SKSource.agda](agda/SKSource.agda) gives intrinsically typed lambda syntax
whose erasure preserves original typing and commutes with native greedy
passes. [SKSourceEquality.agda](agda/SKSourceEquality.agda) proves erasure
injective, recovering hidden application types from the retained annotations.
[SKSourceRank.agda](agda/SKSourceRank.agda) computes a sufficient redex-rank
budget directly from source syntax, without evaluating typing proofs;
normal sources have budget zero. [SKSourceNormal.agda](agda/SKSourceNormal.agda)
uses this budget to normalize without a partial parser or termination premise,
and proves agreement with every independently sufficient native budget.
[SKBracket.agda](agda/SKBracket.agda) compiles it deterministically to SK,
with forward native beta correctness and no eta optimization.

[SKCanonical.agda](agda/SKCanonical.agda) composes expansion, source
normalization and compilation. Its `normalize` preserves native beta meaning
and is idempotent. For inputs of the same simple type, it gives equal SK trees
exactly when the original expansions are beta-convertible.
`normal-form` returns an actual `SK.Nf`, and
[SKCanonicalNormal.agda](agda/SKCanonicalNormal.agda) proves the output
irreducible. The fixed-point family `Canonical` is isomorphic to the native-beta
quotient, has decidable equality, and supports total `apply-and-normalize`
agreeing with quotient application. `check-canonical` combines the independent
declarative SK checker with this canonical output. The algorithm uses typed
lambda syntax internally: it is not a directly binder-free canonical evaluator.
[SKCanonicalExamples.agda](agda/SKCanonicalExamples.agda) checks computation
by `refl`, including reduction under lambdas, newly created redexes, identity
codes and canonical application; function eta remains distinct.

[CanonicalAlgebra.agda](agda/CanonicalAlgebra.agda) packages these canonical
codes with computed `tyOf`, typed fibres, a proved fibre isomorphism,
normalizing application and decidable equality. It uses ordinary Sigma types,
not a claimed dependent IIRT or an assumed normalization theorem.

[NormalizedSubstitution.agda](agda/NormalizedSubstitution.agda) constructs
normal substitutions over original dependent contexts. Images have original
typing with propositionally truncated witnesses. Normalizing composition
preserves dependent typing and gives actual identity/associativity paths;
equality corresponds exactly to native beta conversion.
[NormalizedFamilies.agda](agda/NormalizedFamilies.agda) supplies normal
dependent types and inhabitants, normalized substitution action and its
identity/composition laws. Smart reindexing retains literal normal codes
and agrees with ordinary dependent transport.
[NormalizedComprehension.agda](agda/NormalizedComprehension.agda) adds context
projection, variables, dependent pairing and lifting, with proved uniqueness,
naturality and comprehension equations. Its context eta law is not function eta.
[NormalizedProducts.agda](agda/NormalizedProducts.agda) supplies universe
decoding, dependent products/abstraction and total normalized application,
with original beta and typed substitution-naturality laws. These are proved
equalities of normal representatives, not added quotient constructors.
[NormalizedExamples.agda](agda/NormalizedExamples.agda) checks polymorphic
identity/application, substitution that creates a redex in a dependent type,
typed pairing/lifting and the IR context interface.

[NormalizedInference.agda](agda/NormalizedInference.agda) computes normal types
and their universe ranks from mere original typability. The result is
independent of typing and well-formedness witnesses; computed-type fibres
are isomorphic to original typed-normal fibres. Every original derivation
normalizes into this carrier with exact native beta correspondence.
[NormalizedContexts.agda](agda/NormalizedContexts.agda) defines a genuine
inductive-recursive `Con`, `length` and decoded `context`, extending by normal
dependent declarations. Its operations derive mere well-formedness and
eliminate it using proved witness independence; no chosen certificate is
required for normalizing type/term action or computed types.

[NativeBidirectional.agda](agda/NativeBidirectional.agda) goes beyond certified
normal inputs: structural inference and checking decide the ORIGINAL `Typ`
judgment for arbitrary annotated subjects and candidate types in a well-formed
context. An untrusted-context entry point decides `WellFormed Γ × Typ Γ t A`.
Normalization is invoked only after constructing native typing evidence;
negative branches refute all original derivations. Nine `refl` regressions
cover dependency, invalid inputs and reducible target/function types. No
separate checking judgment replaces the original rules.

This normal-form-first dependent interface retains original binders and uses
the established native normalizer. Its IR context grammar is not a simultaneous
IIRT of all normal syntax and hereditary evaluation. A literal interpretation
of the independent QIIRT, dependent binder-free compilation and full-presentation
code savings remain open; mutual definition alone does not remove termination
or coherence obligations.

[SKDirectSoundness.agda](agda/SKDirectSoundness.agda) proves that direct weak
SK reduction expands to forward original beta reduction at every simple type.
Direct normalization and application preserve native typing and can precede
canonicalization without changing its result. At **ground output type**,
[SKDirectGround.agda](agda/SKDirectGround.agda) proves that direct evaluation
already produces the exact native-beta canonical code: normalization,
application and conversion decision need no lambda intermediate.
[SKDirectBoundary.agda](agda/SKDirectBoundary.agda) gives canonical function
and argument inputs whose weak application has four atoms, while its canonical
function-valued result has eight. Thus weak application need not preserve the
canonical family at function output types; this does not rule out a stronger
direct evaluator.

[SKBracketSize.agda](agda/SKBracketSize.agda) proves that compilation uses at
most `4^s` atoms for a source of s nodes. The complete canonicalizer therefore
uses at most `4^(tower d N)` output atoms, where N counts the annotated native
expansion and d is the computed source budget. Each S, K or ground label counts
as one atom. This bound excludes type-index payloads, label bit lengths, proof
objects, compiler working storage and runtime.

These SK constructions are **not a replacement for the dependent PTS QIIRT/IIR**.
[BinderFreeBoundary.agda](agda/BinderFreeBoundary.agda) checks that distinct
weak-normal SK codes can have beta-equal original annotated expansions.
Function eta is not a valid repair. Both SK pipelines use simple types and
natural-number labels, interpreted as universe terms by native expansion;
unbounded labels make fixed-length fibres infinite. The canonical construction
does not supply dependent PTS coverage or strong normalization of every
combinator reduction sequence. A directly binder-free native-beta canonical
evaluator at arbitrary output types, dependent QIIRT adequacy and code savings
for the full PTS presentation remain open.

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
type rank. These bounds concern annotated syntax states; the separate SK
atom-count bound above does not bound a whole dependent typechecker's memory.

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
it is **not itself a fixed finite first-order model**. Increasing grades
does not supply closure under every valuation. The separate guarded Rocq
models below supply fixed finite domains and total operations for explicitly
bounded quantified rules, not for the full unrestricted native interface.

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

The grounded target now includes **Void denials**, not just positive Horn
clauses: every alleged closed judgment `t : Void` implies falsity. Every
constrained model therefore has an empty ground Void fibre. The existence
condition is discharged for the actual 65-shape Hilbert catalogue using
original native normalization/canonicity; it is not a consistency assumption.
[HilbertGrounding.v](HilbertGrounding.v) proves exact grounding and ground
entailment reflection. Its substitution/reduction side conditions retain
their native meaning; the literal MM0 graph correspondence is proved below.

[FiniteHorn.v](FiniteHorn.v) computes the least model of a finite clause list
in at most its number of clauses, exactly reflecting every fragment query.
[HilbertFiniteModels.v](HilbertFiniteModels.v) instantiates this algorithm
with original judgment atoms, derives native typing, and excludes **every**
closed Void subject, including those absent from the input. Singleton-domain
models still distinguish their nullary predicates; they are not all-true
models. A signed completion additionally reflects every propositional formula
over a chosen finite observation set. Its negative facts are new constraints
relative to that fragment and need not survive addition of more source rules.

[FiniteHornChurch.v](FiniteHornChurch.v) generates literal original-PTS
query/formula/denial truth-table programs, with typing and exact forward-beta
true/false correspondence. Nonempty-input operator types have rank r+2.
Saturation/table generation is external: this is not internal uniform
reflection or a proof about all inhabitants of a Church encoding.

[FiniteUniversalHorn.v](FiniteUniversalHorn.v) goes beyond source-ground
instances: for a supplied finite candidate domain and semantic rule templates,
it enumerates **every semantic valuation**, proves exact universal-rule
satisfaction correspondence, and decides whether a relational interpretation
satisfying the denials exists.
[MM0FiniteSignature.v](MM0FiniteSignature.v) and
[MM0FiniteAxioms.v](MM0FiniteAxioms.v) supply the actual nine-constructor,
eleven-predicate signature and all 55 literal universally quantified axioms.
Every rule passes a proved sort/arity checker. A separate textual crosscheck
compares the expanded MM0 source; it is not a kernel-verified parser.
[MM0SyntaxSoundness.v](MM0SyntaxSoundness.v) proves substitution/evaluation
agreement and soundness of independent source derivations, and computes
their translation into finite semantic Horn proof trees.

[MM0FiniteSearch.v](MM0FiniteSearch.v) enumerates **all** total constructor
interpretations, rather than requiring an accepted candidate as input.
On three separate copies of an m-element domain there are
`m^(2 + 3*m + 3*m^2 + m^3)` tables. Success constructs an all-valuations
model of exactly the selected axioms plus universal Void denial; failure
excludes every interpretation at that cardinality. The current specialization
uses equal cardinalities for the three sorts. Completeness of search is not
an unconditional existence theorem or an efficiency claim.

[MM0ProjectionModel.v](MM0ProjectionModel.v) supplies a concrete two-element
model of the subtheory omitting `sveq` and `f0`, with nonempty typing and
enabled application. These omissions are essential, not minor exceptions:
substitution becomes identity and empty `form`/`ax` disable the catalogue.
Both missing axioms are explicitly refuted in this model. Full55 singleton
rejection is checked; no full55 finite model is asserted. Existence of a
successful two-element search is proved analytically, without running the
`2^28`-candidate search.

[FiniteModelRealization.v](FiniteModelRealization.v) generates actual native
PTS proofs of every finite semantic clause and a continuation conjunction of
all valuation instances, of rank at most four. Inhabitability of that
independently defined type exactly matches candidate acceptance.
[FiniteModelSoundness.v](FiniteModelSoundness.v) recursively compiles arbitrary
finite Horn proof trees to original PTS proofs; its source trees contain
no native typing premise. These are externally indexed proof-producing
translations, not one internal uniform reflection theorem over all represented
fragments or arbitrary Church inhabitants. The grounded target still uses an
infinite recursive vocabulary; none of this identifies original syntax with
a finite equational algebra.
[MM0InternalSoundness.v](MM0InternalSoundness.v) composes these results for
the literal schemas. Successful constructor search supplies a native
satisfaction certificate. The explicit projection model has an unconditional
rank-at-most-four certificate and source deduction translation; acceptance
is proved from its model, not retained as a premise.

[FiniteModelBoundary.v](FiniteModelBoundary.v) proves that total **untyped**
application with the universal K equation forces every finite carrier to be
a singleton. This does not rule out typed/guarded or directed-reduction models.
[FiniteNativeModelBoundary.v](FiniteNativeModelBoundary.v) proves a stronger,
separate obstruction even for directed reduction: native typing/beta
soundness, total compositional application, semantic conversion/type reduction
and empty Void force all Church selectors of every arity to be distinct.
No single ungraded finite term domain meets that full interface. The finite
test version gives an explicit lower bound for fragments containing k selector
tests. It does not exclude size-guarded or graded models, or by itself settle
the literal full55 MM0 theory while original-PTS-to-catalogue completeness
is unproved. Literal MM0/catalogue adequacy is established below.
Full original-PTS soundness therefore needs a more restricted fragment
interface; neither removing essential axioms nor adding guards is silently
identified with the original full theory.

[GuardedFiniteCarriers.v](GuardedFiniteCarriers.v) supplies fixed finite
positional carriers for original annotated syntax, with explicit node-count,
tree-depth and universe-alphabet bounds and one overflow value. Application,
product, lambda and substitution are total, including scope-changing binder
operations. Exactness requires the result to fit as well as the inputs;
none of these guards mentions typing or semantic soundness.

[GuardedHornFragments.v](GuardedHornFragments.v) independently bounds proof
height and all displayed atom costs. It computes sufficient budgets from
source proof trees, proves finite-family coverage, and advances every guarded
rule from stratum h to h+1. A counterexample shows why closure at the same
height would be false even with zero syntax costs.
[GuardedHilbertModels.v](GuardedHilbertModels.v) instantiates this construction
with the six original Hilbert rules on genuinely finite syntax/judgment
domains. All semantic valuations satisfy the staged rules, overflow cannot
be typed, and every semantic Void fibre is empty. Encoded queries exactly
reflect bounded catalogue derivability. Its qualitative auxiliary rule graphs
retain original beta/conversion meaning; finiteness alone does not make
those graphs executable. Coverage is for catalogue proofs, not the still-open
original-PTS-to-catalogue completeness theorem.

[GuardedBetaGraphs.v](GuardedBetaGraphs.v) computes all original one-beta
successors, including annotation reductions, and exact finite bounded
reduction/common-reduct graphs. Every path state is guarded. All original
finite reduction/conversion witnesses admit numerical bounds; composition
adds path budgets instead of falsely closing a fixed cutoff transitively.
[GuardedHilbertTables.v](GuardedHilbertTables.v) uses those graphs to enumerate
every finite parameter tuple of all six Hilbert rule forms, for selected
numerical catalogue instances. Admission checks syntax and reduction witnesses,
not typing. Its finite least model, Boolean rule graph, all-valuation schema
correspondence, universal Void exclusion and rank-at-most-four native
satisfaction certificate are unconditional. Deductions compile to original
PTS terms. Unlike the staged model, finite saturation does not impose a
proof-height cutoff. These bounds are not a host-memory theorem.

[GuardedHilbertCoverage.v](GuardedHilbertCoverage.v) proves monotonicity in
syntax/path budgets and selected labels, then exact union coverage: a closed
judgment is derivable in the independent catalogue iff one executable finite
fragment answers true. A finite family of proofs shares one budget, including
every reduction-witness state. True queries are represented without overflow.
This does not prove original-PTS-to-catalogue completeness or uniform internal
reflection; the external Void exclusion still uses native canonicity.

[MM0GuardedQuantification.v](MM0GuardedQuantification.v) separately defines
literal MM0 size/depth guards, computed whole-proof budgets, exact guarded
all-valuation grounding/checking and rank-at-most-four native satisfaction
certificates. Its structural representation premise reduces to exact decoding,
not desired typing or consistency. Universal Void denials are not guarded away.

[MM0NativeSyntax.v](MM0NativeSyntax.v) proves injective quotation, exact scoped
decoding and agreement with original renaming/substitution at arbitrary binder
cutoffs. [MM0ComputationalAdequacy.v](MM0ComputationalAdequacy.v) proves both
directions for all nine literal computational graph predicates on sorted ground
inputs. [MM0NativeReduction.v](MM0NativeReduction.v) reconstructs native
reduction from raw reduction starting at a quoted term, deriving endpoint scope,
and proves exact conversion and bounded-witness correspondence.

[MM0CatalogueAdequacy.v](MM0CatalogueAdequacy.v) and
[MM0CatalogueRealization.v](MM0CatalogueRealization.v) identify the 17 numerical
MM0 row families with exactly the 65 native catalogue shapes, in both
directions of independent source derivability, not just evaluator tests.
[MM0HilbertAdequacy.v](MM0HilbertAdequacy.v) then proves literal MM0 Hilbert
derivability iff independent native catalogue derivability. Every raw source
Hilbert proof reconstructs a closed original native term and type; scoping and
native typing are conclusions, not source admission requirements.

[MM0GuardedSyntaxAlgebra.v](MM0GuardedSyntaxAlgebra.v) constructs actual finite
MM0 expression carriers with overflow and all nine total operations. The guard
checks all declared sorts, substituted variable values and premise/head
arguments against numeric size/depth bounds, under every semantic valuation.
It discharges exact decoding without typing or consistency premises.
[MM0GuardedReflection.v](MM0GuardedReflection.v) reflects every accepted query
to an independent source derivation and proves exact source/finite-fragment
union coverage, with faithful decoding of true queries.

For every N>=5 and d>=3, MM0HilbertAdequacy proves unconditional finite-model
existence for all 55 **guarded** schemas (or any selected subset), retaining
the **unguarded** universal Void denial. Void is represented without overflow;
the universe query is true. Native satisfaction-certificate types have rank<=4.
The proof uses source reflection, native catalogue soundness and external
canonicity. The depth d counts MM0 constructor depth, not PTS type rank.
This is not a model of the unguarded full55 theory, original-PTS-to-catalogue
completeness, uniform internal reflection or an independent consistency proof.

[HornProofEncoding.v](HornProofEncoding.v) independently represents a fixed
finite Horn theory/query by quantifying one rank-one proposition per atom,
followed by its selected clause handlers. The proof type has rank at most
three and contains no truth table or model. [HornProofRealization.v](HornProofRealization.v)
compiles every source proof and checks clause introduction from arbitrary
encoded premise inhabitants. [GuardedFiniteSupport.v](GuardedFiniteSupport.v)
provides faithful finite indexing, exact derivability/model/checker transport,
and coverage of every guarded semantic valuation and universal Void atom.

[HornInternalSoundness.v](HornInternalSoundness.v) constructs an actual
original-PTS function from this independent proof type to the query's
truth proposition, for ANY inhabitant of the encoding. Its type has rank<=4.
The generic consumer's typing uses model validity, not canonicity or a
restriction to generated codes. External native canonicity separately proves
inhabitation iff finite derivability. [MM0GuardedInternalReflection.v](MM0GuardedInternalReflection.v)
discharges positive model validity for each fixed guarded fragment, supplies
internal refuters for every Void query at N>=5,d>=3, and proves source-code
realization and exact union coverage with faithful decoding. The positive
proof encoding contains no denial constructors; denials are enforced by
the refuters. Their Void specialization still relies on external canonicity.

[IndexedHornEncoding.v](IndexedHornEncoding.v) makes the query an internal
Church code and quantifies one predicate on that code type. This independent
proof family has rank three. [IndexedHornRealization.v](IndexedHornRealization.v)
gives explicit typed bridges at canonical queries, arbitrary-premise clause
introduction and exact closed inhabitation iff finite derivability.
[FiniteTypeDispatch.v](FiniteTypeDispatch.v) realizes a finite family of
types using a rank-zero Church selector, with exact forward beta reduction.
[IndexedHornSoundness.v](IndexedHornSoundness.v) supplies the actual uniform
consumer `Π q : Code. IProof q → truthFamily q`, whose type has rank four.
Both arguments can be arbitrary original typed terms, including open ones;
generic consumer typing needs no selector canonicity.
[MM0IndexedReflection.v](MM0IndexedReflection.v) specializes it to each fixed
guarded fragment and all its supported canonical queries, including Void.

[MM0GuardProvenance.v](MM0GuardProvenance.v) independently computes raw
constructor observations and structural guards. Overflow remains distinct
from every source tree. Active clauses reconstruct selected source rules
and sorted substitutions; inactive clauses are tautologies. Every raw proof
reflects to a genuine literal source derivation, despite observation aliases,
and every source derivation is covered at finite computed budgets.

[IndexedHornTransport.v](IndexedHornTransport.v) constructs actual internal
proof-to-proof translations across finite atom maps preserving selected
clauses. Its rank-four consumer accepts arbitrary open queries and proofs,
without canonicity. [MM0InternalDecoder.v](MM0InternalDecoder.v) applies it
to semantic-to-raw decoding, with both supports fixed before the query;
the output is an independent raw proof, not merely a truth certificate.
Composition with raw least-model soundness is separately typed at rank four.

[FiniteGeneratedCodes.v](FiniteGeneratedCodes.v) gives independent canonical
generation evidence `Enum_r(q)` and genuine dependent finite case analysis.
It contains no desired guard property or model. Its type has rank at most
`max(3,r+1)` and its consumer type at most `max(4,r+2)`.
[FiniteMapCoherence.v](FiniteMapCoherence.v) uses `Enum_3` to prove internal
finite-map composition, identity and retraction in rank-one Leibniz equality,
with consumer type rank at most five. Bare-code exhaustiveness, cumulativity
between generation ranks and native conversion are not inferred.

[MM0InternalGuard.v](MM0InternalGuard.v) realizes the independently specified
raw guard graph: `Enum_1(q)` produces a graph proof, while separate `Enum_3(q)`
evidence proves that its input projection equals q and its Boolean projection
equals the guard table. The corresponding type ranks are four and five.
Canonical accepted graph proofs externally reconstruct actual selected rules,
sorted substitutions and numerical guards; wrong answers are uninhabited.
The sentinel is rejected and failed source instances remain tautologies.
Both Boolean answers occur in support, not as extra inference axioms.

Arbitrary-query/arbitrary-proof soundness and proof-preserving decoding for
each fixed finite fragment are internal. Fixed guard tables have internal
graph and coherence certificates with the explicit generation inputs above.
The fragment/budgets/tables remain external parameters; a recursive raw-tree
interpreter returning source/substitution records and one budget-polymorphic
PTS correctness theorem remain open. External closed-source exactness and
Void exclusion retain native canonicity. No generated-code-size or runtime
bound is added by these type-rank results.

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
The complete import closure is checked with the pinned toolchain;
see [EVIDENCE.md](EVIDENCE.md) for the latest source-specific result.
No postulates, holes, disabled termination/positivity checks or unsafe paper
recursors are imported. The SK signature proves its structural coherence
guards. General
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
original common beta reduct. These correspondences are machine-checked for
the independent Rocq transcription of all55 literal schemas; the separate
textual comparison is not a verified MM0 parser. In MM0, `axiom`
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

- [SK.v](SK.v): intrinsic open SK codes, original typed expansions,
  annotation-preserving bracket abstraction, beta-conversion faithfulness
  and rank-typed Church arithmetic for the simply typed fragment.
- [SKNativeCanonical.agda](agda/SKNativeCanonical.agda): native-beta faithful
  reference normalization and quotient, with decidable conversion/equality.
- [SKSource.agda](agda/SKSource.agda) and
  [SKSourceEquality.agda](agda/SKSourceEquality.agda): intrinsic simple-type
  source syntax, native typing, exact pass commutation and injective erasure.
- [SKSourceRank.agda](agda/SKSourceRank.agda): syntax-only sufficient native
  redex-rank budgets, with zero budget for normal sources.
- [SKSourceNormal.agda](agda/SKSourceNormal.agda): total intrinsic source
  normalization with automatic rank, native reduction, beta coherence and
  reflection, normal-output identity, idempotence and budget independence.
- [SKBracket.agda](agda/SKBracket.agda) and
  [SKCanonicalNormal.agda](agda/SKCanonicalNormal.agda): deterministic
  beta-correct bracket abstraction and irreducible compiled normal outputs.
- [SKCanonical.agda](agda/SKCanonical.agda): actual canonical SK trees and
  normal forms, native-beta quotient isomorphism, total canonical application
  and independent checking composed with canonicalization.
- [SKCanonicalExamples.agda](agda/SKCanonicalExamples.agda): definitional
  computation regressions and preserved distinction from function eta.
- [SKBracketSize.agda](agda/SKBracketSize.agda): exponential bracket-compilation
  atom bound and `4^(tower d N)` bound for the complete canonical output;
  not a payload, workspace or runtime bound.
- [SKDirectSoundness.agda](agda/SKDirectSoundness.agda): general forward native
  semantics of direct weak evaluation and safe canonicalizer preprocessing.
- [SKDirectGround.agda](agda/SKDirectGround.agda): direct native-beta canonical
  normalization, application and conversion decision at ground output type.
- [SKDirectBoundary.agda](agda/SKDirectBoundary.agda): canonical inputs whose
  function-valued weak result is not canonical, with four versus eight atoms.
- [CanonicalAlgebra.agda](agda/CanonicalAlgebra.agda): computed type fibres,
  proved retraction/isomorphism, normalized application and native typing,
  using ordinary Sigma types rather than a dependent IIRT.
- [NormalizedSubstitution.agda](agda/NormalizedSubstitution.agda) and
  [NormalizedFamilies.agda](agda/NormalizedFamilies.agda): normal dependent
  substitutions, types and inhabitants; original typing, exact beta
  correspondence, normalized action and proved category/functor laws.
- [NormalizedComprehension.agda](agda/NormalizedComprehension.agda): context
  projection, normal weakening/variables, dependent pairing/lifting and
  comprehension/naturality laws without function eta.
- [NormalizedProducts.agda](agda/NormalizedProducts.agda): universe decoding,
  dependent products/abstraction, total normalizing application and original
  beta/substitution-naturality laws, including dependent reindexing.
- [NormalizedInference.agda](agda/NormalizedInference.agda): computed normal
  types/ranks from mere original typing, exact typed fibres and witness
  independence; certified normal conversion/type checking.
- [NormalizedContexts.agda](agda/NormalizedContexts.agda): genuine IR contexts
  with decoded length/context, normal declarations, computed types and
  normalization requiring no chosen well-formedness witness.
- [NativeBidirectional.agda](agda/NativeBidirectional.agda): raw original-PTS
  inference, type/context checking and complete rejection, including nine
  executable dependent/conversion regressions.
- [NormalizedExamples.agda](agda/NormalizedExamples.agda): dependent type
  substitution, polymorphic application, comprehension and IR regressions.
- [Combinatory.agda](agda/Combinatory.agda): independent dependent-SK/product
  QIIRT with computed types, numerical atom families and guarded equations.
  This is a signature, not a dependent-completeness theorem.
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
- [NativeCanonicity.v](NativeCanonicity.v): external original-PTS Void
  exclusion by canonical forms and the existing automatic normalizer.
- [GroundHornConsistency.v](GroundHornConsistency.v): genuine negative
  Horn constraints, consistency-sensitive least models, consequence reflection
  and constructive finite proof support.
- [HilbertGrounding.v](HilbertGrounding.v): exact independent grounding of
  the six catalogue rules, unconditional constrained-model existence and
  empty Void fibres in every constrained model.
- [FiniteHorn.v](FiniteHorn.v) and [HilbertFiniteModels.v](HilbertFiniteModels.v):
  executable exact finite saturation, denial checking, signed-diagram formula
  reflection, and the concrete Void-excluding Hilbert instance.
- [FiniteHornChurch.v](FiniteHornChurch.v): typed original-PTS finite query,
  formula and denial programs, with exact external beta correspondence.
- [FiniteUniversalHorn.v](FiniteUniversalHorn.v): exhaustive finite semantic
  grounding and exact universal-constraint checking for supplied candidate
  domains/rule interpretations, not general PTS model existence.
- [FiniteModelBoundary.v](FiniteModelBoundary.v): the constructive finite
  total-untyped-K equality obstruction, not a no-go for directed/typed models.
- [FiniteNativeModelBoundary.v](FiniteNativeModelBoundary.v): distinctness
  of all Church selectors in a full native-sound model, impossibility of a
  finite ungraded term carrier, and finite-test cardinality lower bounds.
- [FiniteAlgebraSearch.v](FiniteAlgebraSearch.v) and
  [FiniteOperationAlgebras.v](FiniteOperationAlgebras.v): exhaustive finite
  total-operation search, exact table counts and no fallback on semantic rows.
- [MM0FiniteSignature.v](MM0FiniteSignature.v),
  [MM0FiniteAxioms.v](MM0FiniteAxioms.v) and
  [MM0FiniteSearch.v](MM0FiniteSearch.v): checked sorted literal schemas and
  complete constructor/predicate model decision at fixed sort cardinalities.
- [MM0ProjectionModel.v](MM0ProjectionModel.v): explicit all-valuations model
  of the precisely specified weaker subtheory, with counterexamples to the
  two omitted base axioms; not full native PTS soundness.
- [FiniteModelRealization.v](FiniteModelRealization.v) and
  [FiniteModelSoundness.v](FiniteModelSoundness.v): literal rank-bounded PTS
  satisfaction certificates and recursive deduction translation.
- [MM0SyntaxSoundness.v](MM0SyntaxSoundness.v): first-order substitution,
  independent source proof trees, semantic soundness and computed grounding.
- [MM0InternalSoundness.v](MM0InternalSoundness.v): exact native certificates
  for actual selected schemas, successful-search realization and an
  unconditional certificate for the explicit weaker two-element model.
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
- [GroundHorn.v](GroundHorn.v): positive Horn kernel and least-model
  consequence. Its all-true model is not consistency-separating; the
  strengthened constrained target and concrete Hilbert grounding are above.

The library depends on the original kernel, normalization development and
the shared Interpretation_of_R equality routine. It does not import either
arithmetic interpretation, the interpreter or a set model.
The staged CI driver includes this library's audit. The note separates the
mathematical Bunder–Dekkers argument from kernel verification. The remaining
Rocq obligation is arbitrary major-chain shortening with a valid sharing
measure, then length-controlled product exposure, internal type correctness
and deduction admissibility. Neither ordinary tree size nor maximum proof
height handles S's duplicated minor premise. No theorem assumes these missing
results as its own premise. The canonical SK result covers the simply typed
surface. Directly binder-free canonical evaluation at arbitrary output types,
dependent SK compilation, QIIRT completeness/equality reflection and compiled
payload/runtime bounds remain separate obligations. The checked simple SK
atom-output bound does not settle them, nor does full native type checking
identify the independent QIIRT with the normal-form-first algebra.

In the pinned environment described in [DirectR-CI](../../docs/DirectR-CI.md):

```sh
dune build @theories/CombinatoryLogic-rk/audit
bash theories/CombinatoryLogic-rk/build-note.sh
```

Use a fresh absolute Dune build directory to regenerate assumption reports.
The focused [audit script](../../docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/AUDIT.sh)
checks all 50 Rocq modules, builds pristine upstream and compares complete
recursive kernel assumption inventories. Fresh compilation and recursive
kernel checking pass with 693 own closed reports (195 new) and no additional
inherited assumptions. The archival whitespace gate was repaired separately;
the final checks retain the exact raw logs and verify unchanged proof sources.
See [EVIDENCE.md](EVIDENCE.md) for actual verification and limitations.
