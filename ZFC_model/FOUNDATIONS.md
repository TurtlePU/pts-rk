# Foundation-strength goal — open

The source and mathematical audit of 2026-10-14 is recorded in
[BZC_AUDIT.md](BZC_AUDIT.md). It exhibits a relative countermodel to obtaining
the present collected envelope from BZC + injection-gap GCH alone, explains
the bounds supplied by V_(omega+omega), and identifies the exact remaining
bounded-denotation certificate. It does not claim the material BZC reduction
has been proved in Rocq. The distinction between injection-gap GCH and
additional ordinal-cardinal existence assertions matters in this weak theory.

Revised user direction: first reformulate the model already being developed
as a set-sized model in **Bounded Zermelo set theory with Choice (BZC) + GCH
+ existence of V_{omega+omega}**, and finish its soundness proof. Only then
investigate strengthening this result to an interpretation in **BZC + GCH**.
GCH denotes the generalized continuum hypothesis (also written GHZ/GHC in
the requests). This ordering supersedes the earlier interpretation-first plan.
This is a new proof objective, not an established property of the current
development. It does not authorize weakening the original PTS rules or
assuming the soundness/product-coding obligations.

## Ordered milestones for the same model

1. Reformulate the existing construction using V_{omega+omega} as an
   explicit ambient hierarchy. Exhibit bounds for carriers, families, graphs,
   decoding, coding bijections and valuations; construct the set-sized model
   and prove soundness for the original PTS rules. Fix the precise BZC axioms,
   GCH statement and hierarchy-existence statement. Eliminate reliance on
   Replacement and unbounded separation: use the supplied hierarchy to bound
   constructions, replace separation instances by hierarchy-based existence
   constructions where possible, and explicitly certify any remaining bounded
   separation. Do not retain an arbitrary-predicate Comp as a justified BZC
   construction just because its ambient set is bounded.
2. Only after the first milestone and its soundness proof are complete,
   establish, if possible, an interpretation of PTS-rk in BZC + GCH without
   assuming existence of V_{omega+omega}. This is a strengthening of the same
   model result, not a prerequisite or an independent set-model proof track.

The hierarchy-existence assumption supplies bounds and collection of levels;
it is not itself an unrestricted subset-comprehension principle. Every
claimed elimination of separation needs an actual existence proof. Ordinary
bounded separation remains part of BZC unless explicitly eliminated in the
construction. No additional set-theoretic axiom may be introduced silently.

An external family of proofs, one for each fixed rank, is not by itself a
uniform interpretation internal to BZC. Likewise, proving finite powerset
iterations exist separately does not license collecting the whole hierarchy
as a set. Keep these distinctions explicit in the formal statements.

## Existing Rocq evidence does not settle this goal

ModelSoundness now proves the full ORIGINAL typing/denotation soundness,
conversion, coherence, and an empty interpretation of Bottom under explicit
supplied-hierarchy/classical/cardinal/Choice parameters. No semantic
conversion premise remains. This finishes the ambient Ens semantic proof;
the outstanding foundation-strength work is to derive this SAME construction
internally in the specified material theory. The statements below that
recorded semantic conversion as open are historical and superseded by
RankedHereditary, RankedNormalization and ModelSoundness.

The current development lives in the pinned ZFC library's Ens encoding in
Rocq. “Closed under the global context” audits the Rocq theorem dependencies;
it does NOT establish derivability in the first-order theory BZC.

Specific constructions needing a foundation audit:

- Ens's sup constructor permits Type-indexed families. Its uses for images,
  family ranges, graphs and decoding need explicit set bounds or a separate
  interpretation theorem; their Rocq definitions are not BZC certificates.
- Comp accepts arbitrary Ens -> Prop predicates. Each use must be translated
  into bounded separation (with its quantifier bounds exhibited), or proved
  eliminable. Separating from a bounded ambient set alone does not make an
  unbounded predicate a bounded formula.
- reverse_edge and member_edge currently quantify over arbitrary sets.
  The intended graph/domain/value bounds need to appear in the material
  set-theory formulation and be proved equivalent there.
- Finite powerset iteration, code universes and El need a uniformity audit:
  avoid assuming the set of all hierarchy levels or a global graph of all
  decoded carriers without justification.
- Fiberwise and cardinal-coding bijection selection needs an explicit set
  of eligible witnesses before using ordinary Choice; no global/class choice.
- Cardinal comparison, GCH consequences, syntax/valuation coding, and
  substitution/soundness induction must each be checked at the weaker theory.
- For the set-sized target, bound carriers, code sets, graphs, coding maps,
  and valuations in the required hierarchy levels; distinguish a structure
  inside V_{omega+omega} from one assembled using it as an ambient bound.

The existing low-rank powerset representatives may be useful for rank
bounds, but do not yet prove feasibility. Preserve verified lemmas; do not
relabel the current Ens development as a BZC model.

## Reference for the BZC convention

Michael Shulman's [Unbounded quantifiers and strong axioms in topos theory](https://home.sandiego.edu/~shulman/papers/uqsatalk.pdf)
describes BZC as omitting Replacement and restricting Separation to bounded
formulas. His [Comparing material and structural set theories](https://arxiv.org/abs/1808.05204)
provides the broader comparison with structural theories. These are
references for the foundation audit, not citations proving this PTS model.

## Checked material BZC checkpoint

MaterialZermelo.v defines the actual pure-membership axioms for
Extensionality, Empty Set, Pairing, Union, Power Set, von Neumann Infinity,
Foundation, bounded Separation, and Choice. Its choice-function formula has
an explicit graph/no-junk clause and is proved equivalent to the existing
set-indexed family_choice. Ens satisfaction and logical soundness for this
syntactic BZC theory are checked under explicit classical logic and Choice.
There is no new axiom or implicit assumption of PTS soundness.

This result goes from the ambient Ens representation to satisfaction of BZC.
The needed foundation-strength result goes the other way: actual internal
BZC derivations of the supplied hierarchy's constructions and the PTS model.
In particular, BoundedChoice's arbitrary-predicate Comp still needs bounded
formulas for its denotation predicates; an ambient set bound alone does not
provide them. The precise GCH and hierarchy-existence theory, its relation
to tower_envelope, and uniform syntax/valuation/denotation coding are open.
The current target retains hierarchy existence; its necessity for every
possible interpretation has not been established.

CanonicalValuationTransport now transports validity for structurally paired
contexts with actual same-value canonical declaration witnesses. It does
not derive those witnesses for arbitrary original converted contexts.
RankedDenotation retains actual formation and body certificates;
RankedSubstitution proves their rank-zero simultaneous substitution and
normalized-binder transport. RankedHereditary now extends this to all ranks.
RankedNormalization proves agreement with arbitrary original denotations and
derives variable certificates from original valid valuations. ModelSoundness
discharges semantic conversion in the original fundamental theorem. The
material BZC audit remains open.

## Earlier bounded-formula checkpoint

MaterialSetTheory.v now supplies an independent first-order language and
classical deduction system. It embeds bounded formulas with actual guards
and defines the bounded-separation schema syntactically. Ens satisfaction
of that schema is proved using Comp restricted to the formula's own
extensional predicate. Consequently the specialized logical-soundness
theorem no longer assumes satisfaction of that schema. MaterialZermelo now
adds BZC satisfaction as described above. The GCH/hierarchy theory and
weak-foundation interpretation remain open. An Ens satisfaction theorem is
not a derivation of all the native model constructions in BZC.

CanonicalRenaming, CanonicalSubstitution, CanonicalRealization,
CanonicalRootBeta and CanonicalContext prove same-value transport and local
realization/root-reduction lemmas without semantic-conversion assumptions.
Normal nonlambda substitution includes the rank-zero base case. Explicit
normality and constituent realization premises still delimit these individual
results; the higher-rank argument is now proved by RankedHereditary.
They do not certify the bounded definability of denotation predicates used
by ordinary family_choice, nor transport validity across converted contexts.

CanonicalTypeWitnesses.v constructs normal inferred typing witnesses using
original strong normalization/preservation. CanonicalDenotation.v is a
coherent auxiliary subrelation of original denotes, preserving the same
term, lambda annotations, selector and semantic value. Its coherence proof
does not assume semantic conversion or a finite height for denotation
derivations. RankedNormalization and ModelSoundness now prove original
totality and beta/type conversion. Bounded definability of denotation remains
open. Rocq coherence alone does not yield a BZC interpretation.

BoundedChoiceSequence.v reconstructs the choice sequence using bounded
finite-prefix recursion. The new injection is now used by
CardinalClassification.bounded_cardinal_code and hence product coding;
the native sup-nat graph remains only a reference for agreement. This
removes an actual unbounded range construction from that path, without
claiming first-order justification for all native induction/Ens operations.
BoundedModelData.v retains the selector's powerset/Cartesian bound and
shows the global decoder belongs to Power H. It deliberately does not
assert global model data belong to H. The bounded defining predicate for
nonempty subset selection is certified too.

TypedEquality.v is a syntactic prerequisite toward semantic conversion:
native mutual certificates retain original annotations and project to
original typings and beta equality. Its completeness and semantic soundness
are still unproved. No first-order BZC proof system is supplied by this module.

BoundedDecoder.v proves full graph agreement with all_decoding_graph.
Each branch's specification classifies arbitrary accepted inputs by its
actual tag, so no wrong-tag values can enter the combined graph. The
formula-defined graph is total on omega_codes (proved equal to all_codes),
single-valued, and evaluates to decode under the same supplied hierarchy
premises. BoundedDecodedSelection.v uses it in code-witness selection and
proves equality of the witness fibers/source domain with the original
ones. The SAME selector s has the SAME selected values for every admissible
source; all rank-typed dependent products are covered. This removes native
all_decoding_graph as an unexplained parameter of the bounded selected
graph. It does not certify omega_codes/Ens, the hierarchy's existence or
identification with V_{omega+omega}, Choice/cardinal principles in BZC,
arbitrary denotation predicates, or the still-open semantic conversion proof.

BoundedUniverses.v constructs the graph of the exact existing U n by
bounded separation. BoundedSortDecoder.v handles every tag 3*n+2 and proves
agreement with decode. All individual decoder branches are now covered;
BoundedDecoder supplies off-branch exclusion and full graph agreement.
The first-order Ens/BZC certification and typed semantic conversion remain open.

BoundedInfiniteDecoder.v supplies the infinite-code branch, using the actual
3*n+1 tags and the bounded carrier graph. Evaluation agrees with existing
decode at every infinite code under the supplied hierarchy premises.
First-order certification of the ambient construction remains open.

BoundedRecursion.v supplies uniform bounded iteration from a supplied step
graph, using finite separators in correctness. BoundedCodeArithmetic.v
instantiates triple singleton successor and proves the tripling equation
for every numeral. Its bounded_finite_decoder composes that graph with
finite_carrier_graph and evaluates repr(finite n) to finite_carrier n for
all n. The remaining branches are now checked; the first-order Ens audit
remains open.

BoundedCodeSelection.v applies bounded selection to the model's actual
codeWitnessF, with an admissible source domain also defined by bounded
separation. Its graph agrees with the existing global witness selector
using the same s, and every rank-typed dependent function space belongs
to the domain under the existing model premises. This supplies a bounded
representation of the actual selection operation. Its new decoded
specialization justifies the decoder parameter. Arbitrary denotation
predicates and the first-order Ens/BZC interpretation remain open obligations.

BoundedFormulaSelection.v constructs an actual selected graph for a total
bounded-formula relation by separation on Prod A B. Candidate fibers are
bounded by Power B and selection values are certified with applyValueF.
Function membership and predicate satisfaction are proved under ordinary
set-indexed family_choice. This does not provide bounded definitions of
the denotation predicates or settle the first-order Ens interpretation.

BoundedChoice.bounded_relation_choice now invokes one selector on nonempty
subsets of the fixed codomain B, rather than collecting a native range of
candidate sets. bounded_relation_choice_from_selector proves that this
restricted selector suffices. Denotation and paired witness selection
inherit this change. Arbitrary P separation and the native selected graph
still need first-order certification; the formula specialization only
certifies the candidate predicate. Ordinary family_choice is set-indexed,
not a declared global/class-choice axiom, but this does not audit all
constructions feeding its invocations.

BoundedIteration.v constructs the uniform graph numeral n -> carrier n
by a least-closed-relation formula bounded over Power(Prod omega_codes H).
The graph is separated from Prod omega_codes H and its evaluation theorem
holds for all n. Its correctness proof now uses finite separators, each
constructed by bounded formula separation, instead of a native sup-indexed
comparison relation. No set of all separators is required. First-order
induction and the Ens representation still need justification; do not infer
full Replacement elimination from this particular construction.
The code-tag and sort-universe modules now use this construction uniformly.

BoundedPowersets.v supplies a bounded formula for powerset equality under
an explicit adequate subset bound, and a graph formed by separation on
Prod H H. Existing supplied-envelope transitivity and powerset closure
prove this graph is a function H -> H, evaluated correctly on every actual
carrier index. No new model assumption or Choice premise is needed. This
certifies the successor operation, not uniform set-coded recursion or
first-order existence of the supplied hierarchy/Ens representation.

BoundedFiniteCarriers.v proves that finite_carrier n is the least transitive
set containing the members of the singleton numeral n. Minimality needs
only quantification over Power omega_codes, yielding a bounded equality
formula. BoundedGraphs constructs the uniform graph omega_codes ->
Power omega_codes by separation, and its evaluation is proved equal to
finite_carrier n for every n. No family_choice premise is used. This does
not itself recover n from the finite code numeral (3*n); that step is now
provided by BoundedCodeArithmetic. Infinite/sort decoding is also checked;
existence of omega_codes in a first-order BZC calculus remains to be certified.

BoundedGraphs.v constructs a graph by separation on Prod A B, with a
syntactically bounded edge formula built from a supplied formula p(x,y).
BoundedFormulaTransport.holds_rename proves the index-renaming step used
to insert parameters and the edge variable. The graph's application law
is proved; when p is total and uniquely valued in B, the graph is a
function and apply_set satisfies p. No family_choice premise, native
function selection, or graph-as-sup occurs in this construction. It agrees
with graph A f whenever p defines the bounded extensional f. This supplies
the generic separation step used by BoundedDecoder's defining formula,
not a derivation of the underlying Ens/Prod operations in a first-order
BZC calculus.

BoundedApplication.v now gives a syntactic certificate for the separation
predicate in SetApplication.value_fiber and proves equality of the existing
application with the union of that formula-defined fiber. applyValueF
characterizes equality to apply_set using only bounded quantifiers and
set variables, even for empty or nonfunctional graphs. The universally
available value_bound (three unions of the graph) supplies its value bound.
CodeHierarchyBounds.decoding_value_certificate specializes this formula to
the decoding graph, with values bounded by Power (carrier i). This certifies
decoding equality GIVEN that graph; it does not justify the graph's sup-based
construction, code enumeration, finite hierarchy recursion, or the Ens
representation in first-order BZC.

CantorBernstein.v supplies Schroeder--Bernstein for actual set-graph injections,
with excluded middle explicitly quantified in the theorem. The least closed
region is separated from A by quantifying over subsets in Power A. Thus its
construction avoids collecting an omega-sequence of iterates via Replacement.
BoundedComparison.v now translates its base, closed-subset and least-region
predicates into Bounded.Formula and proves equality of the separated regions.
The successor subset and final glued graph now also have syntax certificates
and equality proofs. The graph obtained by bounded separation is proved a
bijection from the two injections and explicit excluded middle. This covers
the three Comp predicates in CantorBernstein.v, not all imported constructions
or a derivation in a first-order BZC calculus.
Closed theorem reports do not erase the explicit classical-logic premise.

The cardinal upper bound has advanced: CartesianMaps/PowersetSquares prove
Cartesian absorption throughout the finite powerset carriers, then the
decoded dependent-product bound at max(m+1,n). This construction uses actual
subset bounds of decoded fibers, so no family of chosen fiber injections is
required. GCH is not used in this upper bound for powerset representatives.
It remains needed for the intended classification into available cardinal
codes. CardinalClassification.v now proves classification of all sets bounded
by a carrier, conditional on explicit family choice, cardinal comparability,
the infinite-powerset-gap principle and classical logic. CountableDichotomy.v
derives the finite/countable dichotomy from family choice by choosing outside
successive finite prefixes. It uses choice on the set of nonempty subsets
of X, not global choice. Consequently decoded_product_code constructs a code
for every typed decoded product, without an infinitude side condition.
The new BoundedChoiceSequence.v replaces that native sequence graph on the
actual classification path using bounded recursion and proves agreement.
These principles' derivation in first-order BZC+GCH and the first-order
certification of native induction/Ens remain unproved. In particular sup
nat is not itself a BZC existence certificate. Carrier-index uniqueness is
unconditional.

FiniteClassification.v closes the finite-embedding case: subsets of finite
carriers are explicitly enumerated, and an injection's image yields a graph
bijection to some finite carrier. Classical logic is explicit, with no choice
or GCH premise. The new range Comp and finite Type-indexed graph require
bounded-syntax/bounded-existence audits before claiming a BZC derivation.

BoundedBijections.v now certifies bijections and the eligible-witness predicate
in the bounded formula syntax. Its graph clause excludes arbitrary non-pair
elements, which functionality alone would not exclude. The separated witness
set has an exact membership characterization, completeness of the supplied
graph bound, and an eight-powerset-step rank bound. This supplies the set
bound needed for ordinary choice. ProductWitnesses.v now proves nonemptiness
for typed decoded products under the explicit cardinal/choice principles.
The witness set lies in carrier (13 + max(m+1,n)); the target-carrier family
is proved equal to the existing bounded range of the decoding graph. Generic
choice pullback for extensional set-indexed families is proved, but coherent
product-code selection (including code identity, not just its carrier) and
first-order BZC derivability remain open.

CodeWitnesses.v advances selection: a bounded formula records a code c,
its decoding-graph value K and a bijection to K, retaining (c,f) as the
witness. Nonemptiness follows from classification; every witness set is
bounded by carrier(13+max(m+1,n)). Family choice on nonempty subsets of that
single carrier supplies one operation for all products at those fixed ranks.
The witness extraction theorem transports the bijection to decode c. This
does not yet establish cross-rank coherence, substitution compatibility, or
derive the explicit cardinal principles in BZC+GCH.

SelectedCodes.v now projects the selected code and bijection, proves their
typing and coded beta law, and establishes fixed-rank congruence under equal
decoded domains and pointwise-equal extensional fibers. ProductExtensionality
proves the underlying equality of semantic dependent products. This removes
the local data-extensionality gap, but not rank-independent selection or the
syntactic substitution/typing soundness induction. Projection graphs use the
existing Cartesian graph construction and inherit its foundation audit.

GlobalCodeChoice.v now removes rank dependence of selection, given a
transitive base W containing omega_codes and a supplied tower envelope H.
All codes and one decoding graph define the same candidate set for a given
semantic source A at every rank; graphs are bounded by Power(Prod H H).
Ordinary choice on nonempty subsets of Prod all_codes (Power(Prod H H))
supplies a single selector. Cardinal strictness proves a code equinumerous
to A cannot exceed any known carrier bound for A. Global projections are
therefore typed and extensional without a rank parameter. This is conditional
on the supplied hierarchy and explicit cardinal/choice principles. The
native all-code set/decoding graph still need their first-order bounded
construction audit; no identification of H with V_{omega+omega} is proved.

GlobalOperations.v proves typing, beta and congruence for rank-independent
typed semantic operations. Its selector premise is the property supplied by
global_selector_exists, not an assumed soundness theorem. Application needs
the product's semantic data, which raw Syntax.app does not carry; the next
layer must justify a typed interpretation and conversion/derivation coherence.
No annotated replacement calculus or erasure bridge has been introduced.

CodeHierarchyBounds.v gives the first model-specific hierarchy connection:
the singleton-numeral carrier is transitive, U_i is included in it, and each
decoded code in U_i is a subset of carrier i. The decoding graph is typed by
the existing dependent-product construction and lies at level i+5. This is
an explicit bound for the actual code representation. It still uses the
existing Ens definitions as inputs; it is not a BZC existence proof for the
hierarchy, graph, or cardinal-coding bijections.

BoundedProducts.v now supplies a syntactic five-variable certificate for
function-space separation. Totality quantifies over A and W; uniqueness over
A and two copies of W; fiber membership additionally quantifies over P(W)
and looks up the fiber through a set graph f. P(W) is a free set parameter,
not a function symbol or unbounded quantifier in the formula. Separating
P(A x W) by this formula gives exactly dependent_product A (apply_set f)
when f is a supplied function A -> P(W). Thus the reconstructed definition
does not use the old unbounded function_laws or indexed family_range.
Existence of the required family graphs, closure of the hierarchy, coherent
cardinal coding and original PTS soundness remain to be proved.

BoundedFamilies.v now reconstructs the range of a set-coded family by a
three-variable bounded formula: exists x in A, application f x y. The range
is separated from P(W), contains no sup in its definition, and equals the
old family_range A (apply_set f) whenever f is a function A -> P(W).
Its union is a subset of W. This removes one indexed constructor from the
reconstructed definition. It does not yet construct the needed family graphs
in BZC or replace the unbounded function_laws predicate used to type f.

The hierarchy-bounded reconstruction now also has explicit rank estimates
in HierarchyBounds.v. Relative to a transitive W, domain and fiber elements
in W give a dependent function space in P^5(W); graphs are in P^4(W) and
the indexed family range is in P^2(W). These account for the actual
nonstandard pair representation. The same function-space estimate holds at
every finite powerset level with overhead five. This supplies bounds for
replacing indexed constructors; it does not yet eliminate those constructors
or certify the unbounded function_laws predicate as a BZC formula.

BoundedFormulas.v now defines intrinsically scoped first-order formulas
whose only atoms are equality and membership, and whose quantifiers are
all bounded by variables. It has no arbitrary Prop atom or unbounded
quantifier constructor. Explicit formulas and correctness proofs cover
empty sets, singletons, unordered pairs, the library's ordered-pair encoding,
and graph application. Ordered-pair auxiliary sets are bounded inside the
pair itself; the proof does not rely on a function-symbol extension of the
bounded language.

BoundedInverse.v supplies an explicit four-free-variable formula for the
inverse-graph separation predicate, and proves that separating Prod B A by
this formula gives a set equal to the existing inverse. The unrestricted
reverse_edge witnesses can be restricted to A and B because membership in
the ambient Cartesian product forces exactly those bounds. All nine new
assumption reports are closed.

This is a syntactic boundedness certificate and a checked semantic
equivalence in Ens. It is NOT yet a derivation in a formal first-order BZC
proof system, nor a certification of arbitrary sup/Comp uses elsewhere.
The hierarchy-bounded model and its soundness remain the immediate target;
the interpretation without hierarchy existence is deferred until afterward.

Status: goal active; neither ordered milestone is proved. If a
target fails, report the exact indispensable stronger principle rather
than silently strengthening BZC or claiming completion of the preferred goal.
