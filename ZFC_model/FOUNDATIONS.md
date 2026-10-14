# Foundation-strength goal — open

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

## Checked bounded-formula checkpoint

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
These principles' derivation in first-order BZC+GCH, and the bounded recursion
translation of the native sequence construction, remain unproved. In
particular sup nat is not itself a BZC existence certificate. Carrier-index
uniqueness is unconditional.

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
