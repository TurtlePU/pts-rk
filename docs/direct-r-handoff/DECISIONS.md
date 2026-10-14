# Decisions and proof-engineering history

## 2026-10-14 — discharge original semantic conversion and soundness

Normalize existing ORIGINAL denotation derivations structurally, keeping
their actual values. Derive the required variable certificates from original
valid valuations by induction on context well-formedness; do not restrict
the final model's environments. General certified application uses the
all-rank hereditary theorem for both the codomain and an exposed lambda body.
Normal-form uniqueness and canonical coherence then prove equality of actual
values for originally typed beta-convertible terms. Instantiate the existing
original fundamental theorem with this proved conversion lemma.

ModelSoundness exports original typing soundness, arbitrary-witness
membership/coherence/rank, and actual selector existence with soundness.
Its Bottom code is the original product operation over sort zero and the
identity fiber; its decoding is empty by the proved coding bijection and
the empty fiber. This is external model nontriviality, not internal arithmetic
self-consistency. Keep all hierarchy/classical/cardinal/Choice parameters
explicit. Full ambient semantic soundness is proved; deriving the same
construction internally in BZC + GCH + hierarchy existence remains open.

## 2026-10-14 — all-rank joint hereditary substitution

Use well-founded induction on the cut bound and structural induction on the
full certificate. Choose common syntactic normal forms under binders before
semantic quantification, so empty domains require no witness or choice.
Lift original typed substitutions into the normalized binder independently
of membership. In the neutral-application branch retain the result-type
child; when the function becomes a lambda, derive its actual body value by
semantic beta and invoke the smaller cut rank proved by neutral-head descent.
The resulting theorem normalizes term AND assigned type while retaining both
actual semantic indices for arbitrary ranks. It compiles without a semantic
conversion premise. Certificate totality and agreement with unrestricted
original semantics are still required to obtain original model soundness.

## 2026-10-14 — structural rank certificates and general cut bounds

Use an inductive certificate indexed by both the normal ORIGINAL term and
its normal assigned type, and by both actual semantic values. All semantic
formation/body witnesses are recursive certificates; the neutral application
constructor also retains its normalized result-type certificate. Retain
original binder typing and normality when semantic domains may be empty.
Do not assume certificate totality or replace the original target with it.

Bound the source declaration ranks only for NONVARIABLE substitution images.
This allows lifting under arbitrarily ranked binders. Neutral-spine typing
then proves that every newly exposed lambda has actual domain rank strictly
below the cut bound. The rank-zero simultaneous substitution theorem and
normalized-binder extension compile; general higher-rank hereditary
substitution is still an obligation. A head that stays neutral may have
function rank above the cut bound: use its result-type certificate child.

For root beta with a normal nonlambda argument, derive local body membership
and ranks from certificate children, then preserve the arbitrary canonical
redex value by coherence. Do not generalize this result to lambda arguments
or unrestricted original denotations without the missing proofs.
Validity transport uses actual same-value paired declaration witnesses,
not a constructor asserting the desired validity implication.

## 2026-10-14 — material BZC axioms are not internal model derivations

Define the first-order BZC axioms independently of Ens and PTS semantics.
Include actual von Neumann Infinity and Foundation. The Choice formula has
a graph/no-junk clause and is equivalent to existing ordinary family_choice.
Prove Ens satisfaction and the resulting independent logical soundness with
classical logic and Choice explicit. This does NOT justify constructing
the PTS model inside BZC: the required implication is in the other direction.
The GCH/hierarchy theory and bounded definability of arbitrary denotation
predicates remain open. Follow the user's order: this SAME model first with
the hierarchy-existence assumption, then investigate eliminating it.

## 2026-10-14 — canonical substitution, context transport and ranked root steps

Preserve beta-normal implicit witnesses under substitutions whose images
are normal and not lambdas. This is proved for arbitrary substitutions,
not a finite test suite. In the original PTS a term with type of rank zero
cannot be a lambda: every product type has positive rank. Consequently
normal rank-zero arguments give a genuine semantic substitution base case,
with identical denotation values and unchanged annotations.

For an arbitrary canonical redex denotation with normal original domain,
align its application and lambda witnesses using original typing uniqueness
and normal-form uniqueness. Derive actual product-domain rank descent from
the aligned typing, never from the result term's rank. Root reduction into
canonical denotation additionally requires the proved substitution case;
the general matching root lemma only concludes ORIGINAL denotation.
Local canonical realizations supply actual-witness membership/rank by
unconditional coherence, without an extra semantic-conversion premise.
These local premises and normality restrictions remain explicit. They do
not establish the unrestricted fundamental theorem.

CanonicalApplication removes the old application's explicit coherence
premises using canonical coherence, while retaining the genuine normal
product/normal nonlambda argument restrictions. CanonicalHereditary proves
the rank-one application branch via the actual rank-zero domain. Its normal
lambda case has normal reduct AND normal substituted codomain, with the
same semantic value and original typings. This does not establish the
rank-one SUBSTITUTION case, whose lambda images can expose nested redexes.

Canonical context transport uses original context typing morphisms. Terms,
annotations and normal witnesses are unchanged; no semantic conversion is
needed. It does NOT imply validity transports between converted contexts:
validity additionally compares the semantics of the declaration terms.

Higher-rank hereditary substitution must normalize substituted implicit
witnesses while preserving their values and joint rank/membership evidence.
Raw substitution closure cannot be asserted for lambda images. An NF-based
relation with automatic conversion invariance would still require totality,
compositionality and agreement with the actual model; defining that relation
alone would not solve this obligation.

## 2026-10-14 — independent material language and bounded separation

MaterialSetTheory defines pure first-order membership/equality syntax and
an independent classical natural-deduction system. No deduction constructor
mentions Ens semantics or PTS soundness. Its general logical soundness
theorem explicitly requires satisfaction of the syntactic theory. Embed
the existing bounded formula language with actual membership guards and
state the bounded-separation schema with a fresh output-set variable.

Ens satisfaction of THIS schema is proved using Comp with the predicate
of the actual bounded formula, including its extensionality proof. Thus
the specialized logical soundness theorem discharges theory satisfaction;
classical logic remains an explicit parameter. This is not a definition
of all BZC/GCH/hierarchy axioms, not satisfaction of those axioms, and not
an interpretation of the Ens representation in a weak first-order theory.
Arbitrary Rocq predicates in other uses of Comp remain unaudited until
their bounded defining formulas or eliminations are actually supplied.

## 2026-10-14 — canonical implicit witnesses, not erased annotations

Investigate an auxiliary denotation using beta-normal inferred body types
and application product types. These are type witnesses, NOT new or erased
source-term annotations. Keep the original term/context and the exact same
H, selector and semantic operations. Original typing uniqueness and
Church--Rosser identify normal witnesses syntactically. This permits a
coherence induction on denotation itself, including its genuinely
infinitely branching premises, without a finite-height argument.

CanonicalTypeWitnesses proves existence of the required normal typing
witnesses using original strong normalization and preservation. A direct
normal-or-step proof makes normal-form existence constructive. Lambda
domain annotations remain literally unchanged; only inferred typing
results are normalized. This is syntactic evidence, not a proof that
normalizing a type preserves its decoded denotation.

The auxiliary relation is NOT a replacement target. Its inclusion into
original denotes must preserve the same value. Totality, beta/type
conversion and equivalence with unrestricted denotation remain open.
In particular substitution can create redexes in a normal type, so do not
assert closure under substitution or bootstrap full soundness from
coherence alone. Native typed equality also still needs its own completeness
and semantic proof; these independent prerequisites do not justify each
other circularly.

Possible continuation, NOT PROVED: joint membership and semantic hereditary
substitution for normal terms/type witnesses, following the cut-rank
ordering used by the original Ranks.SL/AL proofs. Newly exposed applications
suggest a smaller domain cut rank. The decreasing measure, all dependent
cases and the semantic theorem must actually be supplied; the syntactic
reference is not itself a semantic proof or a termination assumption.

## 2026-10-14 — native weakening without assuming endpoint regularity

Use an inductive order-preserving context embedding: empty, insert a
natively typed target declaration, or lift both contexts through the same
renamed source declaration. The lift rule needs no typing premise. Prove
preservation of wf/typ/equal mutually; source wf supplies the formation
proof precisely when needed. This avoids hiding native equality endpoint
regularity inside a renaming contract. Context lookup compatibility and
ordinary typing/equality weakening are derived, not assumed. Native
substitution, endpoint regularity and reverse completeness remain open.

## 2026-10-14 — bounded countable selection in actual classification

Use BoundedRecursion to define prefixes by S -> S union {c(X minus S)},
with complement, application and adjoining expressed by bounded formulas.
Project the prefix through the same selector. Prove agreement with the
old chosen sequence, and prove injection directly from the bounded graph.
Route bounded_cardinal_code through the new dichotomy; do not merely add
an unused replacement theorem. The old native sequence remains a reference
for correctness, not the graph used by the new infinite embedding.
Finite-prefix numerical induction and Ens themselves still need a
first-order foundation audit.

## 2026-10-14 — bounds for global data are allowed above H

Retain the actual graph bound in the set-indexed Choice existence proof.
An arbitrary subset_choice X s contract does not constrain garbage edges
of s, so never infer that bound from the contract alone. The existence
theorem chooses a bounded selector and preserves all original witness
values. Decoder edges belong to H by envelope pairing closure, so the
decoder belongs to Power H. Global selector/selection bounds use further
powersets and Cartesian products over H; no unproved membership in H is
asserted. This matches a set-sized structure assembled USING the supplied
hierarchy, rather than incorrectly forcing the whole structure inside it.

## 2026-10-14 — native typed equality as an open conversion prerequisite

The conversion -> realization/coherence -> root-beta route is circular.
Neither raw-term SN nor an unproved finite height of denotes fixes it:
implicit type witnesses can exceed term size, dependent denotation branches
can have no uniform finite witness bound, and substitution can increase
derivation size. The general difficulty and a typed-equality route are
documented by [Siles--Herbelin](https://pauillac.inria.fr/~herbelin/articles/lics-SilHer10-pts-typed-conv.pdf).
The [archived Coq development](https://florisvandoorn.com/ptsf/index.html)
is a reference, NOT an imported theorem or trusted assumption.

Implement only a native mutual typed-equality certificate over existing
Term nat n, with original annotation-preserving projections proved. Do not
silently import an annotation-erasure bridge, change the target calculus,
or assume original-to-certificate completeness. That reverse direction and
the semantic coherence/interpretation theorem still have to be proved.
Projection/reflexivity alone does not break the semantic circularity.

## 2026-10-14 — combine decoder branches with input classification

Before combining branches, prove each application's input is equal to the
appropriate finite/infinite/sort code, with the corresponding exact output.
Use bounded application disjunction over the three already bounded graphs,
separated from Prod omega_codes H. Prove omega_codes equals all_codes and
the complete graph equals the original all_decoding_graph. Preserve the
original decoder and selectors, using equality to justify bounded versions;
do not substitute a new model. The given hierarchy premises are explicit.
This closes the decoder-graph representation gap, not semantic conversion
or derivability of the ambient Ens constructions in first-order BZC.

BoundedDecodedSelection now replaces the code-domain/decoding parameters
by omega_codes/bounded_decoder in the bounded selection graph. Formula
extensionality proves the witness fibers and source domain unchanged.
The selected value is proved equal for the SAME s; ordinary family_choice
still supplies such an s. All typed product sources are covered uniformly.
The old definitions are preserved and related by proved equality, not
silently changed. Fresh build, recursive kernel audit and 147-stage local
CI passed; these are Ens proofs, not first-order BZC soundness certificates.

## 2026-10-14 — exact bounded universe graph and sort decoding

Express universe membership by bounding only the infinite-code indices.
Prove all singleton numerals have an actual Code representative; for each
infinite tag test its recovered index against numeral n or finite_carrier n.
This yields exactly U n, retaining all finite and sort codes. Define the
universe graph by bounded separation, then decode 3*n+2 by two singleton
inversions and bounded tripling. Prove agreement with existing decode for
all sort indices. These are individual branches; their union still needs
off-branch exclusion and full decoder agreement. Semantic conversion and
first-order BZC certification remain unproved. Commit/push is now explicitly
authorized; publish a truthful checkpoint without describing soundness as done.

## 2026-10-14 — infinite decoder uses actual successor tags

Recover the index of repr(infinite n) by one singleton inversion followed
by the uniform tripling graph. Compose with bounded_carrier_graph under
the same supplied hierarchy premises. Prove application, evaluation and
agreement with existing decode for every infinite code. This establishes
the second branch; sort universes and branch combination are still needed
before any claim of a complete bounded decoder. Full soundness remains open.

## 2026-10-14 — uniform code tripling and finite decoding

Generalize bounded iteration to an arbitrary supplied step graph with a
bounded reference family, proved step behavior and uniqueness. Correctness
uses finite separators, not a native graph of the family. Instantiate with
the bounded triple-singleton step on omega_codes; native arithmetic is used
only to verify its uniform numeral(3*n) equation. Combine tripling with the
finite-carrier graph by bounded existential quantification over omega_codes.
The resulting finite decoder handles all indices and the actual 3*n tags.
Do not identify it with the complete decoder: infinite/sort branches and
first-order justification of the Ens framework remain separate obligations.

## 2026-10-14 — certify the existing global coding-witness selector

Specialize bounded formula selection to codeWitnessF and prove its fiber
equals code_witnesses. Define the admissible source domain by bounded
existence of a witness inside the already supplied Cartesian bound. The
resulting graph agrees pointwise with apply_set s (global_code_witnesses H A)
for the SAME s. Prove every typed product's dependent function space is
in that domain under the original cardinal/hierarchy premises. This avoids
changing rank-independent choices and gives the actual model a bounded
graph representation for selection. It does not certify the still-native
decoder or establish semantic conversion/first-order BZC soundness.

## 2026-10-14 — a formula-defined selected graph

For a bounded formula p(x,y), bound its candidate fiber by Power B and
characterize that fiber with the two inclusions. Combine this with the
bounded applyValueF certificate for a selector c. This yields an actual
selection graph by bounded_formula_graph, with function membership and
selection correctness under ordinary set-indexed Choice. Do not extend
the claim to arbitrary semantic predicates: their own bounded definitions
are not supplied by this generic theorem. Denotation coherence/conversion
and first-order BZC proof-system interpretation remain independent gaps.

## 2026-10-14 — choose on a fixed powerset instead of collecting candidates

Refactor bounded_relation_choice through a selector on nonempty subsets
of B. Every candidate set is already a subset of B, so no native
family_range of candidate sets is needed for this use of Choice. The
generic choose_extensional_family theorem remains unchanged elsewhere;
do not infer its arbitrary native-family collection is BZC-justified.
The selected graph still uses native graph, and arbitrary P still needs
its formula specialization to justify candidate separation. This change
narrows an actual dependency of denotation/paired witness selection but
does not complete the first-order foundation or semantic-conversion proof.

## 2026-10-14 — remove native infinite comparison from carrier correctness

Replace carrier_relation in the certificate's correctness proof by a
finite separator built inductively by bounded formula separation. At
index zero restrict the initial value; at each successor retain previous
restrictions and restrict the new value. Prove every separator is closed
under the same successor/powerset operation and forces the correct value
at its index. The proof needs no set of all separators and no native
infinite comparison graph. Keep the earlier comparison lemmas as legacy
facts, but do not use them in carrier_iteration_certificate_correct.
This removes that particular audit concern; it is not a derivation of
the entire Ens construction in first-order BZC or full model soundness.

## 2026-10-14 — uniform carrier graph as least closed relation

Use the least relation containing (zero,omega_codes) and closed under
singleton successor and the certified powerset graph. Candidate relations
are bounded by Power(Prod omega_codes H), so the defining formula has no
unbounded quantifiers. Separation constructs bounded_carrier_graph and
its evaluation is proved equal to carrier n for every numeral. Native
carrier_relation (a sup) is used only as a comparison in the correctness
proof, not as the defined graph. This still leaves a first-order proof
audit: replacing a definition does not automatically eliminate the strength
of auxiliary objects in its proof. No full BZC or soundness claim follows.

## 2026-10-14 — bounded powerset graph using the supplied hierarchy

A bounded powerset formula must carry a bound containing ALL subsets of
its argument; quantifying over an arbitrary ambient set is insufficient.
Prove that adequacy explicitly, then use bounded_formula_graph on Prod W W
for transitive powerset-closed W. Instantiate with the existing supplied
envelope H using envelope_transitive/envelope_power_closed, rather than
adding a new closure premise to the model. The graph evaluates to the
next actual carrier at every index. This certifies the hierarchy's step
operation, not a set-coded recursion collecting all indexed values, and
not the first-order BZC status of Ens or the complete soundness theorem.

## 2026-10-14 — derive arbitrary-denotation regularity from the same conversion premise

Extend RealizationInduction with structural coherence for every typed term,
then membership of every denotation in every denotation of its type, and
universe membership for sort-typed terms. Application coherence transports
codomain typing to the common binder context using original typing
uniqueness/product inversion. All results retain the existing explicit
typed decoded conversion premise; no universal coherence/rank assumptions
are introduced. These are conditional consequences, not a proof of that
premise. In particular they cannot be used circularly to discharge it.
The paper's assertion that the rules are respected supplies no missing
well-founded semantic conversion argument. Full soundness and the BZC
foundation audit remain open.

## 2026-10-14 — assemble realization induction without assuming semantic regularity

RegularTyping is a syntactic induction certificate carrying redundant
type-formation subderivations for lambda, application and conversion.
Proved renaming, substitution, regularity, original-typing embedding and
erasure, and equivalence on original well-formed contexts. No PTS rules
were changed and no semantic assumptions enter the equivalence proof.
This supplies the previously missing induction hypotheses for domain and
codomain realizations. RealizationInduction now proves realization for
ALL original typings under the explicit typed-decoded-conversion premise
and the existing set-construction premises. It assumes no universal rank
bound or component realization beyond what the induction proves.
The conversion premise is not declared as an axiom or hidden in a model
record: it is printed in the theorem type and remains an unproved target.
This is NOT unconditional soundness. Do not use its closed Print Assumptions
report to claim either that premise or first-order BZC derivability.

Before the user's soundness refocus, BoundedFiniteCarriers was completed:
finite_carrier n is the least transitive set containing numeral n as a
subset. A bounded formula quantifies over Power omega_codes; separation
constructs a uniform graph with verified evaluation at every numeral.
It does not yet implement the finite-code tag 3*n or other decoder branches.

## 2026-10-14 — formula-defined function graphs without a Choice premise

Use separation on Prod A B rather than graph A f (whose implementation is
sup-indexed) to construct a graph from a bounded formula p(x,y). Add and
verify general bounded-formula renaming so p is embedded in the edge
certificate without arbitrary Prop atoms. Prove its exact application law,
agreement with graph A f for bounded extensional f, and function membership
and evaluation from totality/uniqueness of p. No family_choice or selected
Ens->Ens function is required. This discharges a generic construction step,
not the bounded definition of the decoder, hierarchy recursion, or the
first-order interpretation of Ens/Prod. Full semantic soundness remains open.

## 2026-10-14 — certify the actual union-of-fiber application

BoundedApplication.applyValueF expresses both inclusions between a proposed
value and the union of the graph's value fiber, using only bounded Formula
constructors. Its correctness does not assume functionality or totality;
the triple-union value_bound supplies a bound for any graph. The original
value_fiber separation is proved equal to separation by applicationF, and
apply_set to the union of that formula-defined fiber. Decoding equality
then has a bounded certificate using the existing decoding graph and its
proved Power(carrier i) value bound. Do not infer bounded first-order graph
existence from this certificate: graph construction, recursion and the
Ens encoding still require the foundation audit. This does not discharge
the open semantic-conversion/fundamental theorem obligations.

## 2026-10-14 — remove redundant beta product-witness premises

Proved lambda_product_body without semantic premises: lambda/product
inversion, original type correctness, and binder typing transport show
that any assigned product's codomain types the lambda body in its annotated
context. Use this in realized_root_beta to transport both fiber denotations
to that context and invoke the existing body-type conversion obligation.
Application domain comparison factors through a denotation of the annotated
domain supplied by its realization. Thus the separate PA/PB premises were
removed, with CA reformulated as conversion of typed domains to the actual
annotation. CA/CB and constituent realization/coherence remain unproved
general facts; this refinement is not a replacement for their joint proof.

Also proved realization transport along context typing morphisms and
well-formed context conversion, and under pointwise set-equal valuations.
These use already proved denotation transport and retain the same value
and type code. They do not imply validity transport when declarations
change: that requires semantic comparison of the declarations, still open.

## 2026-10-14 — arbitrary beta values via derived coherence

RootBeta.realized_root_beta combines the selected shared beta witness with
lambda and application coherence. Lambda coherence needs equality of
decoded domains, not equality of domain codes; generalized its premise
accordingly. Body/argument coherence and local conversion of actual typing
witnesses derive redex coherence, rather than assuming it. Set equality
then transports reduct denotation and result-type membership to any given
redex value. The result type code remains in U k. Universal rank and
membership premises for arbitrary denotations are absent from this route.
The constituent realization/coherence/conversion obligations remain open;
this is not the joint fundamental theorem or a first-order BZC proof.

## 2026-10-14 — construct a shared beta value from realizations

DenotationBeta.realized_beta selects the domain code from its sort
realization and jointly selects ranked body/type witnesses over that
domain. Decoded domain coherence transports argument membership; decoded
codomain coherence supplies ranked pairs from ordinary realizations.
The checked matching-witness beta law and original substitution then give
one value for both redex and reduct, in the actual substituted result type,
whose code lies in U k. No universal rank bound on arbitrary denotations
or assumed redex-coherence premise is used. Realization/coherence of the
constituents still need the joint fundamental proof; this existence result
does not prove arbitrary-denotation preservation by itself.

## 2026-10-14 — ranked witnesses from realizations, not universal rank premises

For lambda, combine a body realization with a realization of its type at
the required sort. Choose the latter's already ranked code and transport
body membership using equality of decoded sets. No code equality or
assertion that every denotation is ranked is needed for this construction.
For application, select a ranked domain/fiber family from their type
realizations, then transport the function's membership to that product.
Generalize product coherence to decoded component equality, which already
suffices for semantic_product_congruence. This removes universal rank
premises from the new application_realization_from_induction theorem.
The required type realizations and decoded coherence remain actual
fundamental-proof obligations; no final soundness theorem is claimed.

## 2026-10-14 — extract arbitrary root-beta witnesses

RootBeta.denotes_root_beta inverts an arbitrary redex denotation and its
function's lambda denotation. Derive the product-witness equalities using
original lambda typing and typing uniqueness, not semantic assumptions.
Original type correctness supplies domain/codomain sorts. Transport both
typing and denotation of the application codomain into the lambda's binder
context before using the local semantic conversion premise. This avoids
requiring conversion for untyped terms or mismatched contexts.
The remaining local domain/codomain conversion, rank bounds, body membership
and argument membership are still obligations of the joint fundamental
proof. They are not added to the model as axioms, nor is a global beta or
soundness contract assumed. This theorem is the root constructor step,
not final unrestricted reduction preservation.

## 2026-10-14 — unconditional type-head normalization

Use the original SN/SNx/WHR_SN machinery to obtain a head form; do not
assume a semantic normalization contract. Original typing rules exclude
sort/product-headed applications and exclude a lambda at a sort type.
Thus well-typed types reduce to sorts, products or variable-headed spines.
Confluence, preservation and typing uniqueness then give a common such
head and equal sort ranks for two convertible well-typed types.
This is only head classification: annotations, product bodies and neutral
arguments need not be fully normal. It does not itself transport denotation
or discharge the joint semantic conversion/rank invariant.

## 2026-10-14 — application coherence transports the binder context

For two application denotations, use original uniqueness_of_typing on the
two product types of the same function, followed by product injectivity.
Derive domain well-typedness from original type correctness and product
inversion; no extra domain-typing contract is needed. The proved binder
context conversion transports the second fiber denotation into the first
context. Semantic application congruence then reduces equality to subterm
coherence and decoded conversion of those particular domains and fibers.
The latter remain local proof obligations, not axioms or a completed
semantic conversion theorem. Do not infer equal decoded fibers merely from
equality of product codes: coding can identify equipotent sets.

## 2026-10-14 — compare lambda result witnesses by original typing uniqueness

DenotationInversion.denotes_lambda_coherence uses original
uniqueness_of_typing to relate the two body-result types. Domain and body
coherence are restricted to the lambda's actual subterms and binder-domain
extensions. The remaining conversion premise concerns only decoded values
of the two body-result types, not equality of the lambda being proved.
Semantic lambda congruence then discharges the constructor case. This is an
induction-step lemma, not a global coherence or soundness theorem; the
conversion premise must still be established in the fundamental proof.
The existing product-coherence lemma now likewise restricts its fiber
coherence premise to members of an actually denoted domain. No caller
depended on the unnecessarily stronger arbitrary-valuation version.

## 2026-10-14 — beta across different product witnesses

Use semantic application congruence before the coded beta law, allowing
the application and lambda witnesses to differ when their decoded domains
and fibers agree. Derive argument typing at the lambda annotation directly
from original redex typing using app/lambda inversion, product injectivity
and typ_conv. Then apply the proved original-syntax substitution theorem.
Do not silently assume the equalities or membership/rank facts: they remain
visible premises of denotes_beta_across_products and obligations of the
future general soundness proof. No global beta/coherence axiom is added.

## 2026-10-14 — lift preservation through original constructors

Prove the six compatible reduction cases directly by denotation inversion,
keeping semantic values/families unchanged and transporting original typing
witnesses with subject/context reduction. Root beta remains separate: do not
add it as an assumed contract and claim a final preservation theorem.
Lambda/application inversion includes EQ closure. Local Opaque for semantic
operations prevents expensive dependent-inversion unfolding only; all
definitions and kernel/guard/universe checking remain intact. Explicit
conjunction splits avoid accidentally descending into set equality proofs.
Binder-body induction hypotheses are restricted to extensions by elements
of an actually denoted domain. Requiring preservation at every valuation
would be too strong for the intended valid-context induction.

## 2026-10-14 — context conversion from original variable typings

Transport denotation with identity simultaneous substitution, once original
variable typings transport. Define structural context convertibility using
only original beta equivalence of corresponding declarations. Prove the
required variable typings from source well-formedness by induction, using
original typ_conv and weakening; then transport denotation both ways when
both contexts are well formed. This is a proved syntactic context-conversion
principle, not an assumed semantic conversion contract. In particular,
context denotation transport does not prove term conversion or transport
valid_valuation across beta-equivalent declarations by itself.

## 2026-10-14 — recover the function's actual product witness

Invert the denotation of the original product syntax, including its EQ
closure, to recover its domain and fiber family. Application must reuse
that family, not choose an independent product witness. Transport function
membership through product equality and argument membership through domain
coherence, then invoke original-syntax substitution for the result type.
The local coherence/rank premises remain unproved induction obligations;
application_realization_from_inversion is not the final soundness theorem.
Product coherence is proved from its two subterm-coherence hypotheses, not
asserted globally. No PTS rule, syntax, conversion or annotation is changed.

## 2026-10-14 — joint selection preserves body/type compatibility

Do not select a body's type code independently from its value and then
assume they are compatible. Select pairs in the explicit Cartesian bound
Prod (U k) (carrier k), using the existing relational-choice theorem. Prove
projection typing and extensionality and preserve the joint predicate
denotes B c /\ denotes t v /\ IN v (decode c). This removes the preselected
codomain-family premise of lambda realization. Pointwise ranked body
witnesses remain a lower-level induction obligation, not an axiom or a
replacement for the final original-typing theorem. This native selection
still requires a first-order bounded predicate certificate.

## 2026-10-14 — bounded witness selection, no class-choice shortcut

Prove extensionality of holds for every syntactically bounded Formula.
Select relational witnesses from Comp B (P x), using a set-indexed family
and ordinary family_choice. The resulting family is apply_set of a set graph
and is EQ-extensional; no meta-level or global choice axiom is added.
Distinguish the general native relational lemma from bounded_formula_choice:
only the latter certifies the candidate predicate as a bounded formula.

For denotation, prove the relation extensional in its binder valuation and
result. Select codomain codes in U k and body values in carrier k. This
discharges product family assembly from the two actual semantic induction
hypotheses in valid contexts. Lambda body assembly still presupposes a
compatible codomain family; proving such compatibility is not replaced by
a premise of a claimed final soundness theorem. Comp of native denotation
is NOT yet certified bounded: its first-order translation remains open.

## 2026-10-14 — structural context validity, explicit rule composition

Define valid_valuation by recursion on context declarations. Each extension
requires a denotation of its declared type and membership of the new value;
it does not quantify over all well-typed terms or assume their soundness.
Prove lookup via denotation weakening and valuation extensionality. Define
realizes as existence of term/type denotations with membership, then prove
sort/variable realization and composition for product/lambda/application.
Application must interpret the original substituted codomain using the
proved denotes_subst, not replace it by an unconnected semantic codomain.

Keep family existence and witness coherence explicit as unsolved induction
obligations. The equality-transport lemma only takes actual set equality;
it is not named or reported as a proof of syntactic conversion. The native
context relation remains subject to the first-order bounded-foundation audit.

## 2026-10-14 — relational denotation and original-syntax substitution

Use a type-directed inductive denotation over unchanged Term nat n. Lambda
and application constructors carry original Typing.typ witnesses to supply
their product type; they are not new typing rules or added annotations.
Do not build semantic membership into the denotation relation as a way of
assuming typing soundness. Prove valuation extensionality, renaming and
simultaneous substitution by induction on denotation. Transport the typing
witnesses with proved original-typing renaming/substitution lemmas.

Single-variable substitution then connects the semantic beta operation to
the original syntactic beta redex and reduct, for matching witnesses and
explicit semantic typing premises. This is deliberately named
denotes_matched_beta: it does not imply arbitrary-denotation coherence,
conversion soundness, or totality. Those remain proof obligations, not
record fields or hypotheses of a claimed final soundness theorem. The
native relation is not yet a first-order BZC interpretation certificate.

## 2026-10-14 — typed global operations before syntax interpretation

Inspection of Syntax.v/Typing.v and paper.tex section rk-model confirms that
application has no type annotation, while the coding inverse depends on its
product type. Do not invent a value-only raw-term evaluator or erase lambda
annotations. Define rank-independent typed semantic operations with product
data explicit, then prove typing, beta and semantic congruence for use in a
typed syntax interpretation. Upstream Inversions.uniqueness_of_typing gives
only syntactic beta-equivalence; semantic conversion and substitution must
still be proved, not assumed from that theorem. The original rules and
syntax remain unchanged.

## 2026-10-14 — rank-independent code selection in the supplied hierarchy

Define candidates from the semantic source set alone, using all universe
codes, their decoding graph, and a common Power(Prod H H) graph bound. Choose
once over nonempty subsets of the bounded candidate space. Do not choose
independently at different ranks. Prove rank admissibility afterward: if a
selected infinite code exceeded a source carrier bound, its coding bijection
would contradict strict powerset growth. Global projections then depend only
on the source set and respect EQ. The supplied hierarchy is explicit and
its identification/existence and first-order bounded construction remain
foundation obligations.

## 2026-10-14 — selected-code projections and semantic congruence

Project witnesses with Cartesian graph maps, preserving the pinned library's
pair encoding. Prove projection beta laws, transport graph/codomain equality
of bijections, and specialize coded_beta to the selected witness. Prove
dependent-product congruence for equal domains and pointwise-equal extensional
fibers, then equality of eligible witness sets and selected outputs at fixed
ranks. This does not replace the original syntax's substitution induction
and does not establish cross-rank coherence.

## 2026-10-14 — code-preserving witnesses and fixed-rank uniform choice

Retain (code, bijection) rather than (carrier, bijection), with the decoded
carrier bounded by Power(carrier k) and related through the decoding graph.
Certify the full predicate in Bounded.Formula. Choose from all nonempty
subsets of carrier(13+k), obtaining one set-coded selection operation for
every product at fixed ranks m,n. This avoids a separate meta-level choice
for each product and does not collect arbitrary Ens -> Ens families. Do not
claim cross-rank coherence or substitution compatibility from this theorem.

## 2026-10-14 — nonempty bounded product-witness sets

Use the decoded-carrier range as the target set for eligible_bijections and
prove it equal to the previously certified bounded decoding range. For rank
k=max(m+1,n), put the actual product and target carriers inside carrier(5+k).
Existing graph/witness bounds then put the eligible set in carrier(13+k).
Use decoded_product_code to prove nonemptiness without assuming it. A generic
choice pullback constructs a graph for an extensional set-indexed family.
Choosing a carrier/bijection pair does not yet choose a syntactic universe
code coherently; retain that obligation rather than identifying the two.

## 2026-10-14 — dichotomy from set-indexed family choice

Use choice on the family of nonempty subsets of X, a subset of Power X.
Native recursion chooses outside each finite prefix. If a remainder is empty,
the prefix enumeration constructs a finite bijection; otherwise the choices
construct an injective countable graph. Family choice is an explicit generic
principle, not a product-coding assumption or global axiom. Combine this with
the powerset hierarchy classification to remove the infinitude side condition
from decoded_product_code. First-order bounded recursion/separation audits
and derivation of cardinal principles in BZC+GCH remain open.

## 2026-10-14 — finite-embedding classification by actual graphs

Compress the selected numeral indices by finite induction, then use an
explicit finite enumeration graph to construct a bijection. For a general
injection into a finite carrier, separate its image inside that carrier and
prove the original graph is a bijection onto the image. This derives the
finite-embedding case with excluded middle explicit, not a cardinality
contract. The finite/countable dichotomy remains a separate proof obligation;
new graph/image constructions still need the weak-foundation audit.

## 2026-10-14 — conditional infinite cardinal classification

Use generic set-cardinal principles, not a code/product-coding contract:
comparability of graph embeddings, and the disjunction X <= K or Power K <= X
whenever omega <= K <= X <= Power K. Induct over the finite powerset hierarchy
to classify countably infinite-or-larger bounded sets, and then exhibit an
allowed code. Specialize using the proved dependent-product upper bound.
Keep these principles and classical logic explicit in theorem types. Do not
claim they have been derived in BZC+GCH or that the finite case is covered.
Carrier-index uniqueness needs only the already proved strict growth theorem.

## 2026-10-14 — bounded comparison gluing and successor

Complete the syntactic certificates for the three separation predicates in
CantorBernstein.v. The successor formula existentially quantifies an element
of the supplied region and its image in B, replacing composed application by
two graph relations. The glued graph formula bounds its endpoints by A and B
and expands the ordered-pair predicate. Transport the existing bijection proof
across extensional equality to the formula-separated graph. The final theorem
keeps excluded middle explicit; no global axiom is introduced. Certificates
for these predicates are not a first-order BZC derivation of the model.

## 2026-10-14 — bounded syntax for the comparison region

After checkpoint 5e08a2c, translate the least-region predicate into a scoped
six-variable bounded formula. Quantify over supplied Power A, A and B, and
replace the composed application term by bounded graph relations. Prove
equivalence under the input injection contracts and equality of the separated
sets. This closes the region's syntactic boundedness audit; successor/gluing
certificates and the full BZC interpretation remain outstanding.

## 2026-10-14 — Schroeder--Bernstein without sequence collection

The pinned ZFC subset and installed Stdlib provided no directly reusable
Schroeder--Bernstein theorem for these set graphs. Construct a least closed
region by separation from A, quantifying over Power A. Prove its one-step
decomposition through another bounded candidate subset, then glue f and the
inverse relation of g to obtain the bijection. The final theorem explicitly
takes excluded middle, as appropriate for a classical set-theory development;
no global axiom is added. Formula-syntax certification, GCH classification
and model soundness remain separate unfinished obligations.

## 2026-10-14 — all-rank decoded dependent-product upper bound

Build Cartesian graph maps explicitly, encode pairs of subsets by disjoint
tags, and propagate square absorption through every powerset level. Combine
with flattening and direct images to get the bound max(m+1,n). For actual
decoded fibers, use their established subset bounds to include their function
space in the constant-carrier function space. This avoids requiring chosen
fiber injections. The result is uniform in m,n,a,b, with no GCH/choice premise.
It proves an upper bound for powerset representatives, not that the product
is equinumerous with an available code. GCH classification and coherent coding
remain required for the original PTS soundness theorem.

## 2026-10-14 — derive the countable subset exponent from Cartesian pairing

After commit 34b85de, combine the explicit flattening injection and powerset
image injection with the countable square bijection. This proves the
countable subset-valued exponent bound, plus a generic square-absorption
lemma and a dependent version with supplied fiber injections. No GCH, choice,
or global family of injections is assumed by the nondependent theorem.

## 2026-10-14 — countable Cartesian base as an actual graph bijection

CountablePairing uses Stdlib.Arith.Cantor's checked pairing/inverse to construct
a graph over the library's set-coded numerals and ordered pairs. Prove graph
typing, functionality, injectivity and surjectivity before exporting the
Cartesian-square cardinal estimate. This is the first Cartesian base needed
for the exponent bound, not the all-rank GCH classification.

## 2026-10-14 — bounded bijection and eligible-witness certificates

BoundedBijections proves syntactic boundedness and equivalence with the existing
bijection definition. Include graph-element shape, totality, functionality,
injectivity, and surjectivity explicitly. Construct eligible_bijections by
separation from Prod T F, with bounded quantifiers over target and graph bounds.
Prove the graph bound omits no eligible bijection, and the full witness set
lies in P^8(W). This supplies a concrete set for later choice; do not replace
the missing GCH classification/nonemptiness proof by an assumed model field.

## 2026-10-14 — bound coding witnesses before selecting them

After checkpoint 5f88ec1, derive the graph bound for any supplied bijection
between subsets of a transitive W, then bound the pair (K,f) in P^7(W).
This validates the needed ambient witness bound without assuming existence
of a suitable cardinal code or bijection. Nonemptiness/GCH and coherent
selection remain explicit missing obligations.

## 2026-10-14 — supplied hierarchy characterization and closure

SuppliedHierarchy uses the membership characterization of a supplied union
of finite powerset levels. Derive powerset/transitive closure and membership
of the actual model's code/carrier/graph constructions; do not assume PTS
model closure as a field. No existence or identification with V_{omega+omega}
is claimed. Next bound the coding witnesses before using set choice.
Corrected the preceding handoff's stage/report counts from the raw logs.

## 2026-10-14 — connect concrete code decoding to hierarchy bounds

CodeHierarchyBounds proves the singleton-numeral base is transitive, every
code universe U_i lies inside it, and decoded members of U_i are subsets of
the corresponding powerset carrier. The decoding graph is typed and bounded
at carrier (i+5). This is model-specific progress toward the supplied
V_{omega+omega} realization. It does not turn Ens.sup into BZC collection,
does not prove coherent cardinal coding/GCH, and does not establish PTS
typing soundness. Keep all those obligations explicit.

## 2026-10-14 — bounded reconstruction of dependent function spaces

BoundedProducts defines graph laws with all quantifiers bounded by A, W,
or a supplied P(W). The five-variable first-order formula has no opaque Prop
atoms or function symbols. The ambient P(A x W) bounds all graph arguments;
this is essential for equivalence to the original unrestricted function_laws.
For a supplied family graph f : A -> P(W), prove equality of the reconstructed
space with dependent_product A (apply_set f), not merely pointwise analogy.
No assumption that the desired PTS model exists is introduced. The typing of
f is an explicit input condition whose model-specific witnesses remain to be
constructed. Keep this distinction and the missing cardinal coding visible.

## 2026-10-14 — reconstruct family ranges from set-coded families

BoundedFamilies replaces sup-indexed family_range in a new construction by
bounded separation from Power W, using a syntactic Formula 3 certificate.
The input is a set graph f rather than a meta-level Ens -> Ens family.
Proved equality with family_range A (apply_set f) for f : A -> Power W,
as well as range and union bounds. This supplied typing premise is a normal
input contract, not evidence that the model's required family graphs exist.
Nor does it certify function_laws itself as bounded. Those are the next
reconstruction obligations; do not claim full BZC soundness from this lemma.

## 2026-10-14 — explicit rank bounds for the existing graph representation

HierarchyBounds uses transitive ambient sets and ordinary powerset iteration,
without assuming closure of a PTS model. The library's ordered pair has an
extra nesting level: bound it in P^3(W), graphs in P^4(W), and the dependent
function space in P^5(W). Indexed family ranges are in P^2(W) when all
fibers are subsets of W. Prove the uniform n+5 estimate, not just samples.
These results bound the existing sup/Comp constructions but do not license
their use in BZC. The next reconstruction must replace indexed constructors
by bounded definitions for set-coded families; an arbitrary Ens -> Ens
parameter is not itself a first-order set-theoretic function graph.
No hierarchy-existence theorem, model closure axiom or soundness hypothesis
was introduced. The immediate target remains the supplied-hierarchy model.

## 2026-10-14 — hierarchy-bounded model first; interpretation afterward

User corrects the foundation goal and sequencing. Reformulate the existing
model in BZC + GCH + existence of V_{omega+omega}, complete its construction
and soundness, and only then seek the stronger interpretation in BZC + GCH.
This supersedes the interpretation-first/two-independent-target wording below.
Use the supplied hierarchy to bound constructions and eliminate stronger
collection/separation uses wherever possible. Any remaining separation must
be explicitly bounded; hierarchy existence alone is not subset comprehension.
The bounded inverse certificate remains useful but is not the main theorem.
No proof claim, PTS rule, or source theorem is changed by this correction.

## 2026-10-14 — bounded syntax certificate for graph inversion

The previous goal-registration turn was progress: it recorded the weaker
targets and an actionable strength audit. This continuation implements the
first certificate rather than merely repeating that audit. BoundedFormulas
has only scoped equality/membership atoms and bounded quantifiers; no opaque
Prop predicates, function symbols or unbounded quantification are admitted
into the syntax. Ordered-pair auxiliaries are bounded inside the pair itself,
matching the pinned library's {{x},{empty,{y}}} representation.

BoundedInverse proves the four-parameter bounded separation formula produces
the same graph as the existing inverse. Ambient Cartesian membership bounds
the witnesses of reverse_edge. This is a semantic equivalence in Ens and a
syntactic boundedness result, not yet a formal BZC derivation or a translation
of all existing Ens constructions into BZC. All nine new audits are closed.
No original PTS rule or goal changed; the overall goal remains active.

## 2026-10-14 — preferred weaker foundation: BZC + GCH

User adds an explicit goal: if possible, obtain an interpretation in Bounded
Zermelo with Choice + GCH, and hence a set-sized model after adding existence
of V_{omega+omega}. “GHZ” is provisionally read as GCH; confirm if corrected.
Track interpretation and set-model realization as distinct unproved claims.
The new goal does not permit assuming model laws or changing the PTS.

ZFC_model/FOUNDATIONS.md records the necessary audit. In particular, closed
Rocq assumption reports for Ens are not proofs of first-order BZC strength.
Arbitrary sup-indexed families, unrestricted Comp predicates, hierarchy
collection and bijection selection must be justified by bounded constructions.
Do not equate external fixed-rank proofs with a uniform internal interpretation.
Preserve existing results; feasibility remains to be determined. No stronger
foundation is to be used silently if the preferred target cannot be obtained.

## 2026-10-14 — powerset images and subset-function exponent step

PowersetEmbedding.v constructs direct images via the existing apply_set.
Set-level extensionality and injection of the original map prove that its
image map on powersets is injective. SubsetFunctions.v constructs the
membership-pair relation of a subset-valued function by separation from
Prod A B. Recovery of every fiber proves the encoding injective. This
gives the concrete exponent step (P(B))^A -> P(A x B), without GCH or choice.
Combining with the earlier fiberwise map gives the corresponding dependent
product bound for supplied fiber injections into P(B).

Do not call this rank-indexed product closure: Cartesian-product estimates,
coherent selection of fiber injections and GCH exact cardinal classification
remain unproved. No model law or cardinal bound is added as an axiom.
All twelve new Print Assumptions reports are closed.

## 2026-10-14 — constructive Cantor theorem and concrete all-rank decoding bound

CardinalGrowth.v proves diagonal non-surjectivity for any extensional map,
then rules out injections Power A -> A using the previously constructed
inverse relation on its image. This needs neither excluded middle nor
choice. Singleton graphs give forward injections, and graph composition
gives transitivity. Every finite powerset iteration strictly increases size.

CardinalHierarchy.v instantiates the arbitrary infinite carriers with the
iterated powersets of omega_codes. Exact code membership and the counting
bijections prove the decoding-size bound uniformly at every rank, with no
carrier assumptions. This removes a real parameter from the construction,
but does not identify powerset iterates with alephs or prove exact product
closure. The GCH classification and exponent bound, coherent cardinal coding
and PTS interpretation remain required; this is not an alternative model
silently dropping those obligations. All fourteen new audits are closed.

## 2026-10-14 — explicit counting bijections and rank-zero carrier bound

CountableCodes.v replaces reliance on a possibly repeating enumeration with
an actual graph bijection U_i -> omega_codes. Number infinite j by j (j<=i),
finite n by i+1+2n, and sort j by i+2+2j. Elementary arithmetic proves this
numbering bijective on the permitted codes. The graph's function laws,
Cartesian bound, injectivity and surjectivity are checked, not assumed.
Existing inverse constructions give a checked round trip. No choice needed.

omega_codes consists of singleton numerals, not von Neumann ordinals.
It is a concrete countably infinite representative. Fixing the rank-zero
infinite carrier to omega_codes proves the decoding bound for all codes
in U_0: finite carriers inject directly, sort carriers use the counting
bijections, and the sole permitted infinite carrier is omega_codes itself.
Higher carriers remain explicit arbitrary parameters; do not claim the
all-rank bound, initial-ordinal hierarchy or GCH product closure from this
base result. All ten new audited theorems are closed.

## 2026-10-14 — dependent-product injection, not assumed cardinal closure

ProductEmbedding.v defines set injections by actual function-set membership
and relational injectivity. Given an extensional family of fiber injections
B(x) -> K, construct the map g |-> (x |-> enc(x)(g(x))) as a set graph.
Prove its typing and injectivity using graph/application extensionality.
When enc is itself supplied as a set graph, application extensionality
discharges the family-extensionality obligation without a new hypothesis.

This is the constructive first inequality of the paper's cardinal argument,
not a renamed premise asserting the dependent-product bound. It still
requires actual fiber injections; their coherent selection and the aleph/GCH
exponent bound are separate unproved obligations. No PTS model-law record or
new axiom has been introduced. All seven new audits are closed.

## 2026-10-14 — concrete inverses and local coded-function laws

SetBijections.v defines a bijection as a member of the actual function set
with relational injectivity and surjectivity. Construct its inverse by
separation from Prod B A, not by choosing inverse values. Prove inverse
typing/bijectivity, both evaluation round trips, and graph composition.
Equinumerosity is an existential over these concrete set graphs; reflexivity,
symmetry and transitivity are proved. No choice or functional extensionality
axiom is introduced. The Cartesian bound is essential when recognizing a
function graph: function laws alone do not exclude non-pair junk elements.

CodedFunctions.v combines those constructions with the dependent-function
graphs. For a supplied ordinary bijection from the dependent product to K,
prove typed encoding/decoding/application and beta, and transport empty-fiber
emptiness to K. This factors out a genuine lemma used by the manuscript;
it is explicitly NOT a soundness theorem with missing model laws moved
into hypotheses. The remaining existence/coherence of cardinal bijections,
aleph/GCH construction and original-typing interpretation remain outstanding.
All fifteen new audited theorems are closed under the global context.

## 2026-10-14 — constructed code universes, parametric infinite carriers

CodeUniverses.v constructs disjoint finite/infinite/sort codes as tagged
singleton numerals in the existing Ens universe. U_i is a subset-indexed
supremum over the codes permitted at level i. Explicit enumeration by nat
proves countability; exact membership proves monotonicity and strict growth.
No countability or code distinctness is an assumed model field.

Extensional decoding is the union of the set of values indexed by codes
whose representations equal the argument. This avoids arbitrary-set equality
decisions and choice. Code injectivity proves the decoding equations. Finite
carriers are bounded-nat-indexed sets of distinct numerals (not asserted to
be von Neumann ordinals); sorts decode to the constructed U_j. An explicit
parameter nat -> Ens supplies the infinite carriers, with NO assumed aleph,
GCH, product-closure or soundness properties. It must later be instantiated
with a genuine hierarchy; the parameter is not a substitute for that proof.

The sort axiom and ordinary decoded-product emptiness now follow from the
construction. The latter still does not establish semantic or syntactic PTS
Bottom nontriviality: the product code and typing interpretation are absent.
All ten new Print Assumptions checks are closed. CI adds the module as a
separate stage and preserves all older stages.

## 2026-10-14 — concrete set application, not assumed model soundness

The latest user explicitly requests finishing the set model, superseding the
old scope exclusion. Inspection found only SetFunctions.v, not a latent
interpreter or pending final soundness lemma. Keep the paper's ZF+GCH
qualification; do not turn the missing cardinal arithmetic, code universes
or coherent coding bijections into assumed model-record fields.

SetApplication.v defines application of ordinary set graphs constructively:
separate the value fiber from Union^3 g and take its union. Three unions are
needed because this ZFC library uses {{x},{empty,{y}}} as its ordered pair.
Prove the fiber characterization and extensionality, graph beta, dependent
application typing/specification, graph reconstruction and function
extensionality. All six audited theorems are closed under the global context.
This avoids choice merely to implement graph evaluation, but does not remove
the manuscript's need for choice/GCH in its cardinal-coding construction.
Graph reconstruction is a set equality, not a new PTS eta-conversion rule.
Add a CI stage for the new module without removing or relaxing existing stages.

Full PTS soundness remains unproved. The next construction is the actual
countable code universes with decoding, followed by finite-aleph/GCH bounds
and coherent coding bijections; graph application alone does not interpret
the cardinal elements that represent functions in the manuscript's model.

## 2026-10-14 — annotation-preserving STLC reduction for completeness

The updated manuscript claims TOWER-completeness of closed well-typed
beta-convertibility. Implement the embedding portion in STLCEmbedding.v,
not an axiom standing for the external lower bound. Independent simple
typing and beta rules share only the original scoped raw syntax. A single
ground type suffices; code its arrows as products and close that type
variable with lambda o:U0. Keep every Church annotation. Normality of type
codes and shape closure under simultaneous substitution imply reflection
of original beta reduction; confluence then implies conversion reflection.
The final theorem packages typing, conversion equivalence and an exact
pair-size increase of 4. All eight new audited results are closed.

Use the Church-style version of Nguyen's Theorem 1 (LMCS 20(3:21), 2024,
https://arxiv.org/html/2305.12601v4), avoiding the manuscript's Curry inference
detour. Linear unification alone does not establish a linear bound for
writing explicit tree annotations. No source hardness theorem or machine
complexity model is in this repository. Consequently this milestone is a
checked reduction supporting the textual completeness proof, NOT a fully
formalized unconditional machine-level TOWER-completeness theorem. Keep
that boundary explicit. Existing normalization operation-cost qualifications
and the conservative-rank repair remain unchanged.

## 2026-10-14 — checked normalization classification with a repaired bound

The semantic head-rank definition is unchanged: rank of the product TYPE of
a redex head, not merely its annotated domain. Typed substitutions, renamings,
and context transport give a structural RankSafe predicate proved equivalent
to RedexBound on original well-typed inputs. Its substitution residual lemma
and the exposed-head lemmas prove strict greedy descent. Thus d-bounded
original-typed terms normalize in d passes; the costed implementation now has
a success theorem, not only an upper bound for unsuccessful attempts.

The manuscript's bridge from maximum abstraction-domain rank B to semantic
(B+1)-boundedness is false under product binders. EstimatorChecks.v proves a
closed witness typed at U3 has estimateRank = 0 and a rank-2 redex head:
B = Pi _:U0.U0, A = Pi _:B.U0,
Pi x:A. Pi y:B. ((lambda z:U0.x) U0) y.
This counterexample does NOT refute TOWER normalization or the success of
the original sharper estimator budget; it refutes that proposed bridge.
Retain rank.agda's faithful translation unchanged and retain the checked
counterexample. Do not silently change the meaning of head rank or input typing.

Use the conservative computed bound 1 + maxRankLiteral t + nodes t for the
automatic normalizer. SortBounds proves the underlying sort bound uniformly
over typed simultaneous substitutions and application spines. This covers
every binder, including products. AutomaticBound proves semantic soundness,
magnitude <= 2*encodingSize+1, and cost <= 7*encodingSize. Normalization.v
combines it with the fixed-rank proof and costs the bound computation as well
as reduction: tower (4*s+3) (18*s+8). All public statements use original typ,
original beta normality and unchanged result typing; no pending proof contract.

The classification is for the documented explicit constructor/callback and
word-operation model with unary-label/index encoding. Cost counters are ghost
accounting, not a claim about running the Gallina unary counters. A separate
machine/extraction or binary-label analysis is not asserted. The sharper Agda
budget is optional future research, not needed for these completed results.

## 2026-10-13 — normalization-complexity library and cost-model separation

- Create independent PTSrk.NormalizationComplexity library under theories,
  depending on the unchanged original kernel; no arithmetic interpretation or
  set-model dependency. Translate rank.agda's reference and optimized variants.
- Prove optimization agreement with the simplified estimator, not an unjustified
  equality between reference and simplified algorithms on ill-typed syntax.
- Count unary labels and variable indices in input encoding. Explicitly charge
  linked-context lookup; state linearity for an abstract word-operation model,
  not Rocq unary-natural bit execution. Prove numeric word-size bounds separately.
- Preserve lambda annotations in greedy reduction. Prove beta soundness and
  exponential/iterated-tower output-size bounds without assuming rank descent.
- Use a checked normal-form test for bounded attempts. Do not call a bounded
  attempt a total typed normalizer until its computed budget is proved sufficient.
- TOWER/ELEMENTARY membership remains open: semantic estimator soundness,
  strict greedy redex-rank descent, and implementation time bounds are still
  required. Closedness/well-typedness restrictions from the paper are retained.
- Add an audit stage to existing CI; no existing stages are weakened or removed.

## 2026-10-13 — instantiate Good and realize all functional axiom indices

- Expose the original Good predicate with a fixed, checked specialization
  term. Its arguments are arbitrary typed d and an exact rank-10 family Q;
  no recursion on host expression trees or new induction principle is added.
- Instantiate Q at the existing annotated invariant_motive. Generic family
  formation and proved beta/renaming equations transport the four constructor
  closure witnesses to the exact binder annotations required by Good.
- Project the uniform negative bounded case from the positive invariant.
  Derive R4 using internal no_back in the large branch, and derive R5 from
  finite equality/order transport or transitivity of the global large bound.
- Package all five original schemes as a uniform Prop-valued existence of
  original PTS typing witnesses. This does not prove the archived generator
  contracts or build the legacy Type-valued witness-selection record.
- Independent functional first-order deduction preservation still must be
  proved. Do not call this axiom-realization milestone the completed Theorem 7.

## 2026-10-13 — multiplication closure with guarded order bounds

- Reuse the addition milestone's negative case eliminator and two-child
  positive-invariant elimination, without changing the carrier or ranks.
- Multiplication propagation requires the OTHER factor to be at least one.
  Keep that premise explicit in both scoped order-bound lemmas. Obtain it
  from equality to a positive numeral or a global large-branch lower bound.
- Handle both zero-factor cases separately, transporting equality through
  multiplication congruence and then using the appropriate original zero law.
  A large factor with a zero factor never enters a propagation branch.
- Cover finite/finite, finite/large, large/finite and large/large branches by
  actual target proof terms. Case analysis only returns the stable CaseAt;
  positive G evidence is retained outside that analysis for invariant closure.
- The next mathematical step after checked closure is Good instantiation at
  the existing rank-10 invariant motive. This does not yet discharge R4/R5 or
  functional first-order deduction preservation.

## 2026-10-13 — addition closure and two-child invariant elimination

- Generalize finite-branch injection to equality with an arbitrary numeral:
  below the cutoff choose the finite branch; above it compose ground order
  with reverse order induced by equality. This remains an internal proof.
- Prove addition's finite/finite branch using original congruence, the existing
  ground-addition theorem, and equality transitivity. Either large operand
  bounds the sum via its original guarded propagation law.
- Package negative case analysis with stable targets and actual context-
  extension callbacks. This reduces nested branch bookkeeping while preserving
  the original PTS typing relation and lambda annotations.
- Compose Positive.extension derivations constructively. Eliminate both child
  positive invariants at the SAME rank-8 answer type; carry their positive G
  evidence and negative cases separately. Feed the parent continuation only
  after independently constructing its G and Case witnesses.
- Addition invariant closure is proved for arbitrary scoped objects, not just
  host expression trees. Multiplication still needs zero/positive-factor cases;
  no bounded-case theorem or Theorem 7 completion follows yet.

## 2026-10-13 — exact-rank functional invariant and successor closure

- Reuse Codes.CaseAt/InvariantAt and NegativeLogic's positive invariant. In
  the functional interpretation both equality and order have rank 6; a
  nonempty flat case list has exact rank 8, independently of cutoff. The
  invariant/motive have rank 10. No cumulativity is used.
- Apply original closed guarded laws in arbitrary contexts by weakening and
  scope-correct substitution. Finite successor branches either advance below
  the bound or provide the global large branch by equality/order congruence;
  a large child propagates by successor order and transitivity.
- Use Positive.extension callbacks when eliminating the invariant under
  continuations. This keeps positive G evidence separate from negative Case
  evidence and lets the successor proof return the parent's SAME rank-8
  answer variable. Negative cases eliminate only into the stable Case target.
- Rewrite a continuation's type through a separately proved equality, not
  its entire typing hypothesis: the latter can inadvertently rewrite the
  context and prevent applying original weakening/extension lemmas.
- Uniform zero and successor closure, motive typing/beta, and case projection
  are proved. Addition/multiplication closure and the final Good instantiation
  remain open; these results alone are not the bounded-case theorem.

## 2026-10-13 — original functional separation and negative ground faithfulness

- Extract the literal two-binder body of Codes.Order, retaining all annotations.
  Prove its two-step reduction and exact equality with the data/law telescope
  and order_suffix. Reduce assembler eq_rect transports explicitly, peel the
  31 product binders and normalize only the remaining closed-substitution goals.
- Obtain observation formation by original subject reduction from Order's
  existing typing theorem. No formation/well-formedness hypothesis is added to
  the public no_back theorem. Lift this closed result under the original LeAt
  binder and use the constructed finite observation to obtain internal Bottom.
- Use no_back plus the existing original order-transitivity law to refute
  every reversed numeral comparison. Partially specialize closed laws to
  residual arrow types; weakening and ordinary arrow introduction/application
  then supply contraposition and permutation of proof arguments.
- Ground order refutation transports the existing term-to-numeral equalities
  through order congruence. Equality implies order on observed terms, so order
  refutation and equality symmetry also give false ground equation refutations
  and uniform R3. A separate equality-table/source bridge is unnecessary here.
- All these are original typ inhabitants, not native-Prop replacements. The
  four-constructor bounded invariant, R4/R5 and independent functional deduction
  preservation remain open; no completion of Theorem 7 is claimed.

## 2026-10-13 — data-only atomic suffix specialization

- Prove telescope prefix preservation from the typed argument-spine relation.
  Embed data-only suffixes with telescope_inclusion and use replace_rename
  pointwise; do not unfold the 23 existential law proofs or assume extensionality.
- The original functional numeral fold in the finite order table reduces to
  the negative entry at min i c and min j c. Backwards-successor separation
  requires c = S n, hence S (S n) selectors; c = n would collapse both indices.
- Export a contextual elimination lemma for the expanded observation. It
  applies real data/law arguments, converts the result to Neg Top and applies
  the actual top proof to obtain Bottom. This is internal PTS typing, not an
  external model argument or a host-Prop arithmetic substitute.
- The source EqAt/LeAt beta/formation bridge is still missing. Neither this
  elimination lemma nor its numeral suffix conversion is advertised as the
  original no_back theorem, negative ground faithfulness, or Theorem 7.

## 2026-10-13 — contextual observation and functional fold equations

- Lift the closed dependent argument spine through the original weakening
  theorem. Track terminal substitutions pointwise and compare replaced terms
  with replace_ext; do not assume function extensionality.
- Choose the finite law terms once, independently of context and the input
  observation proof. Apply the data and law spines sequentially to preserve
  their exact dependent suffix. Connect this theorem to the named source.
- Prove fixed open beta schemas for all four Codes constructors, then
  instantiate them by scope-correct substitution. Numeral folds use the
  functional five-argument carrier; the shared iteration helper is merely
  syntax and does not change the interpretation.
- These results enable, but do not themselves prove, internal no_back.

## 2026-10-13 — binary congruence and order-law observation prefix

- Package binary congruence with all four interleaved guards, retaining the
  original equality-table and binary-operation applications. Specialize the
  existing typed law separately to capped addition and multiplication.
- Extend order congruence through the same four-object discipline, then reuse
  generic reflexivity/transitivity application certificates for Nat.leb.
- Preserve exact source-prefix equalities and dependent suffix substitutions.
  Source matching uses direct application of assemble_prefix_congr; this avoids
  expensive whole-goal reduction/rewriting and changes no source statement.
- All ten arithmetic arguments are now assembled as well. Their rank-five
  formation and beta conversion preserve annotations and multiplication's
  positivity premises. full_observation_specialization reaches the original
  complete nAllObs source, for every named suffix.
- Export observation_certificates and observation_arguments independently of
  any assumed typed observation. This makes the closed finite instance usable
  for future context lifting and internal separation.
- This finishes observation assembly, not Theorem 7. Contextual separation,
  the four-constructor bounded invariant and functional deduction preservation
  remain substantive obligations.

## 2026-10-13 — successor-congruence observation argument

- Retain original predicate, equality-table and unary-operation applications
  in the raw interleaved guard. Prove substitution through that guard and
  exact rank-five formation of its finite specialization.
- Use the checked unary-congruence theorem via beta conversion, preserving
  lambda annotations. Specialize the operation to capped_successor uniformly
  for q>0. No raw selector canonicity is assumed.
- Match the original first sixteen source fields and perform the sixteenth
  dependent application. Fifteen observation arguments remain unassembled.

## 2026-10-13 — equality equivalence-law prefix

- Preserve the source's interleaved object/domain guards for symmetry and
  transitivity, and prove substitution through these raw annotated types.
- Convert predicate/table applications to the existing finite law types using
  beta conversion with exact rank-five formation. Generic certificates work
  for every Boolean symmetric/transitive relation with the stated bounded
  numerical premises; equality discharges these premises without assumptions.
- Source-prefix equalities check firstn 14 and firstn 15 for arbitrary suffixes.
  Actual dependent applications extend the eight-data/four-domain/reflexivity
  prefix through both chosen proof terms. Sixteen further arguments remain;
  this is not yet a closed implementation of the entire observation.

## 2026-10-13 — equality-reflexivity observation application

- Keep the original predicate and relation-table applications in field 104.
  Prove their exact formation and beta conversion to the existing uniformly
  guarded reflexivity certificate; do not substitute a reduced annotation
  without a checked conversion.
- Generalize the relation-table application typing and beta lemma to arbitrary
  ambient scopes. The reflexivity certificate works for any Boolean relation
  reflexive on all indices below q, and in particular finite equality/order.
- Identify the thirteen-field prefix with source assembly for every suffix.
  Apply the equality certificate by tApp and retain the suffix's dependence
  on all five proof arguments. Eighteen further relational arguments remain.

## 2026-10-13 — four-domain-certificate observation prefix

- Package uniform bounded binary-table closure into an interleaved two-object
  PTS certificate. Use guarded_intro and the existing positive delta_binary
  proof; do not apply the rank-at-most-three relational eliminator to the
  rank-four positive membership conclusion.
- Convert each closed certificate to the predicate-application type used by
  the original telescope. Both addition and multiplication discharge the
  generic bounded-table premise uniformly for every q>0.
- Prove simultaneous substitution through the generic binary guard. Identify
  source fields 102 and 103 after all preceding substitutions, retaining any
  suffix dependence on the actual four certificate terms.
- domain_prefix_matches_source checks the original first twelve fields for
  every named body. domain_specialization performs the actual twelve PTS
  applications. This is not the entire observation or an interpretation theorem.

## 2026-10-13 — typed dependent application and ten-argument observation prefix

- Represent an argument spine by original typing judgments at successively
  substituted annotations. Prove arguments_application using only ordinary
  tApp and the simultaneous/single substitution identity; do not replace
  dependent application with a homogeneous list of separately typed terms.
- Prove the eight-data telescope equals assembly of the first eight fields of
  Codes.observation_fields for every named suffix. Repeat the source-prefix
  equality through the zero and successor domain certificate binders.
- Specialize arbitrary typed suffixes through all eight finite data terms and
  the first two domain proofs. The remaining codomain is the exact simultaneous
  substitution, retaining any dependency on the actual proof arguments.
- Reuse Separation.predicate/initial_certificate/step_certificate, which are
  generic finite-membership constructions, not the unary interpretation's O.
  The original functional observation and calculus remain unchanged.
- This is ten of thirty-one arguments, not the complete observation. Binary
  domain closure must still be packaged and its binder conversions checked;
  the nineteen relational proofs must then be applied in their fixed order.

## 2026-10-13 — all five finite order-propagation laws

- Compile unconditional comparisons and one-premise order implications from
  finite expressions. Their PTS bodies have exact ranks two and three,
  respectively. False Boolean premises are handled by the already checked
  negative Horn constructor, not by general positive ex falso.
- Provide separate one- and two-object abstraction theorems, each exporting
  the expanded interleaved domain guards with checked beta conversion and
  rank-five formation. Successor propagation has no dummy second object.
- Retain the observed-one lower bound in each multiplication implication.
  Handle q=1 separately: its sole index is zero. For q>=2 the observed one is
  the native index one, making the numerical product lower bound valid.
- All nineteen relational observation laws now have individual closed PTS
  certificates. This is not yet the complete observation: its eight data and
  twenty-three certificate arguments still need typed dependent assembly.
  The bounded invariant and independent functional deduction preservation
  remain separate unfinished obligations. No interpretation theorem is claimed.

## 2026-10-13 — finite-table expression evaluation and recursion equations

- Introduce a small two-variable expression syntax solely for composing finite
  observation tables. Its denotation is an original annotated PTS term. It is
  not a replacement for the arithmetic-expression domain D or its Good predicate.
- Prove denotation typing, substitution compatibility, bounded numerical
  evaluation and beta evaluation on selector inputs compositionally. These
  lemmas avoid duplicating nested table reductions in each observation law.
- Compile universally valid numerical equations into original PTS negative
  equality inhabitants, then close the two interleaved domain guards. Export
  expanded types with explicit beta-conversion and exact-rank formation proofs.
- Reuse CappedArithmetic.capped_add_succ and capped_mul_succ only as numerical
  side facts. The native observation record is not used as a PTS inhabitant;
  every proof of membership/equality is constructed by checked PTS lemmas.
- All five finite arithmetic equations are now proved. Five finite order laws,
  complete observation assembly, the bounded invariant and independent functional
  deduction preservation remain open. The external set model is out of scope
  under the user's replacement AGENTS instructions.

## 2026-10-13 — finite arithmetic zero laws

- Compile all three zero equations through one guarded, rank-two unary family.
  Its Boolean parameters select the zero argument's side and whether the result
  is zero or the input; they do not add proof assumptions to the public laws.
- Prove every point branch using the existing binary table beta action and
  negative_true, then eliminate positive domain membership through the checked
  guarded telescope lemma. No raw-selector canonicity is assumed.
- Export expanded guarded types and audit their formation and beta conversion.
  The generic constructor requires a pointwise beta equation; each of the three
  public capped-operation laws discharges that equation for all bounded indices.
- Twelve of nineteen relational observation certificates are now available.
  The two successor-recursion equations and five order-propagation laws remain;
  no full observation, separation, bounded invariant or Theorem 7 is claimed.

## 2026-10-13 — finite successor and binary-operation congruence

- Prove generic unary/binary operation congruence from original PTS typing
  and positive domain closure on every selector tuple. On true equality
  branches, native index equality makes the outputs literally identical;
  guarded relation reflexivity constructs their PTS equality certificate.
  Existing capped-operation domain closure discharges all generic premises.
- Generalize Boolean-premise introduction only to negative conclusions of
  rank-one types. A false premise yields Bottom and the negative conclusion
  is constructed by abstraction, not by an unavailable general eliminator.
- Retain the expanded two-/four-object telescopes with interleaved domain
  guards as public types. Check beta conversion and exact rank formation.
  Do not infer canonicity of arbitrary selectors or erase binder annotations.
- These are three more of the nineteen finite relational certificates, not
  the completed observation or Theorem 7. Ten laws, the bounded invariant and
  independent functional deduction preservation remain explicit obligations.

## 2026-10-13 — arbitrary guarded telescopes and finite relational laws

- Factor interleaved selector/domain abstraction into a uniform guarded_intro
  theorem using actual context-extension paths. Open every guard before
  applying delta_eliminate_arguments; never eliminate membership directly
  into the rank-five outer telescope. Prove the telescope's exact rank.
- Compile equality/order transitivity and arbitrary finite-relation equality
  transport using the Boolean Horn branch constructor. Instantiate it with
  fully discharged native truth-table side facts to obtain PTS inhabitants.
- Export the expanded, interleaved-guard law types, not only applications of
  curried family terms. Prove their rank-five formation and explicit beta
  equivalence before converting the constructed certificates.
- These three additional certificates do not by themselves assemble the full
  finite observation or prove Theorem 7. Keep the remaining thirteen relation
  laws, bounded invariant and functional deduction preservation explicit.

## 2026-10-13 — CI interruption and generated-example memory repair

- Distinguish the supplied runner shutdown (143) from a compiler rejection.
  Neither configured timeout had elapsed; the log does not identify the cause.
- Keep generated witnesses compact in Ltac. Compute the scope success tag,
  then kernel-check the selected Gallina expression using the unchanged
  checker and fuel. This avoids expanding a huge syntax tree into the goal;
  it does not remove examples or assume the fallback is typed.
- Preserve signal diagnostics and nonzero exit status. A killed host can still
  prevent artifact upload; shell traps cannot fix hosted-runner shutdowns.

## 2026-10-13 — functional Theorem 7 continuation (not completed)

- Keep the arithmetic-expression carrier and guarded 31-argument observation
  telescope fixed. Theorem 4's unary interpretation is not a replacement for
  this direct functional statement. Source arithmetic operations do not become
  beta arithmetic on expression presentations.
- Proved arbitrary closed-expression evaluation by EqAt, composing the checked
  guarded congruence laws with uniform numeral arithmetic certificates.
  Open-term Good closure supplies observed evidence where those laws require it.
- Atomic stability abstracts the actual full observation telescope and its
  final negative test; fixed certificates are checked in original typ.
- Added actual binary selector tables and positive finite-membership closure.
  Eliminate input membership only at rank-three motives after opening the output
  continuation. Native boundedness is a side condition on indices, not a
  replacement for PTS inhabitants.
- Implemented relation tables and exact-rank lifting, then derived arbitrary-
  arity positive-membership elimination. Guarded equality/order reflexivity
  and equality symmetry are checked closed certificates. Added a uniform
  Boolean Horn-branch compiler producing actual negative PTS conclusions;
  native truth-table validity is only its finite branch side condition.
  The other 16 relational certificates and
  the four-constructor invariant are still required; successful point branches
  alone are not claimed to prove the full observation telescope or Theorem 7.

## 2026-10-13 — complete unary relational Theorem 4

- Proved translated formula stability structurally, including guarded universal
  quantification. Classical elimination constructs original PTS inhabitants;
  no host classical axiom, positive elimination from negative disjunction, or
  change to the PTS rules was used.
- Proved equality transport for every source formula. Bound objects and their
  Good guards are shared between the compared environments; no equality
  invariance of Good is assumed. Binary arithmetic congruence uses annotated
  lambda sections and beta conversion, not eta or annotation erasure.
- Proved every constructor of the independent classical natural deduction
  system sound for the structural translation. Sentence preservation has no
  certificate-record or theorem-soundness premise.
- Connected the concrete SOURCE countermodel to that calculus, proving its
  soundness without classical axioms via decidable atoms and structural
  stability. Universal order reflexivity is underivable there but its guarded
  target translation has the already checked rho witness.
- Assembled Theorem4.theorem4 with all axiom schemes, all classical deductions,
  ground proofs/refutations and nonfaithfulness. The final theorem and each new
  principal dependency pass Print Assumptions with no global assumptions.
  Fresh build and full-suite status are recorded separately in STATE.md.
- Theorem 7, external Bottom nontriviality, internal self-consistency and PTS
  set-model soundness are not consequences claimed by this theorem.

## 2026-10-13 — independent relational syntax and structural translation

- Defined a scoped source language with only 0/S terms and the four atomic
  predicates =, <=, A, M. Source derivability is inductive natural deduction,
  independent of PTS inhabitation, with classical double-negation elimination,
  universal rules with scoped freshness, and full formula equality replacement.
- Falsity, implication and universal quantification are primitive. Conjunction,
  finite disjunction, existential and equivalence are classical abbreviations
  using the manuscript's negative encodings. No source rule assumes target
  soundness, and no native classical axiom was imported.
- Proved structural translation/substitution/renaming and instantiation laws,
  exact formula ranks, and typed/admitted term translation. Ground source terms
  translate to their unary numerals, connecting all four kinds of source atoms
  to genuine PTS proof/refutation inhabitants.
- Proved preservation of the independently stated source axiom schemes, plus
  implication and guarded universal elimination. These do not imply arbitrary
  deduction preservation: stability, equality transport, introduction rules,
  and the derivation induction remain explicit obligations.

## 2026-10-13 — all relational axiom schemes and ground arithmetic

- Proved the full guarded R4 biconditional, not just its forward direction.
  Negative bounded-case elimination uses the checked no_back certificate;
  its target is stable. No positive domain certificate is extracted from it.
- Proved actual unary numeral addition and multiplication by beta conversion
  through fully annotated Church normal forms, with no eta conversion.
  Finite open schemas are substituted at arbitrary terms; index induction
  proves the all-index result, not successful finite examples.
- Used those equations to realize relational R1/R2 with arbitrary admitted
  third arguments, and both proofs and refutations of all ground ternary atoms.
- Added an unconditional all-five-schemes realization theorem in original typ.
  It is explicitly NOT the whole Theorem 4 or the old functional target.
  Independent source deduction preservation, a structural source translation,
  and countermodel soundness/non-derivability remain to be connected.

## 2026-10-13 — uniform unary separation and R3

- Completed the upward separating test with an exact rank-three motive;
  only negative conclusions are obtained from contradictory test evidence.
- Proved unary fold computation on arbitrary scoped arguments by substitution
  into fixed open beta schemas, then induction on the external numeral index.
  Domain annotations are retained and no eta equality is used.
- Instantiated the actual O telescope with all three closed certificates:
  d0, ds and Up. Compact structural telescope types avoid expanding the full
  named order encoding during substitution. No certificate is assumed.
- Proved unconditional uniform no_back, every reversed ground order
  refutation, and all distinct-numeral R3 instances in original Typing.typ.
- Theorem 4 is still incomplete: relational R1/R2, both directions of R4,
  ground ternary arithmetic and independent source deduction preservation
  remain. This is not a claim that Kernel.Theorem5Target (functional) is proved.

## 2026-10-13 — positive finite observations

- Added positive finite membership with rank-3 predicate parameters rather
  than reusing negative disjunction to obtain unrestricted positive results.
- Generic telescope introduction transports actual witnesses only along
  original context extensions; its transport proof uses PTS weakening.
- Instantiated the exact finite delta predicate from the harmonized text.
  All selector certificates and a closed capped-successor certificate are
  checked uniformly in arity. The only bound is q>0, the nonempty telescope
  required for rank four; no raw-selector parametricity is assumed.
- Added transitive assumption audits and dedicated CI stages. No PTS rule,
  target, axiom, admission, eta principle or annotation-erasing bridge changed.
- This is a partial Theorem-4 checkpoint: Up(P), no_back, remaining axiom
  schemes, ground refutations and independent deduction preservation remain.

## 2026-10-13 — relational comparability and uniform finite tables

- Proved the unary relational comparability scheme for all cutoffs, using the
  existing bounded-case invariant, equality-to-order and ground comparisons.
  This axiom does not require finite separation. The original-kernel audit
  states its exact guarded universal type explicitly.
- Added intrinsically scoped finite projection/table builders with uniform
  formation and full-term beta equations. This replaces the need to certify
  the old named assembler's finite table code for the unary interpretation.
  It does not change Domain, Equality, Order, PTS rules, or annotations.
- Capped successor action, separating tests and arbitrary iteration are
  checked, with explicit valid-index bounds. Beta action is not pointwise eta
  reasoning, and no parametricity over all raw selector inhabitants is used.
- The positive delta predicate/certificates and the upward test law still
  need construction. These table lemmas do not by themselves prove no_back,
  R3/R4, ground refutations, or source deduction preservation.
- Expanded CI with finite-table and unary-axiom stages, leaving existing
  stages and timeouts intact. All 27 current unary assumption queries are
  closed. See STATE.md for commands and compiler evidence.

## 2026-10-13 — unary Theorem-4 proof continuation

- Follow the latest request's unary Theorem 4; do not advance the separate
  functional or set-model developments in this session.
- Added fixed closed certificates for the unary basic laws, equality/order
  stability, and a rank-ten positive invariant eliminator. The latter retains
  explicit case-family closure premises and is not advertised as bounded cases.
- Uniform numeral/order proofs use structural application and external
  induction. Variable-arity negative logic uses original typ derivations,
  not a fuel check repeated on finite examples.
- Case_n is exactly the manuscript's flat list of rank-five equalities plus
  one rank-six order atom. Its rank eight, Inv_n's rank ten and both zero
  witnesses compile uniformly. G remains positive and is constructed separately.
- No PTS syntax/rule changes, new axioms, admissions, or positive ex-falso.
  See STATE.md for exact successful and failed compiler transcripts.
- Completed the actual all-cutoff successor closure using stable flat
  elimination, successor congruence and order transitivity. Instantiating
  cases_from_closure with the actual Case_n family now proves the unconditional
  bounded-case lemma for arbitrary Good inhabitants, not expression trees.
- Added a distinct original-typ audit theorem and CI stage. All 15 transitive
  assumption reports are closed; a fresh isolated build of the unary audit,
  old DirectR facade, arithmetic, countermodel and model foundations succeeded.
  This milestone is not Theorem 4: finite separation, complete relational axiom
  realization, ground refutations and first-order preservation remain open.

## 2026-10-13 — imported handoff

- Keep TurtlePU's original scoped beta-only PTS kernel.
- Use arithmetic-expression presentations and certified observations directly;
  no intermediate WF- interpretation.
- Use the modular native target evaluator/checker design; lab code can be
  adapted, not trusted as a bridge to the original typing judgment.
- Keep the section-3 finite observations for INTERNAL arithmetic refutations.
- Reduce the separation API to no_back_n if that simplifies the uniform proof.
  This is a proposed code refactor with an on-paper argument, not compiled yet.
- Set models are excluded. External Bottom-uninhabitation can be a separate
  corollary of normalization/preservation/canonical shapes, not a prerequisite.
- No uniform Theorem 5 proof or successful Rocq build was recorded in this chat.
- User uses ordinary Git and browser GitHub Actions, not gh.

Append dated entries for substantive changes: decision, reason, alternative
rejected, actual evidence and affected theorem statements. Avoid claiming that
an architectural change has been verified before compiling it.

## 2026-10-13 — CI toolchain and local checks

- CI now pins Rocq core 9.2.0, Stdlib 9.1.0, and Equations 1.3.2+9.2.
  The historical upstream uses `Create Rewrite HintDb`, introduced in 9.2;
  run 38328517931 failed parsing it under 9.1.1. The unchanged baseline
  compiled under the updated local toolchain.
- Installed a dedicated native ARM OCaml 4.14.2 switch and matching static
  GMP 6.3.0. Existing Intel Homebrew GMP cannot link with the ARM compiler.
  Local checks use actionlint followed by the actual CI build driver, rather
  than treating YAML parsing alone as workflow validation.
- Repaired evaluator/checker scripts with explicit case analysis, correct
  indexed induction patterns, and properly constrained theorem applications.
  No statements, target rules, assumptions, or checking flags changed.
  Their main soundness theorems compile and report no global assumptions;
  see STATE.md and the infrastructure assumption transcript.
- DirectRCodes excludes Syntax's notation category to avoid the upstream
  lambda/list parser conflict. It still imports the original constructors
  and definitions. DirectRProofs supplies the closed application parameters
  explicitly to `fold_left`.
- An experiment reusing fixed certificate hypotheses in the symbolic tactic
  exposed a further opaque-numeral typing problem and was reverted. Repairing
  that symbolic induction layer remains pending; no uniform theorem completion
  is claimed.

## 2026-10-13 — checked structural and numeral foundations

- Pushed the authorized checkpoint `b6fa20660860258717637426605353e0bf3e38e5`
  with the existing infrastructure fixes, user-supplied handoff, and local CI
  setup. Downloaded `logs/` artifacts were preserved and not added.
- Split the previously monolithic proof dependency into DirectRStructural,
  DirectRFoundations, and the remaining DirectRProofs. Kernel includes
  Foundations, preserving its public names and the Theorem5Target statement.
  CI now reports these two new dependency stages separately without dropping
  any existing stage or relaxing time limits.
- Proved substitution identities without unfolding symbolic numerals or
  closed observation certificates. Direct two-step applications now prove
  observed/admitted successor closure, both uniform numeral families, and
  the ground-addition base case. Their statements use the original typ.
- Added rank-annotated dependent telescopes with explicit annotation formation
  obligations; formation, abstraction, and projection are proved generically.
  Added all-arity selector formation/typing, typed table application, and
  beta-computation to the selected entry. These are not finite tests.
- The new scoped selector implementation is NOT yet identified with the named
  generator's nSelector/nFType encoding. Nor does table application alone
  certify unary/binary capped operation tables, delta elimination, or all
  observation laws. Those integration and realization obligations remain.
- A recursive application-tactic experiment still stalled in the addition
  base case and was removed. The direct base-case lemma compiles. The legacy
  tactic remains only downstream, starting at ground_add_typed's successor
  step; do not treat that source proof as checked.
- The new modules compile under the installed toolchain. Assumption queries
  for telescope formation/abstraction/projection, selector typing/table
  application/computation, both numeral families, and the addition base-case
  application all say `Closed under the global context`.
  Exact transcripts and remaining build status are recorded in STATE.md.

## 2026-10-13 — harmonized Theorems 4 and 7

- The user's harmonized TeX supersedes the old numbering: label main is
  Theorem 4 (unary relational interpretation); thm:direct-R is Theorem 7
  (functional interpretation). Neither is just the old axiom-witness record.
- Completed compilation of the uniform ground addition, multiplication and
  order families, hence R1_realized/R2_realized. Direct structural application
  lemmas replaced the legacy symbolic proof calls. All three main assumption
  queries report no global assumptions.
- Added DirectRUnary for the distinct unary carrier and negative-test
  equality/order. Exact-rank formation, constructor certificates and the
  paper's raw/admitted order-reflexivity terms are checked.
- Added the concrete source countermodel, with proofs of all relational and
  functional axiom schemes and failure of universal order reflexivity. It
  does not replace an independent source deduction system or its soundness.
- Added the functional admitted-reflexivity witness as well. Both target-side
  witnesses are separate from the countermodel's host-logic facts.
- Repaired actual downstream compiler failures: generator notation/type
  inference, explicit intermediate objects in existing native arithmetic
  proofs, and the missing scope parameter in the zero-budget test. No rule,
  target statement, assumption, or CI timeout was weakened.
- User explicitly put the PTS set model in scope as a subsequent task using
  rocq-archive/zfc. Preserve its ZF+GCH premise and audit imported library
  assumptions separately. No model soundness proof has yet been constructed.

## 2026-10-13 — concrete set-function foundations, not model soundness

- Pinned the required Sets/Axioms/Cartesian subset from rocq-archive/zfc at
  ede7126560844c381c2b021003a8dbcb0668ecad, preserving LGPL license and provenance.
  Replaced the removed elimtype tactic only. No logical statement changed.
- Built dependent function sets by separation from a powerset of a Cartesian
  product. Indexing a set directly by all host functions Ens -> Ens would
  exceed the library's set-indexing universe; no universe check was disabled.
- Proved graph introduction, application, uniqueness, beta computation and
  empty-fiber emptiness with the actual set library. All printed assumptions
  are closed. No choice or GCH assumption is needed for these foundations.
- The paper's coding universes/cardinal bound/coherent bijections and original
  PTS typing soundness remain open. This checkpoint does not claim them, nor
  does it call the generic empty-fiber fact a proof of PTS nontriviality.

## 2026-10-13 — completed functional theorem and effective witnesses

Use a separate functional source countermodel with the shared arithmetic
structure to prove nonfaithfulness. Its negative semantics validate all
independent classical deduction rules constructively. No external PTS set
model or native classical axiom enters the interpretation theorem.

Close the Prop-to-Type gap by constructive exhaustive search, NOT choice or
an assumption of generator completeness. DirectRDerivationCertificates
interprets finite trees as original annotated typing derivations. Soundness
and completeness are proved against the unchanged Typing.typ/RankSorts rules.
Beta conversion certificates contain two finite reduction paths to a common
reduct; completeness uses the existing kernel's confluence theorem. Reductions
inside annotations are retained. This does not assert normalization of arbitrary
terms or decidability of typing.

DirectRWitnessSearch enumerates all finite certificates, and Stdlib's
constructive indefinite ground description on naturals selects a successful
stage from its proved existence. All assumptions are closed. This provides
transparent Type-valued witnesses for all axioms and source deductions and
constructs Kernel.Theorem5Target itself. The algorithm is intentionally slow;
the efficient native checker and historical bounded generator remain available,
but their separate totality contracts are not assumed or claimed here.

Theorem7.theorem7 packages all mathematical claims of thm:direct-R. Effective
interfaces accompany it, rather than misrepresenting Prop existence as a
Type-valued function. No rules, source axioms, domain, or theorem premises were
strengthened. Existing relational interpretation remains an independent library.

At the user's request move the existing set-model files from models/ to
ZFC_model/ without changing PTSrkModel or the pinned vendor/zfc dependency.
Update the build target but retain its checks. This is only a relocation of
the incomplete set-model foundations, not a proof of set-model soundness.

## 2026-10-13 — functional equality and deduction preservation

Prove equality transport with two typed Good-admitted environments and internal
equality witnesses. Keep all functional observation premises, deriving GAt from
GoodAt before using symmetry/transitivity/constructor congruence. Transportable
is only a local theorem property, proved for all formulas, never a premise of
the source deduction system or an addition to the domain.

For primitive conjunction/disjunction/existential, reuse the definitionally
equal negative encodings in the transport induction. This does not change the
source syntax or erase any PTS annotation. Preserve the source's actual
natural-deduction rules separately: conjunction and existential elimination
use the already proved stability of the translated conclusion. The existential
eigenvariable case extends the target context by the negated conclusion,
the domain element, Good admission, and the source premise, with explicit
source renaming/substitution lemmas throughout.

Full sentence preservation now compiles in the original typ relation. Do not
equate this Prop-valued constructive existence statement with a Type-valued
effective proof-term selection API. Nonfaithfulness of the independent
functional source calculus and the final theorem package remain separate work.

## 2026-10-13 — independent functional deduction infrastructure

Keep the existing FirstOrder functional syntax and translation, including its
primitive conjunction/disjunction/existential. Define a separate source
natural-deduction relation without target typing/inhabitation in its premises.
Use syntactic source substitutions and proper eigenvariable contexts, not
target inhabitation as a definition of source provability. Adapt structural
proof patterns from the relational development without importing that library.

The original functional R4 (harmonized paper, r:bound) is implication; do not
copy the relational biconditional as a source axiom. Use a classically equivalent
flat negative finite disjunction to match Codes.R4/R5; the source's primitive
binary disjunction remains unchanged. All five independent source schemes now
have unconditional realization theorems for arbitrary scoped environments.

Prove formula formation and stability compositionally for every formula,
including both guarded quantifiers. These are checked prerequisites, not a
claim of deduction preservation or completion of Theorem 7. Equality
replacement and induction over derives remain the next proof obligations.

## 2026-10-13 — independent interpretation libraries

At the user's request, move the DirectR development out of the original
theories/ kernel directory into Interpretation_of_R, with relational/ and
functional/ subdirectories. Each is a separate Dune rocq.theory; the two
interpretation libraries depend on shared infrastructure and PTSrk, never on
each other. No compatibility facade is added to PTSrk: that would introduce
a dependency cycle back from the kernel to its interpretation clients.

Extract CommonCodes (assembler, negative logic, exact-rank lifts, selector
syntax) from functional Codes, which includes those shared definitions.
Extract generic iterations/finite_iterations from UnaryEvaluation, finite
predicate/zero/successor certificates and step_guard from Separation, and
arrow_beta from Unary into Structural. Relational modules may re-export the
extracted APIs, but functional modules import their shared owners directly.
Move functional-specific unfolding out of the shared structural-substitution
tactic and into its Foundations call sites. All term encodings, typing rules
and proof obligations are unchanged. Source countermodel machinery is shared;
the separate external PTS set model stays untouched in models/.

Separate @Interpretation_of_R/relational/audit and
@Interpretation_of_R/functional/audit targets expose the existing assumption
audits. Theorem 4 is complete; the functional directory contains checked
components, NOT a completed Theorem 7. Build evidence and any refactor failures
are recorded in STATE.md. Historical logs keep their original paths.
## 2026-10-13 — normalization cost and semantic rank continuation

Use executable output/cost pairs, with proved projections to the existing
operations, rather than treating output size as runtime. Charge substitution
lifting/renaming and final normal checking explicitly. Costs are ghost
constructor/callback accounting, not the execution cost of unary counters.
The resulting fixed-pass ELEMENTARY and estimator-budget TOWER envelopes
are bounds for attempts; they are not claims that the attempts succeed.

Define TypeRank by original typings of a term and its type at a sort. Define
RedexRank by original product-typed head witnesses and all syntactic occurrence
positions, including annotations. Do not define rank by a successful fuel
budget. Conversion independence and substitution/reduction preservation are
proved using the existing kernel metatheory. A function's argument rank is
strictly smaller, but its result rank is only non-increasing; keep that
distinction in the descent proof. The newly exposed lambda/head bound is now
checked. Substitution residual bounds, context transport, strict descent and
semantic estimator correctness remain obligations, not assumptions.
