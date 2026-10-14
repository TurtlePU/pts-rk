# PTS-rk set model — original typing soundness proved

Reference: the set-theoretical model section of `latex/paper.tex`.
Dependency: the pinned LGPL subset of rocq-archive/zfc in `vendor/zfc`.

`ModelSoundness.original_typing_sound` proves soundness for ALL original
Typing.typ derivations under original valid valuations. It has no
semantic-conversion, coherence, certificate-totality or normalization
hypothesis. `original_membership_sound` covers arbitrary original denotation
witnesses, and `sound_nontrivial_model_exists` constructs a selector yielding
soundness and an empty interpretation of Bottom. The parameters remain
explicit: transitive W containing omega_codes, its supplied tower envelope
H, classical logic, cardinal comparison, infinite powerset gap and ordinary
family_choice. The internal BZC interpretation of these parameters and
constructions is still open; this result does not assert that derivation.

Current foundation target: reformulate this model in BZC + GCH + existence
of V_{omega+omega}, bounding constructions in the supplied hierarchy and
eliminating unbounded separation, then finish its soundness proof. Only
afterward pursue an interpretation in BZC + GCH without that existence
assumption. See [FOUNDATIONS.md](FOUNDATIONS.md) for the ordered milestones.
Neither weaker-foundation claim is established by Rocq assumption reports.

The first syntactic foundation audit is implemented in `BoundedFormulas.v`
and `BoundedInverse.v`: ordered pairs/application have explicit bounded
first-order formulas, and the inverse graph is proved equal to separation
by a bounded formula. This checks a specific predicate, not all of BZC
soundness or the strength of the Ens representation.

## Checked construction

`RankedHereditary.v` proves the simultaneous substitution theorem for every
cut rank, normalizing BOTH term and assigned type while preserving both
semantic values. It handles empty interpreted domains using syntactic
normal forms chosen before semantic quantification. `certified_application`
constructs the normalized result-type certificate for arbitrary normal
certified functions and arguments, including lambda arguments.
`RankedNormalization.v` normalizes unrestricted ORIGINAL denotations with
their actual values preserved. It derives variable certificates from
original context validity, then proves equality of actual values of
originally typed beta-convertible terms. This discharges the former
conversion premise of RealizationInduction in `ModelSoundness.v`.

The earlier module notes below describe the scope of those individual
lemmas. Earlier statements that the general semantic theorem was open are
superseded by ModelSoundness; the material BZC/GCH/hierarchy audit remains open.

`RankedDenotation.v` supplies structural certificates for normal original
terms AND assigned types, with actual recursive formation/body witnesses.
Membership and type rank follow from these witnesses. `RankedTransport.v`
proves same-value renaming, weakening, context transport and normal type/code
alignment. `RankedSubstitution.v` proves full-certificate nonlambda
substitution, normalized-binder lifting, and the rank-zero case of general
simultaneous bounded substitution. `NeutralCutRank.v` proves strict actual
domain-rank descent when substitution turns a neutral head into a lambda;
its bound on nonvariable images survives lifting under arbitrary binders.
`RankedRootBeta.v` derives body membership from certificate children and
preserves an arbitrary canonical redex value in the nonlambda-argument case.
The general results are now provided by RankedHereditary, RankedNormalization
and ModelSoundness, with the original denotation and validity unchanged.

`CanonicalValuationTransport.v` proves validity transport between contexts
whose paired declarations have actual same-value canonical denotations.
It does not infer that premise merely from original syntactic conversion.

`CanonicalRenaming.v` preserves canonical denotation under arbitrary typed
renamings. `CanonicalSubstitution.v` proves same-value substitution for
normal nonlambda images, including all normal arguments of rank-zero type.
`CanonicalContext.v` transports denotation and realization through original
context typing morphisms, without asserting valuation validity transports.
`CanonicalRealization.v` derives local membership/rank from unconditional
canonical coherence and proves variable, sort, product and normal-codomain
lambda realization. `CanonicalRootBeta.v` aligns arbitrary canonical redex
witnesses when the original domain annotation is normal, proves actual
product-domain rank descent, and obtains canonical root reduction for the
proved substitution case. The unrestricted results are exported by
RankedHereditary, RankedNormalization and ModelSoundness.

`CanonicalApplication.v` proves application realization for a normal inferred
product and normal nonlambda argument, with a rank-zero corollary. It uses
local realization inputs but no semantic-coherence premise.
`CanonicalHereditary.v` proves normal-form existence for applications of
normal operands with normal rank-one product type, and exact-value canonical
semantic preservation in the normal-lambda branch. This is the application
step from rank one to the proved rank-zero substitution case, NOT the full
rank-one substitution lemma or an all-rank soundness theorem.

`MaterialSetTheory.v` supplies independent first-order membership/equality
syntax and natural deduction, with a proof of logical soundness. The
bounded-formula embedding uses explicit membership guards. Ens satisfaction
of the syntactic bounded-separation schema is proved, so the specialized
logical soundness theorem requires classical logic but not an unproved
theory-satisfaction premise. `MaterialZermelo.v` extends this to the actual
first-order BZC axioms, including Foundation and von Neumann Infinity, and
proves their Ens satisfaction under explicit classical logic and ordinary
family_choice. It does not provide internal BZC derivations of the model's
constructions or the material GCH/hierarchy theory. Full PTS soundness in
the ambient representation is supplied by ModelSoundness.

`CanonicalTypeWitnesses.v` proves constructive normal-form existence and
normal inferred type witnesses for originally typed lambdas/applications.
`CanonicalDenotation.v` keeps the same annotated terms and model operations,
requiring these implicit witnesses to be normal. Its valuation extensionality,
same-value inclusion into original denotes, and COHERENCE are checked
without a semantic-conversion premise. This is only an auxiliary subrelation:
totality, beta/type-conversion preservation and agreement with unrestricted
denotation remain open. Normal types are not closed under substitution;
normalizing a substituted witness still needs semantic justification.

`BoundedChoiceSequence.v` constructs the same countable selection sequence
by bounded recursion, with an injection proof used by cardinal/product
classification. `BoundedModelData.v` gives actual set bounds for global
selectors and their graphs; the decoder is a subset of H, not asserted to
be an element of H. These are still Ens proofs, not a BZC derivation.

`TypedEquality.v` defines a native mutual typed-equality certificate over
original annotated terms. Reflexivity and projection to original typing
are checked. `TypedEqualityRenaming.v` proves native context regularity,
structural renaming and weakening by mutual induction, without assuming
endpoint regularity or preservation in the embedding definition.
Original-to-certificate completeness and semantic soundness remain open;
the existing target and PTS rules are unchanged.

`BoundedDecoder.v` combines all three branches after proving their exact
input/output specifications, excluding mismatched tags. The resulting
bounded-separation graph is total on omega_codes, single-valued, evaluates
to the existing decode, and equals all_decoding_graph. These theorems use
the existing explicit supplied-hierarchy premises, without Choice or GCH.
`BoundedDecodedSelection.v` uses that graph and omega_codes in bounded
coding-witness selection. Its witness sets and source domain equal the
original ones, and the selected values preserve the SAME selector s.
Every rank-typed dependent product is in its source domain. Ordinary
family_choice supplies the selector; no global/class Choice is introduced.
The first-order Ens/BZC audit and typed semantic conversion remain open.

`BoundedUniverses.v` gives a bounded graph for the exact original universes.
`BoundedSortDecoder.v` proves decoding agreement at every sort tag 3*n+2.
Together with the finite and infinite branches, this covers all individual
code forms; their combination is now provided by BoundedDecoder.

`BoundedRecursion.v` generalizes bounded iteration; `BoundedCodeArithmetic.v`
uses it for uniform tripling of singleton numerals. The resulting finite
decoder uses the actual 3*n tags and is correct for every finite code.
The infinite/sort branches are also checked; full model soundness remains open.

`BoundedCodeSelection.v` specializes bounded selection to the actual
coding-witness predicate and proves agreement with the existing global
selector. Every rank-typed dependent function space is covered. The new
decoded specialization supplies its decoder parameter by bounded separation;
full semantic soundness remains open.

`BoundedFormulaSelection.v` builds the selected graph for a total bounded
formula by bounded separation and proves function membership and selection
correctness. Ordinary set-indexed Choice is explicit; arbitrary denotation
predicates are not automatically covered by this theorem.

`BoundedIteration.v` defines the uniform carrier graph by bounded separation
using a least-closed-relation formula. It proves function membership and
evaluation at every numeral. Correctness now uses finite bounded separators,
not a native infinite comparison relation. A first-order foundation audit
and full soundness remain open; code-tag decoding is now checked.

`BoundedPowersets.v` certifies the powerset operation by a bounded formula
and graph separated from the supplied envelope's Cartesian square. Its
evaluation takes every carrier i to carrier(S i); closure follows from
existing envelope lemmas. BoundedIteration now supplies uniform recursion;
the first-order BZC interpretation remains unproved.

`RegularTyping.v` proves an equivalent induction certificate for original
typing, carrying explicit type-formation subderivations; erasure and the
original-typing embedding are both checked. `RealizationInduction.v` uses
it to derive realization for every original typing, CONDITIONAL on typed
decoded conversion. Component realization and rank obligations are now
derived in that induction, not separate model premises. The conversion
premise is still unproved; this is not unconditional soundness.

The same module now derives coherence of arbitrary typed denotations,
membership in any denotation of their type, and universe-rank membership
from that SAME conversion premise. These are not independent assumptions,
nor do they establish conversion itself.

`BoundedFiniteCarriers.v` gives a bounded least-transitive-closure formula
and uniform function graph for all finite numeral carriers. Code-tag
arithmetic and the other branches are supplied by the decoder modules.

`BoundedGraphs.v` builds formula-defined graphs by bounded separation and
proves their application law, agreement with bounded extensional native
functions, and function existence for total uniquely valued formulas.
There is no Choice premise in these theorems. BoundedDecoder now supplies
the decoder formula; the first-order foundation audit remains necessary.

`BoundedApplication.v` certifies the existing application value-fiber
separation and gives a bounded formula for equality to its union, without
assuming graph functionality. `decoding_value_certificate` specializes it
to the decoding graph with an explicit powerset bound. The graph's own
first-order construction remains an open foundation obligation.

`RootBeta.realized_root_beta` now compares an arbitrary redex denotation
with the shared ranked witness. It derives lambda/application coherence
from body/argument coherence and local conversion of typing witnesses;
redex coherence itself is not a premise. The reduct denotes the original
value, with membership in a ranked denotation of its substituted type.
This route removes universal rank/membership premises but still requires
constituent realization and conversion facts from the fundamental proof.

`DenotationInversion.lambda_product_body` proves from original typing alone
that every product witness for a lambda has a domain convertible to its
annotation and a codomain that types the body in the annotated context.
The beta proof now uses this fact and binder transport to derive its
application-fiber conversion obligation from body-type conversion. Its
remaining domain conversion compares typed domains to the annotation;
there are no separate application product-witness conversion premises.

`DenotationBeta.realized_beta` constructs a shared, semantically typed
value for a redex and its actual substituted reduct from constituent
realizations and decoded type coherence. It also supplies a ranked code
for the substituted result type. This is an existence theorem under local
induction premises, not coherence of all alternative denotations.

The new `lambda_realization_from_induction` and
`application_realization_from_induction` lemmas use ordinary existential
realizations and decoded type coherence to select ranked witnesses.
They do not require a universal rank bound on every possible denotation.
Product coherence likewise requires only equality of decoded components.
General realization/coherence and conversion remain unproved.

`RootBeta.v` inverts arbitrary redex/lambda denotations, derives syntactic
product-witness equalities and type correctness, and transports the
codomain into the lambda context. Its root-beta conclusion still requires
local typed semantic conversion, rank and membership induction facts;
those are not yet established by a general fundamental theorem.

`TypeHeadNormalization.v` proves, without semantic hypotheses, that typed
types reduce to sorts, products or variable-headed application spines.
Convertible typed types have a common such head and equal sort ranks.
The result uses original normalization/confluence/preservation, keeps all
annotations, and does not yet prove denotation preservation along reduction.

`BetaWitnessTransport.v` derives argument typing from the original redex
typing and transports beta across semantically equal product witnesses.
It reaches the actual substituted body, but domain/fiber equality, rank
bounds and membership remain explicit premises. These are not yet proved
for arbitrary typed denotations, so this is not full beta soundness.

`DenotationCongruence.v` handles all six compound-term reduction cases,
given preservation of the immediate reduced subterm, using original
subject/context reduction for typing witnesses. Lambda/application
inversion is proved in `DenotationInversion.v`. The arbitrary root beta
case and general conversion soundness remain open; matched beta alone is
not a substitute for them.

`ContextTransport.v` proves original typing/denotation transport from
variable-typing morphisms, original context reduction, and beta-equivalent
well-formed context declarations. The binder-context corollary needs only
original typing and syntactic beta equivalence, not semantic coherence.
This is context transport, not yet general term-conversion soundness.
Realizations now transport along the same context morphisms/conversions,
and along pointwise set-equal valuations. These results retain the selected
value/type code; they do not assume or establish preservation of valuation
validity when the context's declaration terms change.

`DenotationInversion.v` proves product inversion through equality closure,
variable-value uniqueness, and the product coherence step from subterm
coherence. Its lambda coherence step uses original typing uniqueness for
the two body-result types; decoded result-type conversion remains an
explicit obligation, alongside domain/body subterm coherence.
The application coherence step likewise uses typing uniqueness and proved
binder-context transport to compare the two product witnesses; semantic
conversion of their domains/fibers remains open.
`ApplicationRealization.v` offers both reuse of the function's product with
explicit rank facts and ranked selection from type realizations with
decoded coherence. Neither is a final soundness theorem.

`PairedChoice.v` selects related witness pairs with typed extensional
projections. `LambdaRealization.v` selects type codes and body values jointly
in U k × carrier k, preserving membership. Lambda realization now requires
pointwise ranked body witnesses but no preselected codomain family. Uniform
ranked realization, application compatibility and conversion remain open.

`BoundedFormulaTransport.v` proves extensionality of all bounded formulas.
`BoundedChoice.v` selects a set-graph-backed extensional family from bounded
relational candidates; its formula instance certifies the separation
predicate. `DenotationChoice.v` assembles type/body witnesses from pointwise
existence. The product rule now follows from domain/codomain realization in
valid contexts, without an externally supplied extensional fiber family.
Native denotation has not yet been translated to a bounded formula, and
general conversion/coherence and full typing soundness remain open.

`InterpretedContexts.v` defines context validity structurally and proves
valuation extensionality, context lookup, and sort/variable realization.
`RuleRealization.v` composes explicit semantic witnesses for the product,
lambda and application rules; application uses the original substituted
codomain. This is not yet the full typing induction: existence/coherence of
the witnesses and semantic preservation of syntactic conversion are open.

`SyntaxRenaming.v` and `SyntaxSubstitution.v` prove transport of original
Typing.typ derivations. `Denotation.v` defines a type-directed relation over
the unchanged syntax and proves valuation extensionality, renaming,
simultaneous substitution and single-variable substitution. `DenotationBeta.v`
connects a matching-witness redex and its actual syntactic reduct to the same
semantic value, with semantic typing premises explicit. Denotation totality,
coherence, general conversion and typing soundness remain open; the relation
does not assume semantic membership as part of its definition.

`GlobalOperations.v` defines rank-independent typed product, abstraction and
application operations. It proves their typing, beta law and congruence under
equal semantic domains/fibers/arguments. The global selector requirement has
an existence theorem from family choice; the construction is not a model
record assuming soundness. Since application syntax is unannotated, a typed
syntax relation now exists; its totality and conversion/coherence proof are
still needed.

`GlobalCodeChoice.v` uses a supplied transitive tower envelope to bound one
candidate set independent of typing ranks. One set-coded selector works for
all ranks; strict cardinal growth proves each selected code belongs to every
universe justified by the source cardinal bound. Global code/bijection
projections are extensional in the semantic source set. This removes the
rank dependence of the earlier fixed-rank selectors. Hierarchy existence,
the first-order construction audit and original PTS soundness remain open.

`SelectedCodes.v` defines extensional projections of the selected pair and
proves the selected code is in its universe and its selected graph is the
required bijection. It proves the coded beta law and fixed-rank congruence
under equality of decoded domains and extensional fiber families.
`ProductExtensionality.v` supplies the dependent-product congruence proof.
These are not yet the original PTS substitution/typing soundness inductions.

`CodeWitnesses.v` retains the code and coding bijection in each witness and
certifies its predicate in bounded formula syntax. Its witness sets are
nonempty under the explicit cardinal/choice principles and rank bounded.
`uniform_product_code_choice` supplies one set-coded selection operation for
all typed products at fixed ranks m,n. GlobalCodeChoice and SelectedCodes
now supply rank independence and semantic extensionality respectively;
syntactic substitution compatibility remains open.

`ProductWitnesses.v` connects product coding to the bounded eligible-bijection
sets: they are nonempty under the explicit cardinal/choice premises and lie
in carrier (13 + max(m+1,n)). Their target family equals a bounded decoding
range. A generic graph-selection lemma for extensional set-indexed families
is also proved. This is not yet a coherent choice of product codes or PTS
soundness; the weak-foundation obligations remain explicit.

`FiniteClassification.v` constructs graph bijections from injective finite
enumerations, compresses subsets of a finite carrier, and proves that a set
embedding into finite_carrier n is equinumerous with finite_carrier m for
some m <= n. The subset/embedding classifications take excluded middle
explicitly; no GCH or choice premise is used. This does not yet prove the
finite/countable dichotomy on its own. The image separation and
Type-indexed finite graph still require the first-order foundation audit.

`CountableDichotomy.v` constructs the finite/countable dichotomy from explicit
family choice and excluded middle, choosing from nonempty subsets of X.
The countable injection is an actual set graph. Its native recursion and
sup nat construction still need a first-order bounded-existence proof.

`CardinalClassification.v` combines this dichotomy with classification along
the powerset hierarchy. `decoded_product_code` obtains a code for every typed
decoded product under explicit family choice, generic comparability, the
infinite-powerset-gap principle and excluded middle. These are theorem
premises, not new global axioms or a derivation of them in BZC+GCH.
Uniqueness of the infinite carrier index follows without these premises.

`BoundedComparison.v` gives an explicit bounded formula for the least closed
region in Schroeder--Bernstein and proves that separation by this formula
produces the existing region. The closure condition uses bounded graph
applications in place of function symbols. This certificate itself requires
only the two supplied injections, without excluded middle. The final
comparison theorem still has its explicit classical-logic premise. The
successor subset and glued graph also have bounded-formula certificates and
extensional equality proofs. `bounded_comparison_bijection` proves that the
formula-separated graph is a bijection, with excluded middle explicit.

`CantorBernstein.v` constructs a bijection from two opposing graph injections.
It uses a least closed region defined within A and Power A, avoiding collection
of a sequence of iterates. The final theorem has classical excluded middle
as an explicit premise; no global classical or choice axiom is imported.
Its three separation predicates are certified by BoundedComparison; imported
constructions and first-order derivability still require audit. This proves cardinal comparison infrastructure,
not the missing GCH classification or PTS soundness theorem.

`CartesianMaps.v` and `PowersetSquares.v` prove Cartesian-square absorption
at every finite powerset level, using distinct tags to encode two subsets.
They derive the actual decoded dependent-product bound at max(m+1,n), without
GCH, choice or supplied fiber injections. These are powerset representatives:
GCH classification is still needed to find an equinumerous available cardinal
code, followed by coherent bijection selection and original PTS soundness.

`CountablePairing.v` constructs a set-graph bijection from the Cartesian
square of omega_codes onto omega_codes, using the checked natural-number
Cantor pairing and its inverse. This establishes the countable base for
Cartesian cardinal estimates; no GCH or choice premise is needed.

`BoundedBijections.v` gives bounded first-order formulas for graph bijections
and eligible coding witnesses. The bijection formula is equivalent to the
existing definition, including exclusion of non-pair graph elements. Eligible
witnesses are separated from an explicit Cartesian product; the graph bound
omits no bijection and the witness set lies within eight powerset steps under
the stated carrier bounds. Nonemptiness for cardinal targets remains unproved.

`SuppliedHierarchy.v` proves closure and containment results for a supplied
union of finite powerset levels, including the concrete decoding graph.
Its membership characterization is an explicit premise; existence and
identification with V_{omega+omega} remain foundation obligations.

`CodeHierarchyBounds.v` connects the concrete code universes to the rank
bounds. The numeral carrier is transitive; every U_i is a subset of it, and
every decoded member of U_i is a subset of carrier i. The concrete decoding
graph is typed into the existing dependent product and has rank at most
carrier (i+5). These are checked Ens bounds for the current code encoding,
not a proof that the hierarchy or the graph exists in BZC.

`BoundedProducts.v` reconstructs dependent function spaces for set-coded
families using a five-variable bounded formula for totality, fiber membership,
and uniqueness. It proves equality with the existing dependent_product when
the supplied family graph maps A into P(W). The definition uses only a
bounded predicate separated from P(A x W), with no indexed family_range or
arbitrary family function. Four new assumption reports are closed. This
does not yet provide the family graphs or cardinal-coding bijections needed
for the model's soundness theorem.

`BoundedFamilies.v` replaces the indexed range constructor for set-coded
families by separation from a powerset using an explicit bounded formula.
It proves equivalence with the previous range for typed family graphs, and
bounds the resulting range and its union. Five new assumption reports are
closed. Existence of the input family graphs and bounded reconstruction of
the function-space predicate remain obligations.

`HierarchyBounds.v` proves explicit finite rank overhead for the existing
encoding over any transitive ambient set W: ordered pairs belong to P^3(W),
Cartesian products are subsets of P^3(W), family ranges belong to P^2(W),
graphs to P^4(W), and dependent function spaces to P^5(W), under the stated
domain/fiber bounds. The function-space bound holds uniformly at level n
with overhead five. All eight new assumption reports are closed. These
are bounds on the current Ens constructions, not yet their reconstruction
by bounded formulas or the existence/assembly of V_{omega+omega}.

`SetFunctions.v` constructs dependent function sets as separated subsets of
actual powersets of Cartesian products. Graph abstraction, relational
application, beta computation, application uniqueness, and emptiness in the
presence of an empty fiber are proved using the library's `Ens`, `EQ`, and
`IN`. In particular, function existence is not a postulated model field.
The proofs require explicit extensionality of the supplied set function.

All five printed assumption reports are `Closed under the global context`.
The selected upstream subset has no choice or GCH axiom. The original full
library also exposes choice/collection results as conditional statements;
do not silently turn those conditions into unconditional facts.

`SetApplication.v` extends this foundation with a total, choice-free set
operation `apply_set g x`. It separates the possible values from a concrete
set bound and takes their union. The library's ordered pair is
`{{x},{empty,{y}}}`, so **three** unions of the graph bound its values.
No witness is extracted from an existential in Prop and no choice axiom is
needed. The following results are checked:

- `apply_set_extensional`: equal graphs and arguments give equal results.
- `apply_set_beta`: applying `graph A f` to an element x of A gives f x.
- `apply_set_typed`: a dependent function applied within its domain belongs
  to the corresponding fiber.
- `apply_set_spec`: that result is related to the argument by the graph.
- `apply_set_eta`: rebuilding a dependent function from its values gives
  the same set graph.
- `dependent_product_extensionality`: pointwise-equal dependent functions
  are equal as sets.

All six additional `Print Assumptions` reports are closed. Set-level eta
does not add an eta-conversion rule to the PTS. This operation interprets
application of ordinary graphs; application of the paper's **cardinal-coded**
functions additionally requires the still-missing inverse coding bijections.

`CodeUniverses.v` constructs the countable universes themselves. Codes for
finite carriers, infinite carriers and sorts are distinct sets, using tagged
singleton numerals. `U_i` contains every finite code, every sort code, and
exactly the infinite codes with index at most i. Membership, monotonicity,
strict growth, and an explicit natural-number enumeration are proved.

Decoding `El` is defined on arbitrary sets, without deciding set equality:
union the values of all matching codes. Injectivity of code representations
makes the matching value unique up to set equality. `El` is extensional and
has the specified value on every code. Finite carriers are explicitly
constructed finite sets; sort codes decode to the constructed `U_j`.
The sort-axiom membership `s_i in El(s_0)` and emptiness of the ordinary
dependent function set over `El(s_j)` with fiber `El` are proved.

**Boundary:** the infinite carriers remain an explicit parameter
`nat -> Ens`, with no cardinal properties assumed. They are not yet proved
to be the finite-index aleph hierarchy. The decoded-product emptiness result
is not the denotation of the PTS Bottom term: product coding and the term
interpretation still need construction. All ten new assumption reports are
closed; printed theorem types expose the carrier parameter.

`SetBijections.v` defines bijections using the constructed function sets and
relational injectivity/surjectivity. It constructs the inverse graph by
separation from a Cartesian product, proves its typing and bijectivity, and
proves both evaluation round trips. Identity and composition graphs give
reflexivity, symmetry and transitivity of set equinumerosity. All nine
assumption reports are closed. No choice is needed to invert a given bijection.

`CodedFunctions.v` proves the local laws for encoding a dependent function
graph through a **supplied** bijection to a carrier K. Encoding abstraction
lands in K; decoding lands in the dependent function set; coded application
has the right fiber; coded beta evaluates to the body. An empty fiber forces
K itself to be empty. All six assumption reports are closed. These theorems
expose the ordinary bijection premise and prove the local laws from it;
they do not assert existence or coherent selection of the manuscript's
cardinal-coding bijections and are not a replacement for PTS soundness.

`ProductEmbedding.v` proves the first step of the product-cardinality bound.
Given an extensional family of concrete injections from B(x) into a common
carrier K, it constructs an injection from the dependent function set into
the ordinary function set from A to K. Function-graph extensionality proves
injectivity of the constructed map. A version taking a set graph of fiber
injections derives extensionality from `apply_set`; no extra extensionality
axiom or premise is needed. All seven new assumption reports are closed.
This does not choose the fiber injections, build alephs, or prove the GCH
exponent bound. Those parts of the cardinal argument remain outstanding.

`CountableCodes.v` strengthens countability to an actual set-graph bijection
between every `U_i` and `omega_codes`, the set of singleton numerals. It
uses a repetition-free numbering: first the i+1 permitted infinite codes,
then alternating finite and sort codes. Injectivity, surjectivity, function
typing, forward evaluation and inverse round trip are proved. Finite
carriers inject into `omega_codes` as well.

With the rank-zero infinite carrier fixed to this concrete countable set,
`rank_zero_decoding_bound` proves that **every** code in `U_0` decodes to a
set injecting into it. Higher carriers are still arbitrary parameters; the
result is not the all-rank cardinal bound. All ten new assumption reports
are closed. This countable representative is not asserted to be a von
Neumann initial ordinal; no uncountable aleph construction is claimed.

`CardinalGrowth.v` proves Cantor's theorem constructively: no set admits an
injection from its powerset. It also constructs the singleton injection,
proves transitivity of set injections, and proves strict growth of finite
powerset iterations. All seven assumption reports are closed.

`CardinalHierarchy.v` instantiates the formerly arbitrary infinite carriers
with `carrier i = iterated_power omega_codes i`. It proves monotonicity,
strict growth, and the uniform bound
`IN a (U i) -> embeds (decode a) (carrier i)` for **all ranks and all codes**.
The concrete sort axiom and decoded-product emptiness follow as well. All
seven new assumption reports are closed; there are no carrier assumptions.

These are powerset-iteration representatives, not yet proved to be the
finite-index alephs. This is not a replacement model in which product
closure is ignored: the development still has to prove the GCH cardinal
classification/exponent bound and provide an exact code and coherent
bijection for each dependent product. In particular, the existence of these
strictly growing carriers alone does NOT prove PTS soundness.

`PowersetEmbedding.v` constructs direct images and proves that an injection
A -> B induces an actual graph injection P(A) -> P(B). It also proves
inclusion gives a set injection and records the graph powerset bound for
dependent function sets. Six new assumption reports are closed.

`SubsetFunctions.v` encodes a function A -> P(B) by the subset of A x B
consisting of its membership pairs. It proves extensionality and injectivity
of this construction. Combined with the fiberwise product embedding, this
gives an injection of a dependent product into P(A x K) whenever a set graph
supplies injections of its fibers into P(K). These supplied injections are
explicit premises, not assumed product bounds. Six new reports are closed.
Cartesian-product cardinal estimates and exact cardinal-code classification
are still needed; no GCH or final PTS soundness result is claimed here.

Build from the repository root:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer ZFC_model/PowersetEmbedding.vo ZFC_model/SubsetFunctions.vo ZFC_model/CardinalHierarchy.vo ZFC_model/CodedFunctions.vo
```

## Not yet a model or a soundness proof

The paper's actual model uses distinct cardinal codes and sort codes, with
`El(c_kappa)=kappa` and `El(s_j)=U_j`. Its remaining requirements include:

- the finite-aleph cardinal hierarchy and a precise GCH premise;
- the bound on dependent function cardinality at `max(m+1,n)`;
- a coherent selection of coding bijections, independent of rank bounds;
- interpretation of contexts, annotated terms, substitution and beta equality;
- soundness for the unchanged `Typing.typ`/`Ranks.RankSorts` judgment;
- specialization of the empty-fiber theorem to the interpretation of Bottom.

None of those missing results is asserted as an axiom or hidden inside an
assumed model record. In particular, `dependent_product_empty_fiber` is NOT
yet a theorem that PTS Bottom is uninhabited. No complete model or soundness
commit is claimed by this foundations checkpoint.
