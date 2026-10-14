# PTS-rk set-model development — incomplete

Reference: the set-theoretical model section of `latex/paper.tex`.
Dependency: the pinned LGPL subset of rocq-archive/zfc in `vendor/zfc`.

Current foundation target: reformulate this model in BZC + GCH + existence
of V_{omega+omega}, bounding constructions in the supplied hierarchy and
eliminating unbounded separation, then finish its soundness proof. Only
afterward pursue an interpretation in BZC + GCH without that existence
assumption. See [FOUNDATIONS.md](FOUNDATIONS.md) for the ordered milestones.
Neither is established by the current Rocq assumption reports.

The first syntactic foundation audit is implemented in `BoundedFormulas.v`
and `BoundedInverse.v`: ordered pairs/application have explicit bounded
first-order formulas, and the inverse graph is proved equal to separation
by a bounded formula. This checks a specific predicate, not all of BZC
soundness or the strength of the Ens representation.

## Checked construction

`CantorBernstein.v` constructs a bijection from two opposing graph injections.
It uses a least closed region defined within A and Power A, avoiding collection
of a sequence of iterates. The final theorem has classical excluded middle
as an explicit premise; no global classical or choice axiom is imported.
The predicates still need certificates in the bounded formula syntax for the
first-order foundation audit. This proves cardinal comparison infrastructure,
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
