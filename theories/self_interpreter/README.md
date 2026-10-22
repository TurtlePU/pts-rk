# Indexed PHOAS interpretation and folds

This library, `PTSrk.SelfInterpreter`, uses the original annotated
`Syntax.Term nat`, `Typing.typ`, `Ranks.RankSorts` and beta conversion.
It adds no primitives, cumulativity, eta, or axioms. The
[research note](../../PTS-rk_self_interpreter.tex) and
[PDF](../../PTS-rk_self_interpreter.pdf) state the mathematics; the
[obligation ledger](OBLIGATIONS.md) records precise remaining goals.

## Public interfaces

The current organization separates **folding**, **quotation**, and
**fidelity**. A dependent algebra is an actual originally typed filling of
a finite dependent telescope. Both represented types and represented terms
are interpreted by application to that same filling. This is an original
PTS application spine, not a Rocq recursor masquerading as an internal fold.

- `Algebra`: shared typed-algebra/fold interface, specialization, substitution
  and conversion laws.
- `GenericFold`: an actual normal operator `lambda P. lambda Q. lambda Sig.
  Q Sig`, with no selected filling built into it. The algebra fields are
  ordinary arguments. Typing and beta computation hold for every correctly
  typed filling of the fixed signature; no eta conversion is used.
- `UnifiedAlgebra`: executable full-source type and term programs without
  the raw HOAS envelope; their normality, identity interpretation, literal
  recovery and original result typing.
- `PHOASFold`: specialization of the existing intrinsically faithful
  simply typed PHOAS codes; alternative interpretations are genuine typed
  fillings, not new traversals of the source derivation.
- `PHOASCPS`: continuation-carrier and handler analysis in the original
  calculus. Its exact checked boundary is stated in the note.
- `CombinatoryFold`: normal, intrinsically faithful, numeral-free Church
  codes and internal folds for variable-free trees over a finite atom bank.
  Its checked CBV continuation algebra and constructor observer consume the
  same rank-correct code. `CombinatoryAlgebra` proves exact agreement with
  the shared fold. This connects to `PTSrk.Combinatory`; it is not a complete
  dependent bracket-abstraction compiler.
- `FullDependentInterpreter`: compatibility API retaining arbitrary
  annotated-source syntax injectivity through its separate raw HOAS tag.
- `CappedDependentInterpreter` and `FragmentClosureInterpreter`: full
  quotation-budget fragment coverage and one fixed execution head per fragment.

A common **API for algebras** does not identify different finite signatures.
The full-dependent signature still depends on its numerical equality plan.
One rank-only constructor algebra with independent nonidentity realizations
remains open. The code-carried runner in the fragment closure is likewise
not such an algebra.

## Full dependent quotation

`UnifiedAlgebra` obtains normal programs
`P : Pi Sig.C_s` and `q : Pi Sig.El_s(P Sig)` from independent
`FullSource` derivation data. The constructed identity algebra gives
literal recovery of the unreduced source term and type. No source value is
pre-normalized; no raw HOAS tag or Church numeral is passed to this evaluator.

The implementation behind this interface is:

1. `FullSource`, `SourcePruning`, `SourceValidity`, `SourceClosure`:
   independent six-rule data, harmless conversion pruning and open closure.
2. `TarskiSignature`, `ScopedTarski`, `TarskiBinders`:
   dependent codes, universes, products, casts and normal annotated binders.
3. `CheckedEqualityFields`, `CheckedContextualFields`,
   `NormalEqualityFill`: finite checked laws and independently constructed
   normal identity witnesses.
4. `QuotationTree`, `QuotationCache`, `QuotationViewSubstitution`,
   `LocalCodeAlignment`: finite constructor views and repair infrastructure.
5. `RecursiveQuotation`, `FullQuotation`, `ClosedQuotationPackage`:
   structural quotation, plan construction and closing.
6. `DependentProgramDecoder`, `GenericFold` and the shared algebra interface:
   ordinary type/term arguments and actual typed specialization.

The equality allocator checks ORIGINAL typing and filled endpoint conversion.
It never assumes target quotation or accepted-proof soundness. Application
uses two repairs and finite view substitution; it does not recursively quote
a newly synthesized derivation. All lambda annotations are retained.

### Fidelity without tags: what is established

The existing simply typed PHOAS quotations have intrinsic structural erasure:
`PHOASFaithful` and `PHOASPackage.quote_conversion_injective` recover
literal annotated syntax without an auxiliary tag. The new combinatory codes
likewise retain their own tree structure.

For the full dependent payload, the tag-free interface proves conversion
reflection for codes evaluated under a common algebra. For normal source
terms this gives literal injection. It does **not** prove literal injection
for arbitrary reducible sources or arbitrary distinct plans. Strong recovery
alone cannot do that: two distinct beta-equivalent sources may have a common
reduct.

The faithful compatibility API is therefore retained. Eliminating its tag
while preserving its stronger contract requires a structural decoder for the
actual generated dependent payload, stable under repairs, binders and
signature insertion. `QuotationTree` is external metadata, not that decoder.
No impossibility theorem for intrinsic dependent fidelity is claimed.

## Rank bounds and fragment execution

The source fragment at k bounds the pruned derivation's quotation budget,
including formation ranks and universe literals; source size is unbounded.
The capped quoter maintains its local rank invariant through every rule.
Its actual interpreter type-sort is at most `max(k+7,r+6)`, independently
of plan length, for fidelity-tag rank r.

`FixedInterface` uses
`Code_a(T) = (Pi A:U_a. A -> (A -> T) -> T) -> T`.
A closure carries a normal hidden-domain program and a normal runner;
evaluation computes their application. `RankPadding` supplies exact common
sorts without cumulativity.

`FragmentClosureInterpreter.every_bounded_original` fixes k BEFORE the
source. Its normal head has type-sort k+10 and its ordinary spine is
`head k (Pad_k(nf T)) code (rank_value k)`. The whole expression has the
literal original type T and reduces to t. Only T is externally normalized.
The final force is typed using the supplied padded function shape, not a
generic eliminator for arbitrary types. The compatibility codes retain
cross-budget syntax injection.

`PlanNonuniformity` shows that the current allocator's plan length is
unbounded even at fixed small ranks and even for a fixed final judgment.
`FiniteCoherenceCatalogue` excludes exhaustive finite lists of concrete
equality fields, not finite generic law schemes.
`RankObstruction` excludes a single all-rank typed application head.
None of these results rules out a better rank-indexed algebra.

## Numerals, combinators and consistency

Numerals are not needed for the dependent fold itself: the external plan
selects a finite telescope, whose fields are ordinary terms.
`FiniteLiteralBank` and `PTSrk.Combinatory.ChurchFinite` offer finite
selectors when an object-level atom choice is needed. `NumericLiteralBank`
is an optional saturating Church-numeral adapter, not a prerequisite.

`CombinatoryFold` factors variable-free syntax into atom leaves and
application nodes. Its homogeneous target typing is not a source-type-indexed
dependent interpretation. The combinatory development separately proves
soundness of its Hilbert catalogue and extraction from its own derivations;
full original-source completeness and the general dependent abstraction
compiler remain open. The new fold does not fill those gaps.

For internal consistency, the missing theorem is internal reification from
an INDEPENDENT accepted-certificate predicate, including arbitrary admitted
trace witnesses and resource bounds. An external Rocq quoter or a finite
code-to-code normalizer does not supply it.
`FixedInterface.inhabited_iff` makes the boundary explicit:
producing `Code(Bottom)` already carries the soundness content.
See [self_consistency](../self_consistency/README.md).

A fixed literal alphabet cannot create new universe literals by beta
reduction (`BudgetInternalization`). This limits unbounded literal
unquotation from numeral-only data; it does not rule out fixed fragments,
finite structural codes, or Bottom-specific internal soundness.

## Supporting developments and evidence

The older shallow, raw-HOAS, canonical-normalization and contextual-law
modules remain as checked support and regression material. They are not
alternative promises made by the new public API. Their public declarations
remain available; no compatibility theorem has been deleted.

The fixed-rank normalizer's operation-cost bound is
`tower (2*d+1) (nodes t+5*d+2)`. The manuscript's general elementary-function
compiler is not a Rocq theorem. That independent numeric route is not a
premise of the constructed PHOAS interpreter.

The full source quoter's sort-path extraction test succeeds; lambda and
application probes previously reached a 30-second timeout. Mathematical
coverage is not evidence of practical non-leaf compiler performance.

Use the [pinned toolchain](../../docs/DirectR-CI.md):
Rocq 9.2, Stdlib 9.1, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1.

```sh
opam exec -- dune build @theories/self_interpreter/audit
opam exec -- dune build @theories/self_interpreter/fold-audit
bash tools/build-self-interpreter-note.sh
```

Fresh assumption reports require a fresh absolute Dune build directory.
Verification records under `docs/direct-r-handoff/verification` distinguish
the current scoped audit from earlier full-repository CI. See the newest
handoff entry for exact commands, failures, hashes and remaining goals.
