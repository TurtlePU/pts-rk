# Foundation audit of the existing sound model — 2026-10-14

This is a source and mathematical audit, not a new Rocq theorem deriving
the model in material BZC. The original semantic soundness theorem is
proved. Its reduction to BZC remains a distinct, unfinished formalization.

## Verdict and the meaning of GCH

The supplied-hierarchy version has the required set bounds in BZC + GCH +
existence of V_(omega+omega). No need for Replacement or an additional
V_(omega+omega+omega) has been identified. Finishing the reduction also
requires a bounded definition of denotation and a translation of the proof;
the current native Ens proof does not supply those automatically.

BZC + GCH alone does not guarantee the collected envelope used by THIS
set-sized construction. This negative conclusion concerns the injection-gap
form of GCH used in CardinalClassification.v. It does not rule out a class
interpretation of PTS-rk, a different coding, or a different axiom called GCH
that already includes stronger set-existence assertions.

The convention for BZC is classical first-order set theory with
Extensionality, Empty Set, Pairing, Union, Power Set, von Neumann Infinity,
Foundation, bounded Separation, and ordinary set-indexed Choice. The actual
formulas are in MaterialZermelo.v. This agrees with the convention in
[Shulman's talk, slide 7](https://home.sandiego.edu/~shulman/papers/uqsatalk.pdf).

Write A <= B for existence of a set-graph injection and A ~ B for a
bijection. The GCH consequence actually consumed by the construction is:

    omega <= K, K <= X, X <= Power K
      ==> X <= K or Power K <= X.

Together with cardinal comparability and Schroeder--Bernstein this says
that no cardinal lies strictly between an infinite K and Power K. Ordinary
Choice supplies comparison using well-order relations; collapse of every
well-order to a von Neumann ordinal is unnecessary. A formal derivation of
this comparison in the repository's BZC deduction system is still missing.

In weak theories, do not silently replace this GCH statement by a statement
asserting that every set has an initial-ordinal cardinal and that all
successor initial ordinals exist. Those existence assertions are not part
of the definition above. The failure of ordinal representatives in Zermelo
set theory is explained in
[Panagiotopoulos, Theory of Sets, section 13](https://www.mat.univie.ac.at/~panagiotopoulos/SetTheoryI.pdf).

## Why the extra collection does real work

This argument is in an ambient ZFC + GCH metatheory; it is a relative-model
argument, not a new theorem already checked in Rocq.

Let lambda = omega+omega and M = V_lambda. The membership structure M
satisfies Zermelo set theory, Choice and Foundation, hence BZC. The standard
rank-initial-model argument is also described in
[Theory of Sets, Exercise 4 and Corollary 5](https://www.mat.univie.ac.at/~panagiotopoulos/SetTheoryI.pdf).
The following extension to the precise GCH convention is an audit argument:
for A,B in M, all their subsets and all set graphs between them have ranks
below lambda. Their powersets and injection/bijection witnesses are thus
the same internally and externally. Ambient no-intermediate-cardinal GCH
therefore holds in M too.

The existing singleton-numeral omega_codes has rank omega. Consequently

    rank(carrier n) = rank(Power^n omega_codes) = omega+n.

SuppliedHierarchy.envelope_carrier proves that every carrier n is a MEMBER
of any supplied envelope H. Such an H has rank at least
sup_n(omega+n+1) = lambda, so H cannot be a member of M. In particular M
satisfies the specified BZC + GCH but lacks the envelope needed to
instantiate the present sound_model_exists theorem. The global decoder,
whose values include every carrier n, has the same collection obstruction.

Thus one cannot justify this construction merely by observing that each
fixed finite powerset iterate exists. This argument does not show that
existence of the full V_lambda is the weakest possible extra axiom. A
suitable collected powerset envelope is the actual parameter in the code.

## What supplying V_(omega+omega) buys

Take W = V_omega and H = V_(omega+omega). Then W is transitive, contains
omega_codes, and H is the union of the finite powerset iterates of W.
These are exactly the three supplied-hierarchy premises of ModelSoundness.
The hierarchy-existence statement must assert the actual hierarchy, not
just the existence of the ordinal omega+omega or of each individual level.

The existing checked bounds cover the following operations uniformly:

- Code universes U n are countable subsets of omega_codes. Finite carriers,
  carrier n, and every decoding at rank n occur in H.
- The actual ordered-pair encoding costs three finite powerset levels;
  graphs and dependent products cost finitely many more. The bounds are
  uniform formulas in the rank index, not finite example tests.
- The full decoder is bounded by Power H. The bounded decoder agrees with
  the original all_decoding_graph for every code.
- Put F = Power(H x H) and X = all_codes x F. All eligible coding witnesses
  lie in X. A selector on the nonempty subsets of X is an ordinary Choice
  function bounded by Power((Power X) x X). No class Choice is required.
- Finite valuations can be represented by graphs in Power(omega x H).
  Syntax, contexts and finite syntactic derivations admit natural-number
  codes. Their uniformly collected relations can be bounded using products
  and finitely many powersets of these fixed sets.

Global data need not be elements of H. BZC can form Power H and further
fixed finite products/powersets after H has been supplied. There is no need
to collect another omega-sequence of hierarchy levels above H.

The checked supporting modules are HierarchyBounds, SuppliedHierarchy,
BoundedFamilies, BoundedProducts, BoundedBijections, BoundedIteration,
BoundedRecursion, BoundedChoiceSequence, BoundedDecoder,
BoundedDecodedSelection, and BoundedModelData. Their current semantic
equivalence proofs are in Ens, not derivations from the BZC axioms.

## Remaining separation and proof-translation obligation

The exact live issue is BoundedChoice.relation_candidates:

    relation_candidates B P x := Comp B (P x).

DenotationChoice.denotation_family_choice and PairedChoice instantiate P
with native denotation predicates. No Bounded.Formula for those predicates
is currently supplied. Likewise the original native graph/family_range
definitions accept Ens-valued Rocq functions. A bound for their outputs
does not certify these constructions in material BZC.

There is a concrete bounded construction to formalize, rather than a need
to assume arbitrary-predicate separation. First encode the relevant
judgments (syntax, context, valuation and value) in a fixed set J, using
the bounds above. Encode type families and body functions by set graphs
in Power(H x H), and express the original denotation rules as positive
closure conditions on R subset J. With these bounds, all quantifiers in
the closure predicate range over fixed sets, including Power J. Then the
least closed relation can be defined by bounded Separation:

    D = {j in J | forall R in Power J, Closed(R) -> j in R}.

For a positive bounded rule operator, the intersection is itself closed:
premises in D hold in every closed R, so each conclusion belongs to every
such R. This also gives the usual induction principle for bounded
properties. It avoids collecting an unbounded sequence of approximation
stages or a set of all denotation derivation trees.

This is a mathematical construction method, NOT a checked instantiation
for Denotation.denotes. The work still required is the actual bounded rule
formula, syntax/valuation coding, equivalence on original typed valid
valuations, and translation of the soundness and normalization arguments.
Bounding the Coq inductive declaration by fiat would not prove that
equivalence. BoundedFormulaSelection.bounded_formula_set_choice becomes
applicable only after this predicate certificate has been supplied.

Therefore the audit supports the hierarchy-augmented theory as the target
for this same construction, but does not upgrade the present Rocq results
to a completed BZC theorem. Neither the ordinal-collapse issue nor this
remaining denotation certificate may be hidden in a new axiom.

## Verification for this audit

HEAD c91f9564856a2a94afb7e2d55432693ae2d92bf0. Proof sources unchanged.
The targeted baseline build exited 0 (cached). A newly executed compiler
audit printed the full theorem types and 14 closed Print Assumptions
reports, exit 0. This verifies the existing supplied-parameter theorems;
it does not prove the foundation reduction. Commands and raw logs are in
docs/direct-r-handoff/verification/bzc-foundation-audit-2026-10-14/.
