# Read-only QIIRT comparison

Reviewed all 500 lines of current Combinatory.agda and the new normal-family,
comprehension, products, inference and context sources. This is an endpoint
checklist, not a new interpretation proof. The final full Examples closure
passed safe fresh checking, including every Products/Contexts endpoint.

## Direct correspondence

- Sub's identity/composition/associativity, terminal uniqueness and
  comprehension beta/eta/pair-composition are realized by actual SubNF paths.
  The direction convention is reversed: QIIRT Sub Γ Δ replaces Δ variables
  in Γ; native SubNF Γ Δ replaces Γ variables in Δ.
- Ty's identity/composition and dependent Pi naturality have normal-family
  analogues. Products now also supplies universe naturality and ElNF, whose
  decoding is definitionally the same NfAt fibre, and El naturality.
- Tm identity/composition are proved with typed transport. Pairing gives
  beta-snd. The application naturality target is an actual typed path with
  smart castNF; this is stronger than only subject equality.
- Normal carriers' setness follows from discrete original terms and
  propositional certificate fibres. No analogue of setTm-guarded or an
  equation constructor is required inside their definitions.
- NormalizedInference computes a unique normal type/rank from mere original
  typability, proves its fibre isomorphic to the typed normal carrier, and
  preserves/reflects original beta. Its type-check decision is conditional
  on already having a typable subject; it is not raw typability decision.

## What a literal QIIRT interpretation still needs

- Package all operations under one context/substitution convention and give
  the actual recursion/elimination interpretation, checking every constructor
  and path. A collection of analogous native laws is not that interpretation.
- Prove the chosen target Con is a set for setCon; current normal Con is
  inductive-recursive with empty/extension and native decoding, not a context
  quotient. A normalization/adequacy map for arbitrary original well-formed
  contexts is also needed if claiming complete context coverage of this Con.
- Native realizations of the exact S/K/P families, their fixed application
  arities and beta-S/K/P paths, and every Template.Guards component. The
  current simply typed surface compiler does not supply dependent coverage.
- Package universe-term naturality and El-univ in the combined computed-type
  interface, along with derived structural guards and application spines.
  ElNF is literally identity, so El-univ is already definitionally available;
  this item concerns the literal QIIRT interpretation's typed boundary.
- For an equivalence rather than a model: original-source completeness,
  equality reflection and an appropriate initiality/normal-form theorem.
  Full dependent combinatory completeness is not implied by the algebra.

## Normal-form-first assessment

The checked carrier strategy genuinely removes quotient path elimination
from normal type/term/substitution operations. Pi and lambda smart constructors
are structural, while application normalizes its dependent result type and
subject. Coherence becomes ordinary uniqueness-of-normal-form proofs, not
new equality constructors. castNF transports only typing evidence and leaves
the subject definitionally unchanged; it agrees with Cubical transport.

This is not yet the requested simultaneous normal-syntax/hereditary-operation
IIRT: the actual computation still reuses the original native normalization
proof, retains binders/annotations, and context IR is only one component.
A new mutual presentation must independently pass positivity and termination
and then connect to these native semantics. Its total code economy has not
been demonstrated. Do not compare a 500-line QIIRT signature alone with the
normal algebra plus all imported native metatheory as if they had equal scope.

Context-comprehension eta here is not function eta. No full-system canonicity,
raw checking decision, binder-free algorithm, finite total model or internal
consistency proof follows merely from the checked normal algebra operations.

The final regression module genuinely computes dependent type substitution,
polymorphic identity's two applications and WF-free IR-context operations
by refl. The slow earlier full checks concerned dependency coherence proof
elaboration, not failure of these computational tests.
