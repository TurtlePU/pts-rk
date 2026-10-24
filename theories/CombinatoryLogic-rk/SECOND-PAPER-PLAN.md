# PTS-rk, second paper: presentations and bounded self-interpretation

Status: research targets and staged plan, not new formal results.
This update changes documentation only. Do not start implementing the stages
until requested. Preserve the original annotated PTS, beta-only conversion,
rank discipline and typing judgment throughout.

## Six deliverables

The first three deliverables should culminate in three principal Agda source
files. Provisional module names below are design labels, not existing files.
Shared proof libraries may remain, but report the whole dependency footprint:
three wrappers around the present experiments are not an economy result.

| Deliverable | Required interface and result |
| --- | --- |
| 1. `PTSNatural` | Intrinsically typed, binder-free natural-model QIIRT for full PTS-rk; `Con`, `Sub`, `Ty`, `Tm`, computed typing, equations, original-PTS adequacy, and a Church realization in PTS-rk. |
| 2. `PTSNormal` | Intrinsically typed, binder-free normal-form-first (Q)IIRT; recursive dependent application/normalization; closed beta-equivalent terms and types have definitionally identical canonical representations. |
| 3. `PTSFragments` | Cumulative rank/length-bounded indexed versions of (2); coherent embeddings, explicitly graded application, fixed-grade Church realization and extraction into native PTS-rk terms. |

4. A complete Hilbert-style logical presentation, with proofs as typed terms,
   the literal MM0 theory, and verified soundness/completeness correspondence.
5. Partial finite-fragment models, internal bounded soundness and an eventual
   PTS-rk proof of a specified sentence expressing absence of closed Void
   inhabitants, with the construction and correspondence verified in MM0.
6. An indexed PTS-rk self-interpreter supporting folds over source code,
   demonstrated by a typed CPS translation as well as evaluation.

These are six goals; the finite-fragment hierarchy and finite-model soundness
are related but distinct deliverables. A graded finite syntax carrier is not
automatically a finite first-order model under all valuations.

## Shared contract and design decisions

- **Original calculus.** Native expansion retains lambda annotations and
  original typing. No new primitives, eta, cumulativity or replacement typing
  relation. Cumulative fragment embeddings do not change universe rules.
- **Binder-free.** The three computational presentations have no object-level
  lambda abstraction constructor. Context extension and contextual codomains
  remain available. A source/native adequacy map may mention binders, but the
  normal-form evaluator itself should not rely on lambda expansion.
- **Definitional equality.** For concrete closed beta-equal inputs, the public
  normal representations and normalized type indices must reduce to the same
  Agda expressions without a supplied equality proof or cast. Prove general
  beta soundness/reflection separately. Quantified symbolic equalities remain
  mathematical propositions, not new Agda conversion rules. Equality of code
  projections alone is weaker than equality of whole proof-bearing values;
  the representation must resolve that distinction rather than silently
  dropping the stronger target. Test differing typing/conversion histories.
- **Intrinsic Church realization.** Specify the encoded sorts, rank of each
  interface, constructors, operations, typing evidence and treatment of paths.
  Raw Church trees do not encode a quotient or its dependent eliminator
  automatically. Distinguish a uniform code type from any rank-indexed
  decoding/fold interface; prove whatever uniformity is actually claimed.
- **Uniform complexity boundary.** The intended contrast is unrestricted
  external normalization versus fixed-grade internal normalization. Establish
  the non-encodability of a single fixed-rank uniform normalizing interface
  under explicit representation, decoding and cost assumptions. TOWER-hardness
  of conversion alone is not this theorem; apply-and-normalize needs its own
  reduction if a completeness claim is made. The repository checks the STLC
  reduction and operation-cost upper bounds, not the external hardness theorem
  or a machine-level complexity separation.
- **Source observability.** Keep quotation of intensional source syntax
  distinct from canonical semantic values. Arbitrary source folds need not
  descend through beta equality. A fold on the quotient must validate its
  equations; otherwise use retained source codes and prove semantic adequacy.

## Resource-indexed contract

Use a grade containing a whole-input rank budget `d` and an annotated-size
budget `N`. State exactly which internal type/formation ranks are bounded,
including contexts, codomains, annotations and combinator instantiations;
derive the semantic redex-head bound required by normalization. For bounded
proof soundness, bound every certificate and conversion-witness component
too. Neither outer type rank nor the largest visible numeral alone suffices.

Bound universe/rank literals as part of `d`, or expose a separate finite
alphabet parameter with coherent inclusions. Fixed rank and node count with
unrestricted universe labels still give infinitely many codes. Size must
account for all annotations and encoded index payloads. Translate the existing
native-node estimates to the selected combinator encoding before reusing them.

For grades `g ≤ h`, construct embeddings preserving types, interpretation and
normalization, with identity/composition laws. Define application at a proved
output grade `AppGrade(gf, gx)`, accounting for subject and dependent result
type, rather than pretending that a fixed length bound is closed under
application. Exact-length fibres may be auxiliary; cumulative carriers use
length at most `N`. Cover each finite native input at an effectively found
grade, and prove native extraction commutes with embeddings and application.

For each fixed grade, generate actual PTS-rk types and terms for the carrier,
normalizing application and extraction, with explicit target ranks and size
bounds. Separate extraction of a *native syntax code* from internal unquotation
to an inhabitant of the represented dependent type; the latter is a separate
typed requirement, not supplied by a finite lookup table alone. Fix the
intended interface and prove both bridges wherever claimed. Generated
fixed-grade families are not one internally quantified all-grade evaluator.

## Milestones and acceptance gates

1. **Freeze interfaces and theorem statements.** Fix the six deliverables,
   equality notion, substitution direction, grade and size measures, Church
   interfaces, extraction target, independent checker and consistency formula.
   Preserve the exact predicate-only target in the
   [consistency plan](../self_consistency/README.tex), unless a replacement is
   explicitly specified with a proved comparison. No implementation yet.

2. **Natural model and Hilbert/MM0 correspondence.** Complete original-PTS
   interpretation of the exact QIIRT constructors, dependent S/K/P templates,
   guards and paths. Prove context adequacy and original-source completeness,
   then equality correspondence and the promised Church realization. Connect
   the complete Hilbert theory with literal MM0 derivations. Acceptance means
   all schemes and rules, not selected closed examples or a new typing relation.

3. **Normal-first feasibility gate.** Prototype the fully dependent normal
   family and recursive apply-and-normalize together. Require positivity,
   termination, original typing, beta correspondence and closed definitional
   tests, including reductions inside types/annotations, polymorphic examples
   and distinct proof histories. Keep function eta distinct. Test the direct
   binder-free computation and compare total code/dependencies before replacing
   existing presentations. Do not substitute propositional paths for the
   requested definitional behaviour or hide normalization in quotient guards.

4. **Bounded cumulative models.** Restrict the successful interface from (3)
   to the explicit grades. Prove finiteness, coherent inclusions, coverage,
   graded application and normalized-type/extraction compatibility. Reconcile
   bounds for native nodes, combinator payloads and contexts. Any fixed finite
   semantic domain must satisfy precisely its selected guarded axioms under
   every valuation; partiality/overflow guards must be stated and justified.

5. **Church compilation and bounded internal soundness.** For each grade,
   construct the native encodings and programs, prove exact typing, computation
   and extraction, and connect them to an independently defined certificate
   checker. Internalize soundness for all inhabitants allowed by the encoded
   domain, not just generated canonical codes. Prove Void exclusion without
   assuming the internal consistency result. Verify the specified construction
   and object-level derivations in MM0, rather than merely declaring their
   conclusions as axioms.

6. **Indexed interpretation, folds and CPS.** Reuse the natural/source syntax
   contract for quotation and source folds, and the bounded interfaces for
   evaluation when needed. Specify the CPS answer type, translation, rank/size
   changes and substitution/computation laws. Implement it as a genuinely
   different fold algebra with original typing and semantic correctness.
   This branch may proceed alongside (4)–(5) after its source interface is fixed.

7. **Uniform internal consistency bridge.** Relate every accepted original
   contradiction certificate to a covered bounded model internally. Supply
   resource selection/coverage, proof-predicate adequacy and the exact
   all-budget quantification or restricted-domain transfer. Audit the
   applicability of incompleteness hypotheses to the chosen sentence. A family
   of external fixed-bound proofs, or MM0 checking such proofs externally,
   does not itself yield an original PTS inhabitant of that consistency type.
   Retain this as a separate final goal until all bridges are constructed.

## Reusable results and present gaps

- The 65-shape Hilbert catalogue, native soundness/extraction and literal MM0
  specification exist. Full original-PTS-to-catalogue completeness and the
  final MM0 verification of the programme remain to be completed.
- The QIIRT source is safely checked, but its full native interpretation and
  dependent combinatory completeness remain open. Current normal families,
  comprehension, products, computed types and raw original checking are checked;
  the normalizer retains native binders. Context IR alone is not deliverable 2.
- Finite carriers, graded application, contextual certificate soundness,
  guarded fixed-domain models and Church table compilation provide components
  for deliverables 3 and 5. They do not establish every promised internal bridge.
- The [self-interpreter development](../self_interpreter/README.md) supplies
  folds, faithful source-compatible encodings and CPS components. Reconcile
  their typing/rank interfaces with the three presentations; do not assume
  a rank-only dependent algebra already exists.
- The last fresh proof check covered all 79 Agda modules with zero warnings.
  This planning revision adds no Agda/MM0/Rocq code or proof claims.

Each milestone must record safe-check commands, exact public theorems,
remaining assumptions, concrete computation tests and the source/model/encoding
boundary. Consolidate experimental code only after the replacement meets the
same contracts. Existing historical evidence remains intact.
