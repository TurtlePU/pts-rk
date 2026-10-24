# Internal consistency of PTS-rk — research and formalization plan

This directory develops the direct internal consistency programme. Its Rocq
results establish external certificate adequacy, faithful serialization,
source-rank compression, original-PTS carrier/guard/resource witnesses, and
rank-four internal rejection for every externally size-bounded raw-certificate fragment.
One rank-five internal consumer now handles represented dictionaries at a fixed
polymorphic interface. Fixed internal comparison and conjunction operations
execute externally compiled checker programs with exact Boolean correspondence;
internal compilation, branch generation and consistency remain open.

Independent local source graphs now establish source-to-operation agreement
in Rocq, repairing the resource-only contract. One actual rank-6-type PTS term
also proves residual execution agreement for arbitrary represented Run
witnesses. Original context lookup also has a represented graph with every
enclosing shift and an arbitrary-output scope law. Their internal
source-indexed combination remains open: endpoint coherence, substitution,
encoding and decoding in the source graph are still separate obligations.
The uniform Horn family now binds fragment, clause and premise-position
data internally, with rank-five-type introduction, elimination and clause-map
proof transport. These generic terms still require a concrete source-rule
instance and a constructed interpretation handler; they do not themselves
provide uniform finite models or bounded soundness.
This is not a no-go theorem for consistency.
The concise [direct roadmap](DIRECT_ROADMAP.tex) ([PDF](DIRECT_ROADMAP.pdf))
distinguishes the remaining six milestones; internal finite-fragment soundness
(milestone 4) is not yet established.

## Checked starting point

The library `PTSrk.SelfConsistency` uses the original `PTSrk` kernel, Stdlib,
Equations, the combinatory/normalization libraries, and the shared annotated assembler/native checker in
`Interpretation_of_R`. Neither arithmetic interpretation nor a set model is
imported; the original seven certificate/serialization modules are unchanged.

- [NativeProofCodes.v](NativeProofCodes.v): executable independent certificates
  for all six typing rules, explicit beta locations, equality trees, context
  certificates, and acceptance at the literal type `Bottom`.
- [CertificateAdequacy.v](CertificateAdequacy.v): soundness and completeness
  for original typing and context well-formedness. Acceptance checks local
  syntax equations; no native typing proof is a certificate field.
- [SortRenaming.v](SortRenaming.v): relabeling commutes with weakening,
  substitution and arbitrary beta conversion, and preserves acceptance when
  the finitely used product equations are preserved.
- [RankCompression.v](RankCompression.v): executable compression of the whole
  contextual input, including declaration proofs and conversion instructions;
  original typing, acceptance and Bottom are preserved. New labels are bounded
  by two plus the input's recorded label occurrences. Term node counts are
  unchanged; compression is injective on the collected support.
- [StructuralCodes.v](StructuralCodes.v): one finite-alphabet tree carrier,
  canonical binary labels/indices, and an executable original-term scope decoder.
- [CertificateSerialization.v](CertificateSerialization.v): codecs for every
  beta/equality/typing/context constructor and complete inputs. Both inverse
  laws and injectivity are proved. Arbitrary raw inputs have a sound checker;
  every original derivable judgment in a well-formed context is covered.
  Raw compression preserves acceptance and also operates on well-scoped
  rejected inputs.
- [SerializationBounds.v](SerializationBounds.v): exact positive-bit encoding
  size and a bound on every compressed label by the complete serialized input
  size, including repeated fields, annotations and conversion witnesses.
- [InternalCarrier.v](InternalCarrier.v): a literal original-PTS Church carrier
  for the 29-tag/binary-pair alphabet at rank 2; an independent generation
  guard at rank 4; executable typed quotation/generation for every raw tree,
  including malformed and rejected inputs; syntax-level injection.
- [GuardedTables.v](GuardedTables.v): actual closed PTS terms for binary case
  elimination, closure and pointwise equality on arbitrary guarded Boolean
  selectors. Generic tables take four entries as data at one fixed type.
  Lookup/closure account explicitly for selector expansion, without eta.
- [FiniteRejection.v](FiniteRejection.v): complete coverage of closed leaf
  certificates with labels at most 1, a table generated from the independent
  checker, and an internal rejection term for all guarded selector inputs.
  Local syntax checking suffices; no global Bottom-emptiness theorem is used.
- [FiniteCodeFragments.v](FiniteCodeFragments.v): exact executable enumeration
  of all raw codes of size at most b, including malformed inputs; finite
  indexing, decoding, roundtrip and source injection. Admission does not use checking.
- [FiniteFragmentNormalization.v](FiniteFragmentNormalization.v): accepted
  certificates normalize inside computed finite carriers with every beta state
  covered and exact original typing retained. A whole finite certificate family
  shares one carrier; bounded normalization and native canonicity prove raw
  Bottom-checker rejection. These are external Rocq results.
- [FiniteCaseGuards.v](FiniteCaseGuards.v): independent guards for arbitrary
  finite lists of typed points, executable canonical witnesses and an actual
  original-PTS finite elimination term. Selector guards have rank 3.
- [FiniteFragmentTables.v](FiniteFragmentTables.v): actual native-checker
  tables, exact Boolean-output correspondence, general-judgment checking,
  and typed rejection branches; checker definitions remain unchanged.
- [FiniteFragmentRejection.v](FiniteFragmentRejection.v): executable rank-4
  internal rejection proofs for every external bound, applying to all guarded
  inputs. Every raw code has canonical coverage at its complete serialized
  size. [FiniteSelectorSeparation.v](FiniteSelectorSeparation.v) preserves
  quotation injectivity even modulo beta conversion at each fixed bound.
  These are externally generated instances, not an internal all-budget theorem.
- [InternalFiniteDictionaries.v](InternalFiniteDictionaries.v): Church lists,
  type-valued telescope folds, separate All-branch packages and independent
  membership/Fill evidence. Nil/cons/append and one rank-5 eliminator are
  original PTS terms; no arity-dependent telescope occurs in their interface.
- [FiniteDictionaryRealization.v](FiniteDictionaryRealization.v): executable
  quotation of arbitrary typed lists, independent fillers/membership and
  separately supplied branch proofs, exact telescope beta equations and
  syntax-level quotation injectivity.
- [DictionaryRejection.v](DictionaryRejection.v): one fixed polymorphic
  consumer specialized to every complete-code fragment; rejection covers
  arbitrary admitted inputs, with canonical coverage for every raw code.
  Dictionaries and branch proofs are ordinary arguments, not rejection
  assumptions hidden in admission. Their native-checker-specific generation
  is still external. The present carrier parameter has exact rank 1, not
  the rank-2 raw-tree carrier.
- [CheckerComparisons.v](CheckerComparisons.v): executable external compilation
  of the unchanged checker into conjunctions and explicit structural comparisons.
  All six rules, contexts, conversion and malformed inputs are covered; complete
  comparison operands are retained instead of precomputed answers.
- [InternalCodeComparison.v](InternalCodeComparison.v): independent synchronized
  tree-traversal evidence with no comparison result or rejection field, and one
  actual original-PTS comparator whose full type has rank 5.
- [CodeComparisonRealization.v](CodeComparisonRealization.v): executable traversal
  generation for every raw pair, original typing and exact comparator beta laws.
  Correctness applies to canonical quotations with generated traversals, not
  arbitrary inhabitants of the traversal type. Its node count is not a runtime bound.
- [InternalComparisonFolds.v](InternalComparisonFolds.v): rank-3 conjunction
  expressions and one rank-4-type evaluator. Symbolic leaves retain comparator
  applications; beta laws strengthen to exact forward reduction.
- [CheckerExecution.v](CheckerExecution.v): composes these operations without
  callbacks or correctness premises. Every externally compiled program reduces
  to precisely the unchanged checker's output, including true and false cases.
  Raw quotation stays injective; a counterexample shows residual programs are
  intentionally not injective. Parsing, lookup, substitution and traversal
  generation remain external, so this is not a closed raw-carrier checker.
- [InternalJointTraversal.v](InternalJointTraversal.v): a rank-4 joint-tree
  carrier, its constructors/projections and a rank-6 independent guard type.
  Internal Zip generation and standard realization remain unverified;
  unfinished candidates are separate design evidence, not library theorems.
- [CheckerResourceBounds.v](CheckerResourceBounds.v): faithful residual-data
  encoding, exact size accounting and actual capacity witnesses for complete
  comparison operands and every recursive traversal payload. An externally
  generated envelope covers every code in a complete size-bounded fragment,
  including malformed/rejected inputs. These are storage bounds, not operation
  costs, internal budget selection or source-checker agreement.
- [ComputationBoundary.v](ComputationBoundary.v): a native Rocq refutation
  of the precise resource-only agreement contract, using actual original-PTS
  generation/capacity/traversal witnesses and Boolean-separated executions.
  It identifies the need for an independent source-indexed operation relation;
  it does not rule out such a relation or internal consistency.
- [CheckerSourceGraph.v](CheckerSourceGraph.v): independent native local
  graphs for source/step/equality fields, matching, all six source rules,
  contexts, malformed inputs and both raw wrappers. Agreement with the
  unchanged compiler, all-source coverage, uniqueness and both outputs are
  proved; the resource-only counterexample cannot carry this provenance.
- [InternalExecutionGraph.v](InternalExecutionGraph.v): independent original
  Run(e,b):U5 clauses for Boolean-program leaves and conjunction. One rank-6-type
  internal term proves exact-rank-one predicate transport from evaluate(e)
  to b for arbitrary represented witnesses, with actual Holds transport and
  conditional false-output rejection. This is not internal source checking.
- [CheckerGraphRealization.v](CheckerGraphRealization.v): executable Run
  evidence whose outputs retain symbolic comparison programs; application of
  the internal agreement term, both-output source correspondence, actual
  standard acceptance and conditional rejection. The repaired native resource
  contract includes independent source provenance, never an output equation.
  Raw quotation stays faithful; execution witnesses are not claimed injective.
- [ContextLookupCodes.v](ContextLookupCodes.v): faithful literal-context
  codecs and raw lookup exactly matching original Context.index, including
  every shift. Certificate-context erasure is explicit and still native.
- [InternalContextLookup.v](InternalContextLookup.v): independent rank-18
  original context-lookup graph, separate whole-context scope guard, and a
  rank-19-type output-scope theorem for arbitrary represented lookup witnesses.
  No output scope, equality or native typing is a graph field.
- [ContextLookupRealization.v](ContextLookupRealization.v): executable
  standard guards and original lookup witnesses, decoded/raw agreement and
  injective context quotation. These do not prove arbitrary-output coherence.
- [InternalComparisonGraph.v](InternalComparisonGraph.v): rank-6 formation
  of comparison traces indexed by the actual Zip proof and symbolic result;
  all three local Boolean-agreement cases hold for arbitrary open inputs.
  Full constructor/induction assembly remains unverified.
- [ComparisonGraphRealization.v](ComparisonGraphRealization.v): symbolic
  tag-test/conjunction outputs for all raw operands, with a separate beta
  correctness law; not an arbitrary-trace agreement theorem.
- [NamedBeta.v](NamedBeta.v) and [BooleanAgreement.v](BooleanAgreement.v):
  native structural application/beta helpers and scope-polymorphic uses of
  the existing exact-rank-one Boolean transport. No PTS rule is added.
- [ResourcePaths.v](ResourcePaths.v): independent variable-length tree lookup,
  injective structural path codes, append-only left-spine prefix and two-sided
  subresource extension. Exact external path/result-size bounds.
- [InternalResources.v](InternalResources.v): actual fixed-rank PTS relations
  and witnesses for prefix/extension reflexivity, transitivity, generation
  preservation and joining; root/left/right lookup, root/path/value generation,
  and lookup-to-extension. Exact padding handles rank-5 induction motives;
  public quantified law types have ranks at most 8.
- [ResourceRealization.v](ResourceRealization.v): executable generation of
  PTS witnesses for every successful standard lookup, with exact erasure to
  the independent algorithm; standard prefix/extension realizations.
- [InternalPaths.v](InternalPaths.v): total structural substitution on the
  same carrier, guarded generation/unit laws and associativity; independently
  specified rank-8 lookup composes with rank-7 lookup back into rank-7 lookup.
  The internal composition theorem has rank 9, not same-rank closure.
- [PathSubstitution.v](PathSubstitution.v): exact beta correspondence of that
  operation with external substitution on every raw tree and path concatenation.
- [ResourceSeparation.v](ResourceSeparation.v): internal root functionality
  for exact rank-0 Leibniz transport, and leaf/step rejection on arbitrary
  represented inputs using independent type-valued observations.
- [PathRealization.v](PathRealization.v): executable higher-rank lookup
  witnesses, exact erasure/typing, and application of the internal composition
  term with conversion to the exact concatenated-path type.
- [LookupInversion.v](LookupInversion.v): stratified constructor-case
  elimination from independent Look_9 (rank 11), retaining actual Look_5
  child witnesses. This is not matching-constructor inversion. The exact
  full functionality target is formed, not inhabited.
- [InversionRealization.v](InversionRealization.v): executable Look_9
  witnesses for every successful standard lookup, with exact erasure/typing.
- [LookupHistory.v](LookupHistory.v): an independent rank-10 history relation
  with root and Look_6-segment rules. Its rank-11 soundness term iterates the
  existing composition theorem into Look_5 without rank growth with length.
- [HistoryRealization.v](HistoryRealization.v): executable histories for
  arbitrary finite segment lists; erasure equals sequential lookup. Applying
  internal soundness yields the exact concatenated-path lookup type.
- [InternalCapacity.v](InternalCapacity.v): tag-erasing shape and rank-6
  subtree capacity, with internal reflexivity/transitivity, joins,
  extension-to-capacity and lookup/history capacity witnesses.
- [CapacityBounds.v](CapacityBounds.v): exact beta correspondence of shape,
  standard capacity realizations, a common budget for every finite family,
  and external packing/substitution and flattened-path/result bounds.
- [RelationalTransport.v](RelationalTransport.v): consumer-directed lookup
  and history preservation for rank-4 predicates with explicit local descent
  laws; dual negative safety for upward-closed predicates. No functionality
  or constructor inversion is assumed.
- [OccurrenceSafety.v](OccurrenceSafety.v): absence of a represented
  extension witness propagates to every lookup/history output. Actual
  nonzero-leaf and pair absence from the empty-tag resource is constructed
  internally, without external Bottom emptiness. This is not source rejection
  or a complete native subtree-absence characterization.
- [LookupHomomorphisms.v](LookupHomomorphisms.v): shape and generated
  structural filling preserve Look_5, Look_6 and Hist at their existing
  ranks, mapping root/value and leaving the path unchanged.
- [SimulationRealization.v](SimulationRealization.v): independent native
  specifications and original-PTS application of those maps to standard
  lookup witnesses, with exact canonical endpoints; a counterexample shows
  that filling need not reflect successful lookup.
- [CodeSubstitution.v](CodeSubstitution.v): executable capture-avoiding
  renaming/replacement/substitution of annotated raw codes; independent native
  relational agreement, exact original-syntax correspondence, scope
  preservation and scoped totality. These are external Rocq theorems.
- [InternalBinary.v](InternalBinary.v), [BinaryRealization.v](BinaryRealization.v):
  independent original-PTS positive/number/successor relations at ranks
  4/6/8, exact native canonical characterization and executable standard
  witnesses. No canonical reflection of arbitrary PTS inhabitants is claimed.
- [InternalScope.v](InternalScope.v), [ScopeRealization.v](ScopeRealization.v):
  independent index bounds and annotated scope at ranks 10/12, actual
  constructors and scope-to-generation; executable witnesses for every
  bounded index and original term, including untyped terms.
- [InternalRenamingLookup.v](InternalRenamingLookup.v): one fixed relational
  environment and explicit binder depth; rank-14 lookup with proved
  all-output boundedness, and an independently bounded source-index shift.
- [InternalRenaming.v](InternalRenaming.v): source-directed annotated
  renaming at rank 16 and a rank-17 output-scope preservation term. Its
  independent clauses never assume the preservation conclusion.
- [RenamingLookupRealization.v](RenamingLookupRealization.v),
  [RenamingRealization.v](RenamingRealization.v): executable pointwise lookup
  lifting and annotated renaming witnesses, specializing to standard shift
  without an assumed environment family. Decoded/raw endpoints are exact;
  shifted scope is obtained by applying the internal preservation term.
- [InternalSubstitutionEnvironment.v](InternalSubstitutionEnvironment.v),
  [SubstitutionEnvironmentRealization.v](SubstitutionEnvironmentRealization.v):
  independent rank-13 single-substitution environment (zero maps to the image,
  successors to old variables), a separate rank-14 scope bound, and executable
  witnesses for every standard environment point.
- [InternalTermLookup.v](InternalTermLookup.v),
  [TermLookupRealization.v](TermLookupRealization.v): one fixed term-valued
  environment under binders, rank-18 lookup and a rank-19 every-output scope
  bound; executable lifting realizes original `Syntax.transpose` using the
  already constructed shift witnesses.
- [InternalReplacement.v](InternalReplacement.v),
  [ReplacementRealization.v](ReplacementRealization.v): source-directed
  annotated replacement at rank 20, its rank-21 scope fold, and executable
  witnesses at the literal original `Syntax.replace`/`Syntax.subst` endpoints.
  Single substitution supplies its whole environment family. All four new
  lookup/replacement modules compile; full audit status is in the evidence record.
- [NamedTemplates.v](NamedTemplates.v): native assembler/substitution lemmas
  for specializing checked templates without expanding closed payloads.
  This is proof-checking infrastructure, not an extra PTS rule.
- [InvariantObstructions.v](InvariantObstructions.v): precise implication-rank
  restrictions on a same-index dependent invariant, and an accepted conversion
  certificate with an untyped, non-normalizing intermediate. Neither result
  rules out all fixed-rank interpretations.
- [UniformHorn.v](UniformHorn.v): one internally parameterized independent
  Horn family with exact proof-fiber rank 4, constructor/consumer type rank 5,
  arbitrary-open applications and a literal node-fold beta law. Fragment,
  clause and position carriers have exact rank 1; atom rank 1 and 2 are
  checked separately. An interpretation handler is an explicit consumer
  input, never a proof-family field or established model-construction result.
- [UniformHornReindex.v](UniformHornReindex.v): internally supplied clause
  selections pull back positions and endpoints literally. One rank-five-type
  term transports arbitrary proofs, with typed fold and composition beta
  equations. It assumes neither selector bijectivity nor source soundness.
- [UniformGuardedHorn.v](UniformGuardedHorn.v): explicit independent clause
  guard families of exact rank g=3 or 4, certified separately. Proof fibers
  have rank g+2, constructor/consumer types rank g+3. The node-fold beta law
  retains the guard witness; actual guard and interpretation construction
  remain separate obligations. No cumulativity identifies empty/nonempty
  Enum_3 ranks.
- [FiniteRawDecoding.v](FiniteRawDecoding.v): a rank-four-type decoder from
  finite positions and independent Enum_2 generation to the original rank-two
  raw-tree carrier. Open-input typing, canonical forward beta, all-raw-code
  admission, packed-input correspondence and syntax-level injection are
  proved. Tables remain external; arbitrary-output coherence is not inferred.
- [FiniteRawTables.v](FiniteRawTables.v): the simpler bare-selector raw table
  has exact type rank 2, with no generation premise. It re-abstracts the raw
  algebra and dispatches at its final rank-zero answer type. Canonical forward
  reduction reaches an expanded quotation; genuine beta laws identify it
  with the old quotation and canonical Enum_2 decoder. Expanded quotation and
  complete-source syntax injection are retained, without arbitrary eta or
  parametricity.
- [Audit.v](Audit.v): public theorem types and transitive assumptions.

The finite-fragment route is the current continuation. Its fresh focused
closure is checked by [this audit](../../docs/direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23/AUDIT.sh),
or built with `dune build @theories/self_consistency/finite-fragment-audit`.
The full audit includes its 95 new public reports through
[FiniteFragmentAudit.v](FiniteFragmentAudit.v).
The represented-dictionary continuation has its own fresh
[audit](../../docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/AUDIT.sh)
and `finite-dictionary-audit` alias; [FiniteDictionaryAudit.v](FiniteDictionaryAudit.v)
is also imported by the full audit.
The comparison-execution continuation has a fresh
[audit](../../docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23/AUDIT.sh)
and `comparison-execution-audit` alias. [ComparisonExecutionAudit.v](ComparisonExecutionAudit.v)
lists all 92 new public proof endpoints and is imported by the full audit.
The source-provenance continuation has its own fresh
[audit](../../docs/direct-r-handoff/verification/self-consistency-source-provenance-2026-10-23/AUDIT.sh)
and `source-provenance-audit` alias. [SourceProvenanceAudit.v](SourceProvenanceAudit.v)
lists all 90 new public proof endpoints and is imported by the full audit.
The operation-provenance checkpoint adds
[OperationProvenanceAudit.v](OperationProvenanceAudit.v), covering all 80 new
endpoints, and the `operation-provenance-audit` alias.
The uniform-Horn checkpoint adds [UniformHornAudit.v](UniformHornAudit.v),
covering all 104 public endpoints in its five new modules, and the
`uniform-horn-audit` alias.
Compilation and independent-check status are recorded in [EVIDENCE.md](EVIDENCE.md);
an implemented definition is not by itself a completed verification result.
Run `opam exec -- dune build @theories/self_consistency/audit` in the pinned
environment. For fresh compilation and comparison with pristine upstream,
run [the current focused audit](../../docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24/AUDIT.sh).
It rebuilds all public reports and recursively checks the complete new
uniform-Horn/raw-decoder dependency closure with the supported VM backend enabled.
The unchanged older closure retains its separate full kernel audit; this
continuation check is not full repository CI.

The certificate algorithms remain external Rocq constructions. The raw
carrier now also has an original-PTS representation; external decoders
recover the original intrinsically scoped terms and certificates without
discarding fields or repairing malformed data. Malformed trees remain values
of the carrier and are rejected; resource admission must eventually cover
them as well. Structural generation is not resource admission. The finite
laws have rank-4 types, using exact rank-1 or rank-2 motives; they do not
assert unrestricted Church parametricity. Resource graphs now handle arbitrary
represented arguments with explicit witnesses; source typing/acceptance and
normalization are absent from their definitions. Composition now has a
stratified internal witness and standard coverage. Fixed-rank history
iteration and structural capacity now have witnesses. Full arbitrary-path
functionality and matching-constructor inversion remain open but have no
implemented consumers; they are optional auxiliary lemmas, not prerequisites
to the relational route. Internal numerical comparison is likewise optional
if structural closure proves the required sufficiency. Storage envelopes now
cover all raw sources; operational sufficiency and the final standard
resource admission remain open. Higher-rank
standard coverage does not lift arbitrary lower-rank proofs. The size
bounds remain external; native shape-subtree inclusion implies size comparison
and has a PTS capacity realization. No converse or numerical bound extracted
from arbitrary internal capacity inhabitants is claimed.
Finite-family packing does not establish the resource sufficiency of a checker
or normalizer. Extension transports only rank-4 constructor-closed predicates,
not arbitrary higher-rank lookup claims. The new consumer and simulation
laws avoid global uniqueness for their stated uses; they do not yet supply
the actual source typing/normalization invariant. Dependent consumers must
thread the same result or prove the coherence they need. That stronger
dependent invariant is now an optional route: finite-fragment rejection
bypasses it by externally certified branches and internal finite cases.
The represented Church-list consumer now supplies a fixed interface for
dictionaries and case witnesses. Internally producing its native-checker
branch package from independent computation evidence remains open.
Uniform source decoding, operation sufficiency, complete standard
resource admission, all-budget soundness and consistency remain open. Bound every
history or proof object actually represented; complete typing-certificate
reconstruction after each reduction is a design choice, not an intrinsic goal.

## Milestones and remaining proof obligations

These numbers match [DIRECT_ROADMAP.tex](DIRECT_ROADMAP.tex). The existing
finite rejection schema is completed; the following uniform internal gates
are not. In particular, the schema is not milestone 4 below.

1. **Computation witnesses:** prove the endpoint laws actually used by the
   chosen source bridge. The direct checker route still needs comparison,
   lookup and substitution provenance; its particular implementation and
   joint traversal generation are not unconditional prerequisites.
2. **Internal source bridge:** translate independently admitted proof nodes
   into the guarded Horn proof type, or finish the direct checker relation.
   Cover all six original rules, contexts, endpoints and conversion
   instructions. Coverage and agreement must not be admission fields.
3. **Operational resource sufficiency:** extend storage envelopes to actual
   operations, intermediate states and proof transport; supply independent
   standard admission, including rejected and malformed inputs.
4. **Internal finite-fragment soundness:** reuse the checked arbitrary-proof
   Horn consumer after the source bridge, with the required fragment and
   false-query interface. Bounded normalization or a negative continuation
   remains an alternative. Do not assume an All-package or normalize
   arbitrary conversion intermediates.
5. **Uniform bounded soundness:** integrate checker, dictionary and resources
   into one fixed-rank term for arbitrary represented budgets.
6. **Resource elimination and adequacy:** construct the continuation package,
   prove original formation/typing and standard admission/acceptance, and
   justify any translation to the intended historical consistency sentence.

Audit the chosen relational domain and applicable derivability conditions in
parallel. Weak local finite satisfiability and Willard's stability conditions
are promising inputs, not a demonstrated escape from Gödel's theorem.

Global functionality, full matching inversion, internal numerical comparison,
complete certificate reconstruction after every reduction, and a uniform
budget selector are not unconditional prerequisites. Prove the weaker local
invariant or coherence each actual consumer needs. The logical-viability audit
and assumption/kernel checks run alongside the mathematical work, not only
after final assembly. No unrestricted self-consistency conclusion is claimed.

## Research notes

- [Recommended direct roadmap](DIRECT_ROADMAP.tex) and its [PDF](DIRECT_ROADMAP.pdf):
  proof-local relational soundness inside original PTS-rk, with no H or EA
  proof-theory intermediary. This supersedes the earlier priority order,
  not the earlier note's record of its particular finite-ordinal target.
- [Self-contained research note and plan](README.tex), in the repository's
  LaTeX–Markdown dialect, and its [compiled PDF](README.pdf).
- [Reproducible document build](build-note.sh): run
  `bash theories/self_consistency/build-note.sh` from the repository root.
- [Source provenance and verification](EVIDENCE.md).

The direct route targets one fixed-rank term refuting independently accepted
contradiction certificates under independently specified resource guards.
A continuation-encoded resource domain gives the final negative consistency
statement without a uniform budget selector. Standard raw-code admission,
arbitrary-input soundness and any comparison to the old sentence are explicit
obligations. The combinatory development supplies external Agda soundness in
graded syntactic carriers and executable finite guarded Hilbert models. Its
literal MM0/native adequacy now also supplies models of all 55 guarded MM0
axioms at size>=5 and depth>=3, with unguarded Void denial and actual
original-PTS satisfaction certificate types of rank<=4. Their union exactly
covers the independent catalogue, not yet all original PTS derivations.
The later indexed Horn encoding adds actual original-PTS soundness functions
for arbitrary open queries and independent proof inhabitants: proof fibers
have rank three, consumer types rank four. The fixed guarded-MM0 positive
model premise is discharged. Literal atom maps transport proofs into an
independent raw-observation family, with both supports fixed before queries.
Reuse this backend instead of rebuilding dependent preservation if an internal
source-to-Horn bridge suffices. Original-PTS coverage and concrete internally
represented fragment/budget operations remain open; the Void specialization
still uses native canonicity. UniformHorn abstracts a fixed clause interface
but does not construct those concrete operations or their model handler.
This does not complete milestone 4 for the raw-source interface. The earlier
soundness results have their own combinatory audit evidence.

Build the new roadmap with
`bash theories/self_consistency/build-note.sh DIRECT_ROADMAP`.
The no-argument command continues to build the earlier summary.

The earlier summary isolates the draft's specified predicate-only consistency sentence,
its tower-witnessed elementary-arithmetic soundness obligation, and the precise
boundary between existing Rocq metatheorems and internal proofs. It compares
a direct interpretation of Pakhomov's higher-order theory with a direct,
resource-relativized PHOAS route, including what fragment-uniform interpreters
would add.

The continuation now supplies a fixed closure application head for each
quotation-budget fragment; see
[the interpreter note](../../PTS-rk_self_interpreter.tex). The code carries
its specialized normal runner. This simplifies the evaluation interface,
but internal accepted-proof reification and budget quantification remain
open. No internal consistency proof is claimed by that interface theorem.

The shared `Algebra` interface now also supports tag-free full-dependent
evaluation (`UnifiedAlgebra`) and actual alternative folds on STLC and
finite-dictionary combinatory codes. The latter include a typed CPS algebra
and require no numeral conversion. These simplify code representation and
evaluation, not the acceptance-soundness obligation: the full dependent
signature still varies by plan, and the Hilbert bridge does not yet supply
native source completeness or internal dependent unquotation. See the
updated interpreter note and `self_interpreter/OBLIGATIONS.md`.

The direct roadmap continues from the checked resource graphs, histories,
structural capacity and scope-preserving renaming to term-valued substitution,
the dependent invariant and operation sufficiency. Full lookup functionality
is optional unless a concrete consumer needs it. The earlier `ExplicitPTS`/EA modules belong to the historical
alternative route. All PTS
endpoints must use the original `Syntax.Term nat`, `Typing.typ`, and
`Ranks.RankSorts`. Keep external Pakhomov results visibly outside the checked
dependency graph until their proofs or concrete proof certificates are supplied.

No CPS formalization is part of this plan. The original kernel, arithmetic
interpretations, set models, normalization and self-interpreter developments
remain separate libraries.
