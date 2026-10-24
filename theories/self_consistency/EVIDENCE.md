# Sources, theorem map and verification

## Uniform Horn and finite raw decoding checkpoint — 24 October 2026

Five new modules expose 104 public proof endpoints, all listed with both
Check and Print Assumptions in UniformHornAudit: UniformHorn (19),
UniformHornReindex (16), UniformGuardedHorn (16), FiniteRawDecoding (31),
FiniteRawTables (22).

The generic Horn family internally binds fragment, clause and premise-position
data, not just queries. For exact atom ranks 1/2, proof fibers have rank 4
and constructor/consumer types rank 5. Literal clause pullback transports
arbitrary proofs, with typed fold and composition beta equations. Independent
guard fibers of exact rank g=3/4 give proof rank g+2 and constructor/consumer
type rank g+3. Guards and model handlers remain separate concrete obligations;
the generic consumer does not construct a model or establish source coverage.

The bare finite raw table has exact type rank 2 and accepts arbitrary open
selectors without generation evidence. It re-abstracts the raw carrier's
algebra and dispatches at its final rank-zero answer type. Canonical forward
reduction reaches an expanded quotation; separate beta laws identify it
with the original quotation and canonical Enum_2 decoder. Both ordinary and
expanded quotations retain source-syntax injectivity. The rank-four-type
Enum_2 route separately gives literal forward output and typed standard
admission of every raw tree at its serialized size, including malformed
inputs. No arbitrary-output coherence, eta principle or internal parser is
claimed. Enum_3 has rank 4 for nonempty alphabets but 3 for the empty one;
the guarded interface certifies these separately, without cumulativity.

Fresh focused audit PASSES, exit 0/archive 0, 23:33:49–23:35:50 UTC on
23 October (24 October locally). Compilation takes 69s, 23:34:06–23:35:15;
the actual 64-module closure prints exactly 414 closed reports, including
all 104 aggregate endpoints. Complete recursive VM-enabled kernel checking
passes in 27s, 23:35:15–23:35:42. Its full raw inventory equals fresh pristine
exactly: inherited functional_extensionality_dep only, all unsafe categories
empty. Prior proof bodies, original kernel, frozen ZFC, additive registrations
and source/driver hashes all pass before/after gates. The prior failed run
stopped before compilation on one terminal blank in the new aggregate; that
blank alone was removed and the failed run retained. No gate was weakened.
Exact commands, versions, raw logs, source hashes and worker failures are in
[the verification record](../../docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24/COMMANDS.md).
Fresh build: /tmp/pts-rk-uniform-horn-fresh.cCcZgE; live logs:
_build/self-consistency-uniform-horn-audit.lD2nv7; retained audit.V54reH.
Worker archival preserves all available logs/commands/times/exits/hashes;
failed-source bytes are unavailable for the historical Decoding attempts
and Tables attempts 01–07. Final sources and the fresh audit are fully pinned.
Full repository CI and the unchanged older aggregate were not rerun.

The roadmap build and inspection pass, 23:33:23–23:33:29 UTC: nine nonempty
pages, six links, required text/mathematics and all-page rendering. Pages
1/3/7/8/9 were visually reviewed. Exact note records are note.e1xHbA in the
same verification directory; no rendering caches are included. The updated
roadmap distinguishes the two decoder routes, guarded/unguarded interfaces,
and the missing concrete source/model instance. Milestone 4 and consistency
remain open. No commit, push or cleanup was requested or performed.

## Operation provenance checkpoint

Seven new modules expose 80 public proof endpoints, all listed in
OperationProvenanceAudit: NamedBeta (11), BooleanAgreement (8),
ContextLookupCodes (13), InternalContextLookup (15),
ContextLookupRealization (16), InternalComparisonGraph (14) and
ComparisonGraphRealization (3).

Literal-context encoding is injective and has an exact scoped decoder;
raw lookup agrees with the original Context.index, including every shift.
The original-PTS lookup graph has rank 18 and a separate rank 14 whole-context
scope guard. Its rank-19-type consumer derives scope from arbitrary represented
lookup evidence. Executable witnesses realize every original context/index,
including the old source-graph lookup clause. Certificate-context erasure
remains native; neither arbitrary-output coherence nor typing is claimed.

Comparison Trace has rank 6 and retains the actual Zip proof. All three local
agreement cases hold for arbitrary typed open inputs, with child agreement
as induction data. These transport exact-rank-one Boolean predicates, not
arbitrary syntax identity. Full Trace constructors and arbitrary-Trace
induction remain unverified; failed candidates live only in evidence.
The independent symbolic-output compiler retains tag tests and conjunctions
and has a beta law for every raw operand pair. It does not realize Trace.

Fresh integrated compilation passes 19:28:08–19:56:57 UTC (1729s), exit 0:
80 new closed reports, 81 aggregate. Live logs are in
`_build/self-consistency-operation-provenance-audit.dLxE0S`. The driver then
exits 2 before kernel checking: editing its reusable file during compilation
disturbed Bash's later reads. Both script versions and the raw EOF failure
are retained. The first immutable recovery stops on five further concurrent
registrations; all other 524 raw hashes match. Root reviewed exact
normalization of all 13 additive module/vo entries. Continuation 02 rechecks
those inputs, pins 525 current paths and passes the corrected 80-declaration
and 81-report gates. Full recursive kernel checking passes
20:03:03–20:24:26 UTC (1283s), exit 0, on the same fresh tree. Its complete
inventory equals fresh pristine exactly: inherited functional_extensionality_dep
only, no unsafe entries. All 18 continuation gates pass by 20:24:40;
all 525 current paths agree before/after, and original-kernel, frozen-ZFC,
old-body, safety, exact-registration and whitespace checks pass. This does
not relabel the original failed driver invocation as all-pass.
The first audit stopped before compilation on concurrent Dune
registrations. Exact reviewed normalization now preserves all 514 preceding
nonregistration entries and pins 525 current paths. Every failed attempt,
command and raw log is retained in the
[verification record](../../docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/COMMANDS.md).
The corrected declaration gate also passes negative regression tests: one
missing Print is rejected with all 80 Checks retained. The older full audit
and repository-wide CI were not rerun.
All 14 final documentation/source gates pass, 20:26:43–20:26:50 UTC, exit 0;
live logs `_build/self-consistency-operation-provenance-final.o9Z9IF`.
Final source/PDF hashes and the complete pristine inventory are rechecked;
exact raw logs and readable copies are retained in audit-final/final-checks.
Milestone 4 and consistency remain open. No commit or push was requested.

The concurrently verified Horn checkpoint changes the roadmap's preferred
backend. `HornInternalSoundness.arbitrary_proof_sound` and
`MM0GuardedInternalReflection.arbitrary_encoded_proof_sound` consume arbitrary
inhabitants of independent finite proof types; their fixed-MM0 positive
model premise is discharged. Proof/consumer type rank bounds are 3/4.
This is separate audit evidence, not part of the operation-provenance closure:
the combinatory 63-module fresh build/kernel audit passes with 95 new reports
and 981 aggregate, 19:53:09–19:56:22 UTC. Original-PTS coverage, internal
source translation and represented fragment parameters remain open; Void
certification retains native canonicity. The roadmap now recommends reusing
this backend instead of duplicating dependent preservation where possible.
The final roadmap builds/validates as eight pages with six links; all pages
render and have been visually reviewed (pages 2--6 match earlier renders).
Four note builds and both failed literal-text inspections are retained in
note-horn-final. The inspector was unchanged. Final TeX/PDF SHA256 values:
85749fa09e186fc31c09da98feafdffc2afa42db7f5a55ff201cd4754b169b2d and
97381411194dba5e433ff4819ba784b63effb398c2c2687493fe6d127dc712a8.

## Source provenance and arbitrary-witness internal execution

Three new modules and SourceProvenanceAudit expose 90 public proof endpoints:
CheckerSourceGraph (35), InternalExecutionGraph (28), CheckerGraphRealization (27).

- SourceFields, StepFields and EqualityFields specify native endpoints;
  CheckGraph covers all six rules, and RawGraph/BottomGraph include malformed
  decoding. Agreement, uniqueness, coverage and both outputs are proved,
  never assumed by graph constructors. LookupIndex, original substitution
  and decoding remain native operations.
- Run independently represents Boolean leaf/conjunction execution. Actual
  original-PTS `agreement` has full-type rank six and applies to arbitrary
  represented witnesses. Its Same conclusion transports predicates of exact
  rank one; it is not unrestricted equality or beta conversion.
- `execution_witness` retains symbolic comparison programs and conjunctions.
  `all_raw_sources_have_execution` combines standard resource/source-graph
  coverage and actual internal execution witnesses. SourcedResources excludes
  the old mismatch without assuming checker agreement. Acceptance is realized
  by actual inhabitants; `accepted_sort_realized` is a nonvacuous example.
  Conditional rejection retains a separately proved false-output premise.

The internal residual law and the native source law are not yet combined
inside PTS. Represented original lookup, substitution coherence, rank maximum,
complete source parsing and local endpoint provenance remain. In particular,
generic replacement environments may be multivalued; scope and exact standard
realization do not prove arbitrary dependent coherence. Operational resource
sufficiency and internal finite-fragment soundness (milestone 4) remain open.

Fresh compilation passes 18:09:36–18:14:39 UTC (303s), exit 0: all 90 new reports
closed, 91 aggregate. Complete recursive VM-enabled kernel verification passes
18:14:39–18:22:11 UTC (452s), exit 0, with no dependency skips/admissions.
The entire inventory exactly matches fresh pristine: inherited
functional_extensionality_dep only, no unsafe entries. Live logs
`_build/self-consistency-source-provenance-audit.RB1ktf`; fresh absolute build
`/tmp/pts-rk-source-provenance-fresh.yW2QOO`. The
[verification record](../../docs/direct-r-handoff/verification/self-consistency-source-provenance-2026-10-23/COMMANDS.md)
preserves exact commands, individual failures and audit attempts.

Attempt 01 stopped before compilation at a concurrent combinatory Dune change.
The reviewed adjustment checks exact additive registration normalization,
preserves all 503 old bodies and pins all 510 scoped paths. New independent
guarded-model files are outside this closure; no actual kernel dependency is
skipped. The raw post-build gate then exits 1 at 18:22:18 because the same
Dune file gained two more independent registrations. All other 509 hashes
match. Exact normalization of the six additions recovers the prior Dune hash;
the raw mismatch is retained, not described as an all-pass run. A seventh
registration appeared during archival and independently normalizes to the
same prior hash. All 13 post-build recovery/final checks pass,
18:28:16–18:28:24 UTC, exit 0; live logs
`_build/self-consistency-source-provenance-final.ddsFzI`. All 509 other scoped
entries agree across before/after/current, all 503 prior bodies remain frozen,
and all three exact registration normalizations pass. Full-tree snapshots
are informational, not claims about the concurrent new modules.
The old full audit and whole-repository CI are not rerun.

The updated roadmap builds/validates with 492 source lines and eight PDF pages.
All eight pages are nonempty, rendered and visually reviewed; seven links and
required mathematics pass inspection. Final source SHA256:
80c18b489a7c44cf33ad0e0546b0dedfc9a4c581673cdbc42f9ff333b2f97ffe.
PDF SHA256: 80bce0e5848cb9bc97d16906b304f4837bcdc9af29fc26e62fbf8cc731f23854.

## Joint interface, storage coverage and resource-only contract boundary

Three new modules and JointResourceAudit expose 59 public proof endpoints:
InternalJointTraversal (10), CheckerResourceBounds (38), ComputationBoundary
(11). The joint carrier/constructors/projections and independent guard TYPE
are checked; generation constructors, buildZip and standard joint realization
are not. Their failed/unverified candidates are archived outside theories.

The storage results retain complete operands and every synchronized payload,
with faithful residual-data serialization, exact size accounting and actual
PTS capacity inhabitants. One external envelope covers a complete raw-code
size fragment without filtering by acceptance. This is not an operation-cost
or internal budget-selector theorem.

The counterexample supplies actual source/budget/expression generation,
capacity, correct recursive traversal and typed residual execution for a
scoped rejected source, while its self-comparison returns true. The proper
compiled checker returns false; their PTS executions are beta-separated.
The native contract refutation does not assert an internal PTS negation or
rule out a source-indexed checker relation. Internal source agreement and
dependent soundness remain open; milestone 4 is not achieved.

Fresh integrated compilation passes 11:17:31–11:22:22 UTC, 291s, exit 0:
59 new closed reports, 60 aggregate. Fresh audit passes all 24 stages,
11:17:16–11:28:25 UTC, exit 0. Complete recursive VM-enabled kernel checking
passes 11:22:22–11:28:19 (357s), without dependency skips/admissions. The
entire context inventory equals fresh pristine exactly: only inherited
functional_extensionality_dep, no unsafe entries. All 500 frozen previous
entries remain unchanged; all 506 before/after hashes match. Original
kernel, frozen ZFC, safety and whitespace checks pass.
Live logs `_build/self-consistency-joint-resources-audit.VWulyQ`; fresh
absolute build `/tmp/pts-rk-joint-resources-fresh.TqBIPV`.
The [verification record](../../docs/direct-r-handoff/verification/self-consistency-joint-resources-2026-10-23/COMMANDS.md)
preserves exact commands, worker failures/resource kills and draft status.
The old full audit and repository-wide CI are not rerun.

The streamlined roadmap builds and validates: 432 source lines and seven
pages, down from 1390 lines and 21 pages in the previous working version.
All seven pages are nonempty, rendered and visually reviewed; seven links
and required mathematical text pass inspection. Two failed note attempts
and an intermediate success remain recorded separately from the final build.
Final source hash: 3599bbcdad1e50ce26aadfc16d6b7a81df127158a2df0f40c76009566b39d5e8.
PDF hash: 5aa0f380f8258f7ea137ff3d7fa5bb610c3e6a4716e62de99ff629f068582e33.

## Internal comparison and residual checker execution — verified

Five new modules and ComparisonExecutionAudit expose **92 public proof
endpoints**, including all examples. CheckerComparisons compiles the exact
unchanged checker to expressions retaining complete comparison operands;
InternalCodeComparison supplies output-neutral synchronized traversal and
one rank-5-type comparator. CodeComparisonRealization generates traversals
and proves exact structural equality on canonical quotations.
InternalComparisonFolds supplies one internal conjunction-expression evaluator;
CheckerExecution proves exact forward reduction to either native checker
output, without any comparison callback or rejection premise.

Fresh integrated audit passes all **23 stages**, **09:56:05–10:04:43 UTC**,
exit0. Fresh compilation passes 09:56:21–10:01:22: 92 new closed reports,
93 aggregate including imported Ranks. Complete recursive VM-enabled kernel
checking passes 10:01:22–10:04:36, without skip/admission flags. The entire
context inventory equals fresh pristine exactly: inherited
functional_extensionality_dep only, no unsafe entries. Exact declaration
coverage, all 494 frozen prior entries, all 502 current before/after hashes,
original kernel/frozen ZFC/safety and tracked/untracked whitespace checks pass.
Old full audit/repository CI not rerun.
Live logs `_build/self-consistency-comparisons-audit.ftbRbY`;
fresh absolute build `/tmp/pts-rk-comparisons-fresh.IyPIZj`.
The [verification record](../../docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23/COMMANDS.md)
preserves worker/setup/proof failures and final audit commands separately.

Roadmap/PDF build and inspection pass: 21 nonempty pages, seven links, all
pages rendered; pages1/9/10/20/21 visually reviewed. Build directory
`/tmp/pts-rk-consistency-note.k6uAuy` (final); the earlier B4XQac build is
preserved separately. Final hashes and page-review details are in NOTE-REVIEW.md.

**Boundary:** parsing, context lookup, endpoint/substitution computation and
traversal generation remain external. Correctness covers canonical quotations
with generated traversals/expressions, not arbitrary Church inhabitants.
This is not a closed raw-code checker or all-budget soundness theorem.
Source serialization/quotation remains injective; a checked counterexample
shows residual programs are not. Traversal-node count is not a runtime bound.
Internal compilation/resource sufficiency and a separate internal rejection
argument remain open.

## Represented dictionaries and fixed internal elimination — verified

Three new proof modules and FiniteDictionaryAudit add **56 public endpoints**.
InternalFiniteDictionaries supplies one Church-list interface, internal
type-valued telescope folding, All branch packages, independent Guard/Fill
evidence, and a rank-5 original-PTS eliminator. FiniteDictionaryRealization
proves executable standard quotation/admission, exact telescope beta laws
and syntax-level list injection. DictionaryRejection applies one fixed
polymorphic consumer to every complete-code fragment and handles arbitrary
admitted inputs, not just canonical points.

Fresh integrated audit passes **09:04:26–09:05:22 UTC**, all 22 stages exit 0.
All 56 new endpoint reports are closed (160 aggregate reports). Full recursive
VM-enabled kernel checking passes 09:05:04–09:05:17, with no dependency skips.
The entire context inventory equals fresh pristine: only inherited
functional_extensionality_dep, no unsafe entries. Every previous theory source
is hash-checked unchanged except the two audit/module registration files;
original kernel and frozen ZFC checks pass. The complete older audit and full
repository CI were not rerun. Incremental proof failures remain recorded.

Fresh build: `/tmp/pts-rk-dictionaries-fresh.KOCLBv`.
Live logs: `_build/self-consistency-dictionaries-audit.PkYzEJ`.
The updated roadmap/PDF builds cleanly: 20 nonempty pages, seven links,
all pages rendered; pages 1/7/8/9/19/20 visually reviewed. Exact commands,
source hashes, failures and archived logs are in the
[dictionary record](../../docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/COMMANDS.md).

**Boundary:** uniform elimination is proved, internal native-checker branch
generation is not. The standard list, table and All witnesses are still
generated externally from b; All is never a resource-admission premise.
The current parameter is E:U1, not the existing raw-code carrier C:U2.
Internal budget/dictionary generation, exact represented-checker correspondence,
branch generation from independent evidence, and sufficient-resource/cost
bounds remain open. No internal all-budget consistency theorem is claimed.

## Finite-fragment normalization and internal rejection — verified

Six new proof modules plus FiniteFragmentAudit add 95 public endpoints.
For every external complete-code size bound, FiniteFragmentRejection constructs
a literal original-PTS guarded rejection term whose type has rank four.
All raw trees, including malformed/rejected codes, have independent finite
admission. Tables compile the unchanged checker, general judgment tables
have exact output correspondence, and quotation is injective even modulo
beta conversion at each fixed bound. FiniteFragmentNormalization connects
accepted certificates to the improved combinatory normalization/canonicity
results, with one computed carrier for a whole finite source family.
The guard never assumes checking, normalization or rejection.

Fresh integrated audit passes **08:23:08–08:24:10 UTC**, all 21 stages,
exit 0: 95 new closed reports (199 aggregate including imports/repeats),
full recursive checking of the complete new dependency closure, and exact
complete inventory equality with fresh pristine. Only inherited functional
extensionality remains; no unsafe entries. Original/common/previous proof
sources and the frozen ZFC model are unchanged; before/after manifests agree.
The earlier full 495-report audit is not rerun, nor is full repository CI.
The first fresh run's final whitespace failure concerns an unchanged old
file and remains recorded; it is not relabelled a pass.

Roadmap/PDF build and inspection pass: 19 pages, seven links, all pages
rendered, pages 1/7/8/18/19 visually reviewed. Exact commands, hashes,
failures and archived logs are in the
[finite-fragment record](../../docs/direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23/COMMANDS.md).

This completes the finite bounded schema, not uniform internal consistency.
At this earlier checkpoint the carrier/case telescope/table/proof varied
externally. The dictionary continuation above now supplies fixed-interface
elimination; internal all-budget generation and operation-cost bounds remain
open. No assumptions of those targets were added.

## Binder-lifted replacement and invariant restrictions — verified

Six new modules register 69 endpoints, 495 total. InternalTermLookup and
TermLookupRealization pass isolated compilation (9 and 7 closed reports).
InvariantObstructions passes compilation, 14 closed reports and full recursive
VM-enabled closure checking with the pristine inventory. NamedTemplates
passes isolated compilation and 16 closed reports; its native assembler lemmas support efficient
specialization without changing original PTS rules. Optimized InternalReplacement
passes isolated compilation 04:47:42–05:09:34 UTC, 1312s, exit 0, and 12 closed reports.
ReplacementRealization passes 05:10:04–05:28:10 UTC, 1086s, exit 0, with 11 closed
reports. Thus all 69 new public endpoints compile with closed assumptions.
Milestone 1 is complete. Fresh integrated compilation passes
04:49:40–05:43:05 UTC, 3205s, exit 0, with all **495/495 public reports closed**
and identical before/build source manifests. The complete independent
recursive closure check also passes 05:29:20–06:11:50 UTC, 2550s, exit 0.
Its entire inventory equals fresh pristine exactly: inherited
functional_extensionality_dep only, no unsafe entries. All mapped source
copies and before/after proof manifests match.

The rank-18 lookup and rank-20 replacement relations have independent clauses:
none assumes output scope. Their scope bounds have quantified ranks 19/21.
Standard replacement witnesses retain annotations and realize original
Syntax.transpose/replace/subst, with complete single-substitution lookup
families. Decoder/raw endpoints are literal. This is scope preservation,
not dependent typing/conversion soundness or a uniform internal normalizer.
The rank obstruction rules out one same-index invariant pattern; the accepted
non-normalizing conversion detour rules out normalizing every supplied raw
intermediate. Neither proves impossibility of the overall programme.

The first inlined replacement run times out after 2400s (exit 124); binder
checking and Qed had passed, but application checking was unfinished. The
first fresh audit was deliberately superseded before proof edits (exit 130).
Generic binder/app templates and exact public-type specialization pass
separately; the unchanged scope probe also passes, including Qed. Public
constructor terms now apply the templates to actual term_at. There is no
retained hypothesis for lookup or replacement correctness.

Snapshot 2 began 04:49:40 UTC in the SAME fresh absolute Dune directory,
/tmp/pts-rk-replacement-fresh.87Hwa9. Audit.vo was absent, so public reports
are not cached. Source freeze, safety, registration and 74 prior-source checks
pass; integrated compilation and all 495 reports now pass. The complete
recursive check began 05:29:20 UTC over a
coherent isolated closure, in parallel with fresh Dune. All old/new source
copies match, and its before-manifest equals snapshot 2 exactly. All 15
independent final checks pass at 06:13:32 UTC, including repeated inventory,
snapshot, original-kernel/frozen-ZFC and 74 previous-source checks. The
redundant fresh checker was deliberately stopped afterward, actual exit 143
at 06:14:19 UTC; it is not reported as a pass. The successful coherent
isolated check supplies complete new dependency-closure verification.
Final roadmap build 04 and PDF
inspection pass: 18 nonempty pages, 7 links, required text/math and all-page
rendering; pages 14, 16–18 visually reviewed.
Exact commands, exits and limitations are in the
[replacement verification record](../../docs/direct-r-handoff/verification/self-consistency-replacement-2026-10-23/COMMANDS.md).
No full repository CI, staging, commit, push or cleanup is claimed.

## Standard shift realization and single-substitution environments

Four modules add 41 registered Lemma/Theorem endpoints (426 total).
RenamingLookupRealization constructs fixed-environment pointwise witnesses;
RenamingRealization uses original constructor applications to realize every
annotated renaming with such a family, then constructs the family for standard
shift. Its exact decoded/raw endpoints and actual application of renaming_scope
are separate from arbitrary-inhabitant reflection. InternalSubstitutionEnvironment
defines an independent rank-13 graph and rank-14 bound; standard image/old-variable
witnesses are executable in SubstitutionEnvironmentRealization. Neither graph
clause assumes output scope. Full internal binder-lifted replacement is still open.

Independent source review passes. The environment's isolated compilation passes
(exit0); three completed isolated copies match sources. RenamingRealization's
isolated attempt was interrupted, not a pass. Fresh integrated compilation
passes 03:09:08–03:22:09 UTC (781 seconds, exit0), with all 426/426 reports closed;
see the
[current record](../../docs/direct-r-handoff/verification/self-consistency-renaming-2026-10-23/COMMANDS.md).

The previous seven-module dependency closure now passes full recursive checking
with supported `-bytecode-compiler yes` (02:06:14–02:16:57 UTC including pristine
checking), and its complete inventory equals pristine: only inherited
functional_extensionality_dep, no unsafe entries. All proof bodies are checked;
the VM conversion/serialized-bytecode path is distinct from the earlier
VM-disabled timeout recorded below. The current four-module complete dependency
recheck PASSES 03:22:22–03:36:57 UTC (875 seconds, exit0), with that same explicit
VM flag. Its complete inventory also equals pristine exactly, with no unsafe
entries. All 76 frozen manifest entries check before and after; all 34 earlier
proof modules, original/common sources and the frozen PR#1 ZFC model remain
unchanged. Final note build 02 and PDF inspection pass: 15 nonempty pages, four
links, required text/math and all-page rendering; pages 12/13/15 visually reviewed.
No full CI, commit, push or cleanup. The new one-shot audit script is
syntax-checked; the recorded staged commands are the actual verification run.

## Annotated substitution and fixed-environment renaming

Seven new modules add 102 registered public theorems/examples (385 total).
`CodeSubstitution` proves native raw replacement/computation agreement,
exact original annotated substitution, scope preservation and scoped totality.
`InternalBinary`/`BinaryRealization` and `InternalScope`/`ScopeRealization`
provide actual original-PTS binary/index/scope relations, constructors and
executable witnesses for every original term, including untyped terms.
`InternalRenamingLookup` retains one rank-12 environment under binders and
proves every-output index boundedness, including an independent shift instance.
`InternalRenaming` defines the source-directed annotated graph at rank 16;
its rank-17 scope-preservation term passes isolated compilation, as do all
other new declarations (final renaming run: 811 seconds, exit 0).
No constructor assumes output scope or the bounded-environment contract.

The review confirms that global functionality and matching inversion are
unneeded for this consumer. RenAt does not assert target=base+depth; its
boundedness contract is not exact decoding. Next realize bounded-shift
renaming on every original t -> shift t, then construct fixed-base term-valued
lookup and single substitution. Native substitution correctness plus internal
scope coverage does not itself establish those bridges. Dependent typing/
conversion preservation, resource sufficiency and consistency remain open.

Fresh audit started 00:46:00 UTC. Pristine compilation/kernel checking pass;
fresh dependencies pass at 01:05:26 (1156 seconds). All 385/385 public reports
are closed at 01:06:20. Independent new-closure recursive checking ran
01:06:20–01:46:20 and timed out after 2400 seconds (exit 124), without reporting
a proof error. It did not produce a complete inventory, so inventory comparison
remains unverified; this is not a complete audit pass. Separate post-timeout
checks confirm unchanged proof/common sources, exact before/after manifest
equality, frozen note/PDF hashes and original-kernel agreement with pristine.
The recursive check is deliberately limited to the COMPLETE NEW dependency
closure; all 27 older proof sources match the preceding full audit's hashes.
No full CI or changed CI checks. Roadmap/PDF build 02 passes cleanly: 15 pages,
four links, full inspector and visual review of changed pages 11–15.
Exact contracts, failures, commands and live results:
[verification record](../../docs/direct-r-handoff/verification/self-consistency-substitution-2026-10-23/COMMANDS.md).
No staging, commit/push or cleanup; prior dirty work preserved.

## Consumer-directed preservation and weaker sufficient obligations

Four modules add 41 public endpoints. `RelationalTransport` gives rank-4
predicate descent and dual negative safety through lookup/history, with
explicit local laws. `OccurrenceSafety` constructs and propagates absence
of a represented Ext witness, with nonzero-leaf/pair base instances derived
from the independent Stop observation. This is not source rejection or a
complete native absence characterization. `LookupHomomorphisms` maps shape
and generated filling over Look_5, Look_6 and Hist at their existing ranks,
leaving paths unchanged. `SimulationRealization` separates native equations
from actual original-PTS application, then converts standard endpoints to
canonical quotations. Filling is only forward-preserving; a concrete native
counterexample refutes reflection.

The review finds no implemented consumer of full lookup functionality or
matching-constructor inversion. These remain optional open lemmas rather
than mandatory gates. The new laws avoid them for their specific consumers;
the actual proof-node invariant must still preserve EVERY related output.
Dependent uses need a shared result or a proved coherence law. Structural
resource sufficiency may avoid internal numerical comparison; invariant
preservation may avoid reifying complete transported derivations. Neither
option discharges soundness, resource sufficiency or standard admission.
For negative transfer, constructive forward acceptance realization is the
minimal direction; reflection is needed for exact checker identification.
An independent overapproximation must still satisfy soundness for every
acceptance proof. No acceptance definition is changed. An internal comparison
of consistency sentences needs uniform internal translation, not just
pointwise standard coverage.

Fresh dependency compilation passes at 23:33:26 UTC, separate endpoint
reports at 23:33:33: **283/283 closed** (41 new). Recursive kernel checking
passes at 00:03:42 UTC (23 October), in 1809 seconds. The complete inventory
equals pristine exactly: only unchanged functional_extensionality_dep, no
unsafe entries. Every audit stage exits 0, including original-source and
before/after stability checks; no timeout. Original/common sources and all
23 previous proof modules match their starting hashes. The revised roadmap
builds cleanly: 14 nonempty pages, four links, required text/math and all-page
renders; changed pages 4, 10–12/14 reviewed. Exact commands, failures and contracts:
[verification record](../../docs/direct-r-handoff/verification/self-consistency-relational-2026-10-23/COMMANDS.md).

First concrete next operation: independent capture-avoiding replacement on
annotated source codes, scope preservation and exact standard agreement
with original Syntax.subst, then the dependent semantic/typing contract.
No full CI, commit or push. Historical entries below retain their original
theorem boundaries; their old mandatory-priority statements are superseded.

## Fixed-rank histories, stratified cases and structural capacity

Six new modules retain the original carrier, generation guard and Look_5/
Look_6 relations. `LookupInversion` gives a rank-12 case eliminator from
independently specified Look_9, with actual Look_5 child proofs;
`InversionRealization` supplies executable standard coverage. This is not
matching-constructor inversion. The full functionality target is only
formed at U8, not inhabited or assumed.

`LookupHistory` defines independent root/segment histories at rank 10 and
proves a rank-11 internal Hist -> Look_5 theorem by the existing composition
term. `HistoryRealization` computes witnesses for arbitrary finite successful
segment lists, with exact independent sequential-lookup erasure and original
typing; the integrated theorem applies internal soundness. History length
does not raise the interface rank. No arbitrary Look_5-to-Look_6 lift or
same-rank Look_6 closure is asserted.

`InternalCapacity` supplies tag-erasing shape and rank-6 structural capacity,
with internal generation, reflexivity/transitivity, extension/join and
lookup/history laws. `CapacityBounds` proves exact beta correspondence,
native-to-PTS shape-subtree realizations and a common explicit budget for
every supplied finite family. Numerical packing/fill and flattened-path bounds remain
external. There is no converse or native numerical bound extracted from
arbitrary Cap inhabitants, and no checker/normalizer sufficiency premise.

Fresh dependencies pass at 22:24:58 UTC and separate public reports at
22:25:04: **242/242 closed**, 48 new. Recursive kernel checking passes
22:25:04–22:41:15 (971 seconds); complete inventory equals pristine exactly:
only unchanged upstream functional_extensionality_dep, no unsafe entries.
Every stage passes, including original-source and before/after stability
checks; there is no timeout. Original/common sources and
all seventeen prior proof modules match their starting hashes. The roadmap
builds and validates (13 pages, four links, all-page rendering), with changed
pages 8–10/12 visually reviewed. Exact contracts, commands, failures and logs:
[verification record](../../docs/direct-r-handoff/verification/self-consistency-closure-2026-10-23/COMMANDS.md).

Full functionality/matching inversion, operation/proof-history bounds,
complete resource admission, all-budget soundness and consistency remain
open. No impossibility claim, full repository CI run, commit or push.
The entries below retain their historical theorem boundaries.

## Stratified path composition and root/leaf separation

Four new modules extend the unchanged carrier, guard and lookup interface:
`InternalPaths`, `PathSubstitution`, `ResourceSeparation`, `PathRealization`.
They give actual original-PTS structural substitution with generation/unit/
associativity laws; exact beta correspondence on every standard raw tree;
an independently specified higher-rank lookup relation and a rank-9 internal
composition term; executable standard coverage and application of that term
at exact concatenated-path types. Composition takes Look_6 and Look_5 proofs
and returns Look_5, not a same-rank or arbitrary-lifting theorem.

Independent type-valued observations give internal root functionality for
Eq_0, both root/value equality directions, and leaf/step rejection. They
operate on arbitrary represented arguments, not only quotations, and use
neither normalization nor external nontriviality. Eq_0 quantifies exact
rank-0 predicates; it is not native syntax equality. Full arbitrary-path
inversion/functionality and fixed-interface iteration remain open, as do
size/capacity, resource admission, all-budget soundness and consistency.

Fresh audit passes **18:05:33–18:16:53 UTC**, every stage exit 0. Dependency
build passes 18:08:11; separate reports at 18:08:17 are **194/194 closed**
(28 new). Recursive kernel checking passes in 516 seconds; complete inventory
equals pristine upstream exactly, with only unchanged functional extensionality
and no unsafe entries. Source manifests are stable. Prior thirteen proof
modules, original kernel and shared infrastructure match their starting hashes.
Exact commands, compiler errors
and final audit status are in the
[verification record](../../docs/direct-r-handoff/verification/self-consistency-paths-2026-10-22/COMMANDS.md).

The roadmap/PDF builds and validates: 12 nonempty pages, four links, required
text/math, all-page rendering, changed pages 8–9 and final work-package page
11 visually reviewed. Final clean diagnostics. The initial inspector failure
was a missing output directory, fixed without changing its checks. No full
repository CI, commit or push. Older entries below retain historical boundaries.

## Fixed-rank structural resource graphs

`ResourcePaths`, `InternalResources`, and `ResourceRealization` supply
independent external lookup and structural paths, originally typed rank-6
prefix/extension and rank-7 lookup relations, and actual reflexivity,
transitivity, joining, generation-preservation and lookup-to-extension terms.
Root/step rules use independent structural guards. Exact positive padding
supplies rank-5 motives without cumulativity; quantified step/extraction/
extension laws have rank 8. The original carrier and generation predicate
are unchanged. Prefix means left-spine append, not two-sided extension.

Executable external lookup-witness generation erases exactly to the
independent algorithm and returns originally typed PTS proofs. All standard
prefixes/extensions are realized. Exact external bounds count the selected
subtree and the entire structural path. No Church numeral conversion is used.

Fresh audit **17:36:43–17:43:35 UTC**, all stages exit 0: **166/166** closed
public reports; recursive kernel check succeeds in 295 seconds within the
unchanged 300-second limit. Complete context inventory equals independently
rebuilt pristine upstream: only unchanged `functional_extensionality_dep`,
no unsafe entries. Source manifests are stable; original kernel, common
infrastructure and all ten previous proof modules match prior hashes.
Exact commands, failures, hashes and note validation:
[verification record](../../docs/direct-r-handoff/verification/self-consistency-resources-2026-10-22/COMMANDS.md).

The roadmap/PDF now records these contracts and boundaries (11 pages, four
links, successful build/inspection/rendering). Arbitrary-input internal
lookup functionality/no-junk, path composition, size/capacity comparison,
full resource admission and all-budget soundness remain open. Rank-4 extension
transport does not imply transport of rank-7 lookup claims. No converse
parametricity or internal consistency theorem is claimed. No full repository
CI run, commit or push; earlier entries retain their historical boundaries.

## Fixed original-PTS carrier and guarded finite pilot

`InternalCarrier`, `GuardedTables`, and `FiniteRejection` provide actual
closed terms and proofs in the ORIGINAL `Typing.typ` judgment. The shared
annotated assembler and sound successful-run checker are reused unchanged;
neither arithmetic interpretation nor a set model is imported.

The fixed 29-leaf/binary-pair Church carrier has rank 2. Its independent
constructor-generation guard has rank 4, and pair generation type rank 5.
Executable quotation/generation covers every raw tree, including malformed
and rejected inputs; quotation is syntactically injective. No all-inhabitant
parametricity or resource-admission theorem is claimed.

The Boolean pilot has rank-3 exact-motive guards. Originally typed rank-4
laws prove binary elimination, table closure and pointwise equality on
arbitrary guarded inputs. Four entries are ordinary arguments at a fixed
interface. Separate expansion laws handle lookup without eta conversion.
The rejection pilot completely covers closed height-zero native certificates
with labels at most 1; its table is generated by the independent checker.
Local syntax equations justify rejection on all guarded selector inputs,
without global normalization or external Bottom emptiness.

Fresh focused audit passes all stages, 17:09:43–17:11:55 UTC: **127/127**
closed public reports; successful recursive kernel check; exact full
dependency-inventory equality with independently rebuilt pristine upstream.
Only unchanged upstream `functional_extensionality_dep` occurs, with no
unsafe entries. Kernel and seven prior proof modules are unchanged; shared
infrastructure has no diff. Source manifests before/after the audit match.
Full commands, failures and hashes:
[verification record](../../docs/direct-r-handoff/verification/self-consistency-guards-2026-10-22/COMMANDS.md).

The roadmap/PDF now marks these milestones checked. Fixed-carrier resource
relations, internal decoding/compression, resource admission, operation and
transport/history bounds, all-budget soundness and consistency remain open.
No full repository CI run, commit or push at this checkpoint.
Earlier entries below record their historical verification boundaries.

## Homogeneous serialization and serialized-size bounds

Three new modules complete the external serialization milestone:
`StructuralCodes`, `CertificateSerialization`, and `SerializationBounds`.
A finite-alphabet tree type represents binary labels, scoped annotated terms,
beta instructions, equality trees, typing/context certificates and complete
inputs. Both decoder inverse laws and syntax injectivity are proved. Raw
checking is sound and complete for original derivable judgments in well-formed
contexts; raw compression preserves acceptance and does not require acceptance
to parse an input. Every compressed label is bounded by the full serialized
input's node count. Repeated fields and all binary payloads are counted.

The fresh focused audit passes every stage, 16:34:14–16:34:45 UTC:
85 public endpoints, 85 closed reports, successful recursive kernel check,
and exact context-inventory agreement with fresh pristine upstream. Source
manifests are stable and original kernel files unchanged. Full commands,
incremental failures and hashes are in
[the serialization verification record](../../docs/direct-r-handoff/verification/self-consistency-serialization-2026-10-22/COMMANDS.md).

The updated roadmap builds in `/tmp/pts-rk-consistency-note.M0yWcS`; PDF
inspection/rendering passes. These results concern external Rocq data and
algorithms. Fixed-rank PTS representation, guards, internal finite-table laws,
operation-cost bounds and the bounded-history proof remain open. Resource
admission must cover malformed/rejected raw trees as well as decoded inputs.
No commit or push; earlier checkpoint records remain below.

## Rocq certificate and compression milestone

`PTSrk.SelfConsistency` now supplies independent executable certificates,
soundness/completeness for the original six-rule typing relation and contexts,
sort relabeling, and complete-input source-rank compression. The coverage
theorem `every_original_judgment_compresses` includes every native derivable
judgment in a well-formed context. All 43 public audit endpoints are closed.

Fresh compilation and recursive kernel checking pass, 12:38:45–12:39:13 UTC,
with the same full dependency inventory as independently rebuilt pristine
upstream. A report-count harness error was detected in the earlier run and
fixed before the fresh successful rerun. Exact contracts, commands, failed
attempts, versions and hashes are in
[the native-certificate verification record](../../docs/direct-r-handoff/verification/self-consistency-native-2026-10-22/COMMANDS.md).

The updated DIRECT_ROADMAP.tex/PDF builds in
`/tmp/pts-rk-consistency-note.86KaLm`; PDF inspection passes for nine pages
and four links, with all-page rendering and visual review of changed pages.
The initial overflow failure is retained. No full CI run, internal bounded
soundness or internal consistency theorem is claimed. No new commit/push.
The older entries below describe their historical checkpoints.

## Direct route without H or EA intermediaries

[DIRECT_ROADMAP.tex](DIRECT_ROADMAP.tex) and [its PDF](DIRECT_ROADMAP.pdf)
give the current recommended direct programme: independent native certificate
codes, elementary source-rank compression, guarded internal finite reasoning,
one fixed-type resource interface, internal bounded proof/history soundness,
terminal separation and negative resource elimination. Neither the guarded
soundness theorem nor a consistency inhabitant is reported as proved.

The roadmap corrects the starting-point distinction: current combinatory
soundness is external Agda soundness in graded finite syntactic carriers,
not yet internal PTS soundness or fixed finite first-order models. It also
distinguishes the new structural consistency sentence from the earlier
finite-ordinal target and includes the conditional incompleteness audit.
Three independent source/mathematical reviews checked these boundaries.

Final command `bash theories/self_consistency/build-note.sh DIRECT_ROADMAP`
exits 0, 12:01:53–12:01:58 UTC, in
`/tmp/pts-rk-consistency-note.O8CmUV`: eight pages, clean layout/reference/
glyph diagnostics. The PDFKit inspector exits 0, checks required text,
primary reference and mathematical rendering, and renders every page.
Changed formulas and final pagination were visually reviewed. An earlier
malformed equation tag was detected and corrected; all failed/successful
attempts and exact commands are retained in
[the direct-roadmap verification record](../../docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/COMMANDS.md).

```
37ee293ca952bac4a7507ad734be6d4f9c50b6266d211ef32e5eaff97bdf6a34  DIRECT_ROADMAP.tex
37c5618148dc74f12e797e5d21639e87ac6fda2e27c03d2f7d83d58cdb3119a3  DIRECT_ROADMAP.pdf
```

All 244 inspected proof/Dune sources match their before/after hashes.
No Rocq/Agda proof sources, original draft, or earlier README.tex/PDF were
changed in this turn; no new proof build, staging, commit or push. The new
optional build-script argument preserves the old no-argument behaviour.

## Follow-up: shared tag-free folds and structural codes

The shared-algebra continuation adds a short paragraph to the uniform-PHOAS
analysis: `UnifiedAlgebra` gives tag-free full-dependent execution, while
STLC and finite-dictionary combinatory folds supply actual alternative
interpretations. These results do not supply acceptance soundness, a
rank-only dependent signature, native combinatory completeness, or an
internal consistency inhabitant. Structural recoding must still match the
specified arithmetic sentence on all admitted certificates and traces.

`bash theories/self_consistency/build-note.sh` exits 0 in
`/tmp/pts-rk-consistency-note.7vQRc9`: ten pages, no overfull/underfull,
undefined-reference or missing-glyph diagnostics. The new fold-audit
`inspect.swift` exits 0, renders all ten pages and checks required text;
page 7's added passage was visually inspected. Raw logs and renders:
`_build/self-interpreter-fold-audit.7pRHdb/consistency-note.log` and
`consistency-pdf/`. Current document SHA256:

```
7c84b193ff70194c326fbed0ecff18c948d0ab2771bf5e15afa0f9cd5c0c7bf5  README.tex
a6b58a5e04fa80ebcb7cd5cdfb1b9a9d08355774106db49c3a917ab433dedfb6  README.pdf
```

No self_consistency Rocq library or theorem has been introduced.
Proof evidence belongs to the separate self-interpreter fold audit.

## Follow-up: fixed fragment execution interface

The original five-file documentation checkpoint below was committed as
`cb76553b03d536743e36c4e2c7e5a1c7c1669bef`, at the user's subsequent request.
No push was requested. The note now reflects the new fixed closure interface
and its precise difference from internal proof-code reification. This changes
the status of the second uniformity, not the internal consistency target.
The new proof evidence belongs to
[the self-interpreter continuation](../../docs/direct-r-handoff/verification/self-interpreter-uniform-interface-2026-10-22/COMMANDS.md),
not to a self_consistency Rocq library; none has been created here.

Follow-up declarations: `FragmentClosureInterpreter.every_bounded_original`,
`FixedInterface.inhabited_iff`, and
`BudgetInternalization.no_unbounded_internal_strong_reification`.

Document attempts: `/tmp/pts-rk-consistency-note.OmKWDX` failed overflow
validation (exit 1), preserving the preceding PDF; the long qualified theorem
name was split in prose. `/tmp/pts-rk-consistency-note.L5IDV1` built successfully
but had one underfull paragraph. `/tmp/pts-rk-consistency-note.7u3pxt` is the
final successful build: ten pages, no overflow/underflow/reference/glyph
warnings. PDFKit section/link/text/render validation passes. Inspection output
is under `_build/self-interpreter-uniform-interface-2026-10-22/consistency-note`.
Final follow-up SHA-256 values:

```
cb1b496a89d30d6edb8cc26ba3972ec54a717297acacf5dc5da66ec242e1e73b  README.tex
f37a83f973a114b6d6aa0c0287027a4c80c12334846b8786d6792ce89b66f149  README.pdf
```

## Provenance

This is a documentation-only research checkpoint, 22 October 2026, based on
repository commit `72c9f337224eef9922e3d1949e15bcd4148224b7`. Existing unrelated
documentation, CI and BZC work is preserved. No commit or push was requested
for this checkpoint. No new Rocq theorem, EA derivation or PTS consistency
inhabitant is claimed.

Input supplied by the user:
`/Users/akuklev/Downloads/Logical_and_computational_strength_of_PTS_rk_Zermelo_revision.tex`.
SHA-256:
`0c3a1cd7671abf61e980426e9174344946691d2c260c9c74bdcb1bacb68435c8`.
The original file is unchanged and is not copied into this directory.

Relevant draft labels, in dependency order:

- `eq:internal-target`, `def:bs`, `thm:conditional-self-consistency`,
  `prop:adequate-height` (lines 1068–1290).
- `lem:rank-compression` (1295–1327).
- `lem:ea-constant-separation`, `lem:tagged-projection`,
  `sec:graded-calculus` (1665–1920).
- `lem:source-tag-coherence`, `lem:source-elaboration` (1922–2218).
- `lem:structural-templates`, `lem:aux-one-step`, `lem:active-passes`,
  `lem:aux-terminal`, `thm:bs-proved` (2220–2468).
- `cor:internal-consistency-completed`, `sec:internal-sn-scope`,
  `prop:no-pi2-transfer` and review limitations (2470–2679).

The former WC formulation, quantitative residual joins, unrelated complexity
hardness and model appendices are excluded from the core proof dependency
chain. The note preserves the draft's status as an unformalized argument.

Primary external reference checked directly:
[Fedor Pakhomov, *A weak set theory that proves its own consistency*,
arXiv:1907.00877v2](https://arxiv.org/pdf/1907.00877v2).
Section 2 defines the higher-order theory; Lemma 3.11 (page 18) is the
predicate-only Pi1 transfer using S; Corollary 5.3 (page 22) uses 2S and
the first-order theory. Appendix A's comparison with R is first-order.
These results are identified as external mathematical dependencies, not Rocq
axioms. Checking the citation does not formalize its proof.

## Repository declarations inspected

- [BoundedNormalization.v](../NormalizationComplexity/BoundedNormalization.v):
  `fixed_rank_normalization`.
- [Normalization.v](../NormalizationComplexity/Normalization.v):
  `normalization_in_TOWER`, `rank_bound_in_linear_time`.
- [FullSource.v](../self_interpreter/FullSource.v): `derivation_iff`.
- [DirectRDerivationCertificates.v](../Interpretation_of_R/DirectRDerivationCertificates.v):
  `DerivationCertificates.derive_sound`, `derive_complete`.
- [OriginalTypecheck.v](../self_interpreter/OriginalTypecheck.v): `check_iff`.
- [FullDependentInterpreter.v](../self_interpreter/FullDependentInterpreter.v):
  `every_closed_original`, `every_original`.
- [CappedDependentInterpreter.v](../self_interpreter/CappedDependentInterpreter.v):
  `every_bounded_original`, `fragments_cover`, `quote_at`.
- [CappedInterpreter.v](../self_interpreter/CappedInterpreter.v): `rank_uniform`.
- [DependentProgramDecoder.v](../self_interpreter/DependentProgramDecoder.v):
  `evaluate_typed`, `decoder_typed`.
- [PlanNonuniformity.v](../self_interpreter/PlanNonuniformity.v),
  [FiniteCoherenceCatalogue.v](../self_interpreter/FiniteCoherenceCatalogue.v),
  [LiteralObstruction.v](../self_interpreter/LiteralObstruction.v): scope of
  plan, literal-field and sort-literal obstructions.
- [DirectRFunctionalDeduction.v](../Interpretation_of_R/functional/DirectRFunctionalDeduction.v):
  `FunctionalDeduction.sentence_preservation`.
- [DirectRTheorem7.v](../Interpretation_of_R/functional/DirectRTheorem7.v):
  `Theorem7.effective_deduction`, `theorem5_target`, `theorem7`.
- The normalization/self-interpreter/arithmetic READMEs and BZC foundation audit
  distinguish implemented results, unformalized elementary representability,
  native semantic agreement and material deduction.

No proof files or Dune files changed, so no new Rocq build or assumption audit
was run or claimed. Historical audits remain in the corresponding development
handoff records; they do not verify any new consistency proof.

## Document validation

Build command: `bash theories/self_consistency/build-note.sh`.
The script uses the existing repository Markdown runtime and development
preamble, retains intermediate output in a scoped temporary directory, and
publishes the PDF only after compilation and reference/glyph/overflow checks.
Tool versions: latexmk 4.88, LuaHBTeX 1.24.0, TeX Live 2026.

Recorded attempts:

- `/tmp/pts-rk-consistency-note.F85DFD`: exit 12, unsupported `\tag` inside
  the Markdown display renderer. Replaced by explicit parenthesized labels.
- `/tmp/pts-rk-consistency-note.NFldQl`: TeX exit 0, validation exit 1,
  overlong code-name prose in the roadmap. PDF not published.
- `/tmp/pts-rk-consistency-note.CQHNKd`: TeX exit 0, validation exit 1,
  overlong code-name prose in the theorem map. PDF not published.
- `/tmp/pts-rk-consistency-note.qZxUGL`: build and validation exit 0,
  ten pages; PDFKit text, source-link and render checks passed. The final
  provenance paragraph was subsequently shortened to avoid a sparse last page.
- `/tmp/pts-rk-consistency-note.KlGtoS`: final build and validation exit 0,
  nine pages. No overfull/underfull boxes, LaTeX warnings or missing glyphs.
  PDFKit text/section/source-link/render inspection exits 0; pages 1, 3, 5,
  7 and 9 were visually inspected. `bash -n build-note.sh` passes.

Final SHA-256 values:

```
4f12ef2c225d0f8f7db5fe8ea2850d5120b7094fcb8c73801487c6949076d382  README.tex
6a8fc111e750ad9e74a706cb2d24a2047dbb935bbf31d33105a46ebcf7a30a04  README.pdf
```

PDF inspection command:

```sh
swift _build/self-consistency-note-2026-10-22/inspect.swift \
  theories/self_consistency/README.pdf \
  _build/self-consistency-note-2026-10-22
```

Its text extraction, checked section/link coverage and sample page renders are
retained under `_build/self-consistency-note-2026-10-22`. This ignored directory
contains document-inspection artifacts, not proof evidence. The small temporary
TeX directories retain their build logs. No large new proof caches were created.

Three independent read-only reviews checked draft fidelity, repository theorem
contracts and the external transfer boundary. They prompted explicit tower-seed
comparison, higher-order comprehension/class-separation definitions, and the
internal link from the actual trace predicate to accepted PHOAS codes.
These reviews are mathematical/document checks, not formal verification.

Final repository checks: `bash -n` exit 0; tracked-document `git diff --check`
exit 0; proof/Dune comparison against HEAD exit 0; index empty. The four
new text files have no whitespace diagnostics from `git diff --no-index
--check /dev/null FILE` (exit 1 denotes the new-file differences). An initial
`set -e` wrapper stopped at that expected status; the checks were then run
individually. The final manuscript/PDF hashes still match the values above.
