# Live proof-development state — 2026-10-24

## Requested publication checkpoint

User authorized committing and pushing the combinatory presentations,
self-interpreter and internal-consistency developments. Combinatory sources
and their retained verification records are committed as aa70054; internal
consistency sources and records as a9fed96. Self-interpreter sources were
already committed (7854d1d); no pending source changes were found there.
Shared documentation and the self-consistency CI stage are being committed
separately. Unrelated BZC/prose changes remain in the working tree.
Existing focused verification remains the proof evidence. Publication check:
`OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec --switch=pts-rk-ci -- dune build @theories/CombinatoryLogic-rk/audit @theories/self_interpreter/audit @theories/self_consistency/audit`
was intentionally interrupted with SIGINT (exit 130) during dependency
recompilation, after about four minutes. No compiler error was observed;
load-path/deprecation warnings occurred. Output was streamed to the session,
not retained as a complete raw log; this is NOT a successful audit or fresh
assumption inventory. Shell syntax and staged documentation whitespace pass.
The existing NamedTemplates.v EOF blank-line warning is preserved to avoid
changing audited proof bytes. Mathematical goals remain as below; no new
proof source was edited for publication. Next exact command: `git push origin main`.

## Second-paper plan: documentation only; no new development requested

The user explicitly requested planning, not further implementation. The
introduction now states six goals: three principal binder-free Agda sources
(Church-encodable natural-model QIIRT, definitionally beta-canonical normal
model, cumulative whole-rank/length-bounded fragments with Church application
and native extraction); Hilbert/MM0 correspondence; partial finite models
and internal bounded soundness toward the specified consistency sentence;
indexed self-interpretation with source folds and typed CPS.
theories/CombinatoryLogic-rk/SECOND-PAPER-PLAN.md records seven milestones,
acceptance gates, existing components and exact remaining obligations.

No Agda, Rocq, MM0, Dune or build-driver changes. All 156 proof/configuration
files match the preceding checkpoint (79 Agda, 73 Rocq, Dune/MM0/two drivers).
No proof checks rerun. Documentation build PASS 03:13:21–03:13:37 UTC; PDF
inspection PASS 03:14:25–03:14:27 UTC: 42 pages, appendix 3, 72 Rocq/55 Agda
badges, 172 links. All pages rendered; 1–3 and 42 reviewed. Six-goal/order
check PASS.
Evidence: verification/combinatory-paper-plan-2026-10-24/COMMANDS.md.
Existing user changes preserved; no staging/commit/push.

Do not resume formal construction until the user requests it. The first
planned step is to freeze the three shared interfaces, closed definitional
equality target, internal-rank/label/size grades, Church/extraction contracts,
source-fold interface and precise internal consistency predicate. Earlier
proof checkpoints below describe reusable work, not completion of this plan.
Next documentation check: `bash theories/CombinatoryLogic-rk/build-note.sh`.

## Combinatory logic: dependent normal algebra and original raw checker

Seven new safe Cubical modules, 1,523 lines. NormalizedFamilies constructs
normal types/inhabitants with ORIGINAL truncated typing, dependent substitution
action, identity/composition paths and beta correspondence. castNF changes
only typing evidence and agrees with whole-record transport. Comprehension
gives terminal/projection/pairing/last-variable operations, actual beta/eta/
uniqueness/naturality paths and lifting into normalized extensions. Products
gives structural Pi/lambda, universe/El, normalizing dependent application,
original beta and typed product/lambda/application naturality. No function eta.

NormalizedInference computes the normal type/rank from mere original
typability, proves witness independence and the typed-fibre isomorphism,
and covers every original derivation. NormalizedContexts is genuine IR of
contexts and decoding, extending by normal declarations. Mere well-formedness
is derived internally; normalization/action/computed types require no supplied
witness. NormalizedExamples computes dependent substitution f U0, polymorphic
identity's two applications, and witness-free IR operations by refl.

NativeBidirectional now structurally decides ORIGINAL Typ for arbitrary raw
annotated subject/type in a well-formed context. It constructs original typing
before normalizing types; rejection refutes all original derivations. The raw
context entry decides WellFormed Γ × Typ Γ t A, not bare Typ in malformed Γ.
Nine positive/negative/reducible-type tests compute by refl. This closes raw
original typing decision, beyond the preceding certificate-only interface.

Fresh aggregate 79 Agda PASS 02:38:49–02:42:19 UTC, exit 0/zero warnings;
pinned Agda 2.8.0-3d04bac/Cubical v0.9, copied sources/isolated config/data,
--safe --ignore-interfaces. All 146 baseline files unchanged: 73 combinatory
Rocq, 71 preceding non-aggregate Agda, Dune/MM0. No Rocq/MM0/full-CI rerun.
Note PASS 02:37:19–02:37:36 UTC; PDF inspection PASS: 41 pages, appendix3,
72 Rocq/55 Agda badges, 171 links. All pages rendered; nine visually reviewed.
Evidence: verification/combinatory-dependent-normal-2026-10-24/COMMANDS.md.
Final Products/Examples fresh passes also succeed under a 2 GiB heap cap.
Earlier interrupted/metavariable checks and two overlapping-driver diagnostic
limitations are retained; no positivity/termination checks were disabled.
HEAD 6a8dc984 unchanged, existing staged/unstaged user work preserved;
no staging/commit/push. Seven new proof sources are untracked.

Full combinatory QIIRT replacement remains OPEN. Current normal operations
use native binders and the proved native normalizer. The mutual IR only
defines contexts/decoding, not all normal syntax/hereditary evaluation.
First remaining goal: package a literal QIIRT interpretation (its Sub index
order is reversed), proving context sethood/adequacy, exact dependent S/K/P
template/guard realization, and every path. Then source completeness,
equality reflection and the full positive/terminating mutual IIRT. A direct
arbitrary-output SK canonical evaluator and whole-presentation code savings
remain separate obligations. Next exact check:
`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`.

## Combinatory logic: normal-first operations and direct ground evaluation

Eight new safe Cubical modules (852 lines). SKSourceRank supplies a pure
syntax budget, integrated into SKSourceNormal (+7 lines), avoiding proof
evaluation; SKCanonicalExamples now computes public canonical operations by
refl. Parallel draft adapters were consolidated, not retained as a second
active normalizer. Existing canonical soundness/coherence/reflection remain.
SKBracketSize proves compiler output <=4^source-nodes and canonical output
<=4^(tower d N), with computed source budget d and annotated expansion size
N. This counts S/K/ground atoms, not payloads, intermediates or memory.

SKDirectSoundness proves weak SK traces expand forward to native beta at
all simple types. SKDirectGround gives directly binder-free canonical
normalization/application/conversion decision at ground output. The checked
SKDirectBoundary counterexample has canonical inputs but a four-atom weak
function output versus an eight-atom canonical output. Weak application alone
is insufficient at function output; stronger direct evaluation is not ruled out.

CanonicalAlgebra gives computed-type fibres and normalizing application
using ordinary Sigma, not a full dependent IIRT. NormalizedSubstitution
normalizes ORIGINAL dependent valuations. Its SubNF stores normal images
and truncated original typing witnesses; witness independence, actual
identity/associativity paths, retraction and exact beta correspondence are
proved. No category law is imposed as a quotient constructor. This is not
normalized dependent type action/comprehension/products or QIIRT initiality.
The note explains mutual normal syntax/hereditary operations as a design
target: quotient elimination can disappear, but termination, positivity,
substitution/product coherence and original-typing adequacy still need proofs.

Fresh aggregate 72 Agda PASS 01:48:29–01:49:30 UTC, exit 0/zero warnings;
pinned Agda 2.8.0-3d04bac/Cubical v0.9, copied sources/isolated config/data,
--safe --ignore-interfaces. All 73 Rocq and 62 unchanged prior Agda,
Dune/MM0 hashes agree (137 files). No Rocq/MM0/full-CI rerun.
Final PDF PASS 01:49:44–01:50:00 UTC: 39 pages, appendix 3,
72 Rocq/48 Agda badges, 164 links; all pages rendered, 15 visually reviewed.
Evidence: verification/combinatory-normal-first-2026-10-24/COMMANDS.md.
Early memory failures/interruption are retained; a smaller proved truncation
eliminator fixes the final dependent-substitution check, including a fresh
1500 MiB-capped worker run. No checks or statements were weakened.
HEAD 6a8dc984 unchanged. Existing staged/unstaged user work preserved;
no staging/commit/push. Eight new sources are untracked.

First remaining goals: normalized dependent type action, context extension
and product naturality over SubNF; and an arbitrary-result, beta-sensitive
closure/spine evaluator agreeing with SKCanonical without lambda intermediates.
Then prove the positive/terminating simultaneous IIRT and full dependent
catalogue/QIIRT adequacy. Do not assume eta or identify weak SK equality with
native beta. Atom-output bounds are closed; payload/runtime bounds and full
presentation code savings remain open. Next exact check:
`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`.

## Combinatory logic: canonical SK outputs for native beta

Six new Cubical modules,972lines: SKSource261,SKSourceEquality146,
SKSourceNormal54,SKBracket264,SKCanonicalNormal97,SKCanonical150.
Source greedy passes commute with original annotated erasure. Erasure is
injective at fixed context/simple type, recovering hidden application
domains. Native rank coverage supplies total source normalization, not a
partial native parser. Deterministic bracket compilation has forward native
beta correctness; compiling normal closed sources gives actual Core.Nf.
The composition returns irreducible SK outputs and proves native-beta
soundness/coherence/reflection/idempotence. Its fixed-point family is
isomorphic to the native-beta quotient; application agrees. check-canonical
decides the independent simple SK judgment and returns a canonical output.

This is not direct binder-free evaluation or full dependent PTS coverage.
Typed lambda syntax remains internal; soundness is native beta equivalence,
not a forward weak-SK trace. No new output-size/runtime bound, eta rule or
replacement of original Typ is introduced. Optional large computation tests
caused excessive memory use and were stopped, then removed; logs preserve
exit143 and snapshots. General proofs and small regressions pass.

Fresh aggregate64Agda PASS01:06:10–01:07:02UTC,exit0/zero warnings,
Agda2.8.0-3d04bac/Cubicalv0.9,copied sources/isolated config/data,
--safe --ignore-interfaces. All73preceding Rocq/57non-aggregate Agda,
Dune/MM0 hashes unchanged (132files). No Rocq/MM0/full-CI rerun.
Final note PASS01:07:46–01:08:02UTC:37pages,appendix3,
72Rocq/40Agda badges,156links; all pages render,10–12 reviewed.
Evidence: verification/combinatory-sk-canonical-2026-10-24/COMMANDS.md.
HEAD6a8dc984 unchanged; existing staged/unstaged user work preserved.
No staging/commit/push. Six new Agda sources remain untracked.

First remaining goal: direct canonical-image application agreeing with
SKCanonical.apply-and-normalize, without native lambda intermediate.
Then dependent catalogue coverage and QIIRT path compatibility against
original typing; compiler-output size bounds and economical integration
are separate obligations. Next exact check:
`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`.

## Combinatory logic: SK surface and beta-faithful reference

Latest requested SK migration is implemented. Active sources/paper contain
no superseded basis implementation; historical logs remain historical.
SK.v (473 lines) gives a deterministic intrinsic simple-type compiler into
S/K with original annotated typing and forward beta correctness. Conversion
is preserved/reflected on source expansions; normal source expansions are
equal iff their compiled expansions are beta equal. Numerals have10n+4
atoms; ranks, arithmetic and unapplied native normal forms are proved.
No native-NF parser, canonical SK code equality or dependent compiler is claimed.

Six direct Agda modules now1021 lines versus1168, retaining total weak
normalization, independent checking and the weak quotient isomorphism.
Every SK expansion is natively typed. SKNativeCanonical (121 lines) adds
actual native-beta normalization/decision, native-output idempotence and
apply-and-normalize, and a native-beta quotient with injective normalization,
decidable equality and application. It still returns native binder syntax.
Contextual QIIRT now has S/K/P, no primitive identity; certified SKK
computation is derived. Its full polymorphic/dependent coverage is open.
Native Hilbert catalogue logical identity schemes remain independently valid.

Fresh full active73-module Rocq audit PASS00:36:32–00:39:56UTC:1215own/
1216aggregate closed reports,23new SK endpoints. Recursive kernel32s;
full inventory byte-equals fresh pristine, inherited funext only, unsafe none.
All72 retained Rocq bodies/native kernel/MM0 unchanged. Fresh complete
58-module Agda closure PASS00:36:05–53UTC,exit0/zero warnings; all48
unaffected Agda sources stable. Note/PDF PASS00:38:11–26UTC,36pages,
appendix3,72Rocq/34Agda badges,150links; all pages render,2/10/11 reviewed.
Evidence: verification/combinatory-sk-2026-10-24/COMMANDS.md.
No staging/commit/push/full-repository-CI/MM0 rerun. Existing dirty work kept.

First remaining goal: reify the native normalizer's output into intrinsic
simple-type source syntax, fixing all hidden type choices deterministically;
then compose with SK.compile to obtain actual canonical SK codes. Prove
direct canonical application agrees with that reference before extending
dependent coverage/QIIRT path compatibility. The native reference quotient
does not discharge these obligations. Next verification:
`bash docs/direct-r-handoff/verification/combinatory-sk-2026-10-24/AUDIT.sh`
and the pinned `check-agda.sh` invocation in the evidence ledger.

## Combinatory logic: direct binder-free normalizer and quotient

Latest user task concerns a binder-free normalization/QIIRT integration,
not further finite-Horn work. Six additive safe Cubical modules implement
an independent simply typed BCKWI calculus: Core409, Bidirectional293,
Coherence126, Equality123, Quotient77, Boundary140 lines. Total direct
normalization constructs forward typed traces; normal forms are irreducible.
Independent declarative typing is decidable. Weak conversion iff equality
of normal forms, discrete annotated normal syntax, actual quotient/Nf
isomorphism and shared normalizing application are proved. No fuel,
native-expansion oracle, postulates or unsafe pragmas. Ground labels are
inert test-calculus data, not new PTS primitives.

The full requested dependent replacement is NOT achieved. Native-typed
counterexamples show B I I and I weak-normal but beta-equal in original PTS;
B I and arrow-typed I are beta-distinct, so eta is not a valid repair.
Current QIIRT/native IIR/normalizer and finite bounds remain intact.
No new PTS rank/size bound, arbitrary-strategy strong normalization or
reduction in full-system code size is claimed. The original typing judgment
has not been replaced by the prototype's checker.

Fresh complete 58-module Agda closure PASS, exit0/zero warnings,
2026-10-24 00:03:14–00:04:04 UTC. Pinned Agda2.8.0-3d04bac/Cubicalv0.9,
isolated copies/config/data, --safe --ignore-interfaces. Build
/tmp/pts-rk-combinatory-agda.At6TF2, final logs
/tmp/pts-rk-binderfree-final.j8zDif; source stability passes. All51 preceding
non-aggregate Agda,74 combinatory Rocq,Dune,MM0 hashes unchanged;
Everything adds six imports. No Rocq/MM0/full-CI rerun or git index change.
Final note build PASS00:04:39–54UTC,35pages,appendix3,72Rocq/33Agda badges,
149links; all pages rendered,9–11 visually reviewed.
Evidence: verification/combinatory-binderfree-2026-10-24/COMMANDS.md.

First remaining goal: develop a beta-sensitive combinatory canonical form
retaining native annotations, prove its original-beta soundness/completeness,
then supply dependent catalogue coverage and QIIRT path compatibility.
Only then extend bidirectional checking and compare equal-coverage code size.
Next exact check:
`AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh`.

## Self-consistency: uniform Horn interfaces and finite raw tables

Five new frozen modules, 104 public endpoints: UniformHorn 19,
UniformHornReindex 16, UniformGuardedHorn 16, FiniteRawDecoding 31,
FiniteRawTables 22. UniformHornAudit checks/prints every endpoint; exactly
six additive module registrations, one alias and one full-Audit import.
Existing proof bodies remain unchanged. No staging, commit, push or cleanup.

Fresh focused audit PASSES, exit 0/archive 0, 23:33:49–23:35:50 UTC
(24 October locally). Compilation 69s, 23:34:06–23:35:15: 64 actual native
modules, 414 closed reports including 104 new aggregate endpoints. Complete
recursive kernel 27s, 23:35:15–23:35:42, VM enabled. Full inventory equals fresh
pristine exactly: inherited functional_extensionality_dep only, unsafe none.
Old-body/source/registration/driver stability, original kernel and frozen
ZFC all pass. Live _build/self-consistency-uniform-horn-audit.lD2nv7;
fresh /tmp/pts-rk-uniform-horn-fresh.cCcZgE; pristine
/tmp/pts-rk-uniform-horn-pristine.oSFBh4; archive
verification/self-consistency-uniform-horn-2026-10-24/audit.V54reH.
Attempt 1 stopped before compilation on one terminal blank in the aggregate;
failure retained, blank alone removed. Worker history archived separately;
Decoding intermediate source snapshots and Tables01–07 snapshots were not
available, but commands/logs/hashes/times/exits and final sources are retained.
No full repository CI or unchanged older aggregate audit rerun.

Actual generic Horn terms bind fragment/clause/position data internally.
Unguarded proof fibers U4, node/consumer types U5, exact atom ranks 1/2.
Clause selection transports arbitrary proofs with typed fold/composition
beta laws. Explicit independent guards at exact ranks g=3/4 yield proof
rank g+2 and node/consumer type rank g+3. Empty/nonempty Enum_3 ranks remain
distinct. No concrete guard or interpretation handler is inferred.

Bare finite raw decoding now has exact type rank 2, no Enum premise, by
re-abstracting the raw algebra and dispatching only at X:U0. Canonical forward
reduction reaches an expanded quotation; literal beta laws identify it with
the old quote and canonical Enum_2 decoder. Both quoted forms retain syntax
injection. The separate Enum_2 route has type rank 4, literal forward output,
and independently typed standard admission of every raw tree at serialized
size. No arbitrary-output coherence, internal parser, eta or parametricity.

First remaining goal: instantiate actual raw clause/head/premise projections
and independent clause-generation guards, construct the corresponding
interpretation handler, and prove source-rule coverage/endpoint coherence.
See verification/self-consistency-uniform-horn-2026-10-24/NEXT-PROOF.md.
Generic elimination/reindexing is not this concrete model/source bridge.
Original-PTS-to-catalogue completeness, operational resource sufficiency,
milestone 4 and internally budget-uniform bounded soundness remain open.
Next exact verification command:
`bash docs/direct-r-handoff/verification/self-consistency-uniform-horn-2026-10-24/AUDIT.sh`.
Roadmap/PDF build and inspection pass 23:33:23–29 UTC: 9 pages, 6 links,
all pages rendered; 1/3/7/8/9 visually reviewed. Archive note.e1xHbA under the
same checkpoint. Final TeX/PDF hashes are recorded there.

## Combinatory logic: internal raw decoding and guarded computation

Five new frozen modules compile, with 130 closed public reports:
IndexedHornTransport 27, FiniteGeneratedCodes 23, FiniteMapCoherence 25,
MM0InternalDecoder 27, MM0InternalGuard 28. Five additive Dune registrations.
Fresh 74-module audit PASSES all gates, exit 0, 2026-10-23 22:55:34–22:59:07 UTC
(24 October locally):
live _build/combinatory-raw-internal-audit.i7AcKM; absolute build
/tmp/pts-rk-raw-internal.Cw6I7V; pristine
/tmp/pts-rk-raw-internal-pristine.mI4P4i; archive
verification/combinatory-raw-internal-2026-10-24/audit.lNl9UC.
Compilation 22:55:45–22:58:31 (166s) prints 1230 own / 1231 aggregate closed
reports, 130 new. Complete recursive kernel check 22:58:31–22:59:05 (34s)
passes; full inventory equals fresh pristine exactly, inherited
functional_extensionality_dep only, no unsafe entries. All 77 hashes are
stable; all 69 preceding proofs and the native kernel/MM0/52 Agda sources
are unchanged. Exactly five additive registrations, safety and whitespace pass.

Actual rank-four proof-to-proof translation accepts arbitrary open queries and
independent source proof inhabitants. The semantic-to-raw instance fixes
both supports before the query and proves every mapped-clause inclusion.
Reserve lists enlarge indexing only, not denials or inference constructors.
Raw least-model soundness composes separately at type rank four.

Independent Enum_r(q) contains only canonical finite generation, not a target
property. Formation rank<=max(3,r+1), consumer type rank<=max(4,r+2).
The guard graph producer uses Enum_1; separate Enum_3 inputs prove input and
Boolean projection coherence via rank-one Leibniz equality, with type rank five.
No bare-code exhaustiveness, cumulativity between evidence ranks or native
conversion is inferred. Canonical point constructors exist at every rank.
The structural raw graph is independent of the program; both Boolean outputs
are in support but only the correct one is a fact. Wrong answers have no
closed proof, accepted proofs externally reconstruct source-instance records,
and rejected entries are inert. These closed converses retain canonicity.

First remaining goal: internally reconstruct raw source Expr/substitution
records and their structural invariants, then abstract fragment/budget inputs.
Fixed table certificates do not supply a recursive raw-tree interpreter or
uniform budget-polymorphic soundness. Independent internal consistency and
original-PTS-to-catalogue completeness remain open; no new runtime/size bound.
Next exact verification command:
`bash docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/AUDIT.sh`.
Note/PDF build and inspection PASS 22:56:41–58 UTC: 33 pages, appendix 3,
72 Rocq / 27 Agda badges, 44 Agda links, 140 total; all pages render and 26/27/28
visually reviewed. Archive note.v704EG under the same checkpoint.
No earlier proof/kernel/Agda/MM0 edits, staging, commit, push or cleanup.

## Combinatory logic: internally indexed queries and raw guard provenance

Six new frozen modules compile individually,120 closed public reports:
FiniteTypeDispatch14, IndexedHornEncoding17, IndexedHornRealization17,
MM0GuardProvenance33, IndexedHornSoundness16, MM0IndexedReflection23.
Six additive Dune registrations; all63 prior proofs are unchanged.
Fresh69-module audit PASSES all gates,exit0,20:49:13–20:52:38UTC: live
_build/combinatory-indexed-provenance-audit.rya6B6; absolute build
/tmp/pts-rk-indexed-provenance.cjt8S0; pristine
/tmp/pts-rk-indexed-provenance-pristine.8LBsHH; archive
verification/combinatory-indexed-provenance-2026-10-23/audit.emobKi.
Compilation20:49:23–20:52:08(165s) prints1100own/1101aggregate closed
reports,120new. Complete recursive kernel20:52:08–35(27s) passes; full
inventory equals fresh pristine exactly, inherited functional_extensionality_dep
only, no unsafe entries. All72source/Dune/shared-equality/MM0 hashes are
stable, all63preceding proofs and original kernel/MM0/52Agda sources are
unchanged, and Dune adds exactly six registrations. Safety/whitespace pass.

The independent indexed family Proof(q) has rank3. One actual original-PTS
consumer binds arbitrary query q and proof p internally, with function TYPE
rank4. It returns T(q); only canonical selectors reduce to a particular
truth proposition. Generic typing is canonicity-free. Canonical source
exactness and Void specialization still use external canonicity. Semantic
support is fixed once; its duplicate positions need not have identical
indexed derivability. A checked negative regression enforces this boundary.

Raw structural guard/evaluator provenance independently distinguishes
overflow from zero, reconstructs actual selected source substitutions, and
reflects arbitrary raw proofs without alias-induced spurious derivations.
The separate indexed raw encoding externally reflects arbitrary CLOSED
inhabitants to source proofs, excludes overflow/Void, and covers exactly the
source theory over finite budgets. Its support remains externally query-
seeded; this is not yet an internal raw-Expr decoder/guard consumer.

First remaining goal: Church-realize raw source-instance/guard/decoder
provenance with internal correctness, first at fixed bounds, then represent
fragment budgets uniformly. No independent internal consistency theorem,
original-PTS-to-catalogue completeness or code-size/runtime bound is added.
Next exact verification command:
`bash docs/direct-r-handoff/verification/combinatory-indexed-provenance-2026-10-23/AUDIT.sh`.
Note/PDF build and inspection PASS20:48:12–29UTC,32pages,appendix3,
67Rocq/27Agda badges,44Agda links,135total; all pages render and pages1/25/26
visually reviewed. Archive note.5KCYYS under the same checkpoint.
No old proof/kernel/Agda/MM0 source changes, staging, commit, push or cleanup.
Other-thread state below is preserved.

## Combinatory logic: internal arbitrary-proof fixed-fragment soundness

Five new modules compile individually, with 95 closed public reports:
HornProofEncoding 18, HornProofRealization 13, GuardedFiniteSupport 36,
HornInternalSoundness 11, MM0GuardedInternalReflection 17. Sources and the
five additive Dune registrations are frozen. Fresh integrated audit PASSES
all gates, exit0, 19:53:09–19:56:22 UTC. Live logs
_build/combinatory-internal-horn-audit.JMyhh0, fresh absolute build
/tmp/pts-rk-internal-horn.6x5cr6, pristine
/tmp/pts-rk-internal-horn-pristine.LZ2nx4, archive
verification/combinatory-internal-horn-2026-10-23/audit.td6KVY.
Fresh 63-module compilation passes19:53:19–19:55:55 (156s):980 own/981
aggregate closed reports,95 new. Complete recursive kernel passes
19:55:55–19:56:20 (25s); its full inventory equals fresh pristine exactly,
inherited functional_extensionality_dep only, no unsafe entries. All66
source/Dune/shared-equality/MM0 hashes are unchanged before/after, all58
previous proofs and original kernel/Agda/MM0 are preserved, and Dune is
exactly five additive registrations. Whitespace/integrity/safety gates pass.

The independent Church type quantifies one X_a:U1 per finite atom, followed
by precisely the positive clause handlers and the query proposition. It
contains no model, truth table or source-typing premise. Its rank is <=3;
the original-PTS soundness-function TYPE has rank <=4. This is a real
internal consumer of ANY native inhabitant of the proof encoding, not only
externally emitted proofs. Every source proof compiles, and each clause
accepts arbitrary encoded premise inhabitants. Exact finite indexing
preserves proof trees, models, queries and denials, including every semantic
valuation and universal Void atom. Denials are enforced by separate internal
refuters, not encoded as positive inference constructors.

The fixed guarded-MM0 positive model premise is discharged. At N>=5,D>=3
every semantic Void query has an internal refuter. External inhabitation iff
finite derivability, source-code realization and exact source/catalogue union
coverage are proved, retaining faithful decoding and consistent-model bounds.
Generic consumer typing uses no canonicity; the Void specialization and
external converse retain the previous native canonicity dependency.

First remaining goal: internally represent raw source proof/guard/decoder
provenance and fragment parameters. Fragment, query, budgets and truth table
are still metalevel parameters; this is NOT one internally budget-polymorphic
raw-source reflection theorem or independent consistency proof. Original-PTS
catalogue completeness remains separate. No code-size/runtime bound is added.
Next exact verification command:
`bash docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/AUDIT.sh`.
No previous proof, native kernel, Agda or MM0 source is edited; no staging,
commit, push, cleanup or unrelated process action. Other thread state below
is preserved. Final note build/inspection passes19:55:35–19:55:52 UTC:
31pages, appendix3,61Rocq/27Agda badges,44Agda links,129 total links.
Every page renders; changed pages1/24/25 visually reviewed. Archive
verification/combinatory-internal-horn-2026-10-23/note.nVOBmg. The first note
attempt's overwide display failure is retained; aligned layout repairs it.

## Combinatory logic: literal MM0 adequacy and guarded model existence

Eight new modules,192 public endpoints: MM0NativeSyntax42,
MM0ComputationalAdequacy37, MM0NativeReduction19, MM0CatalogueAdequacy12,
MM0CatalogueRealization7, MM0GuardedSyntaxAlgebra39, MM0GuardedReflection15,
MM0HilbertAdequacy21. All nine computational graphs and all65 catalogue
instances have exact independent source correspondence. Literal PH iff
native catalogue derivability is proved, reconstructing original closed
terms/types and typing without native source admission premises.

For EVERY N>=5,D>=3, all55 size/depth/sorting-GUARDED MM0 schemas have a
fixed finite total constructor algebra/model under EVERY valuation, with
UNGUARDED universal Void denial and nonempty universe typing. Selected
subsets also have models. Source reflection and external native canonicity
discharge consistency/model-existence premises. consistent_finite_union_exact
covers every catalogue proof by an actually accepted model at bounds
representing Void, with exact query decoding. Generated native certificate
TYPES have rank<=4; D measures Expr depth, not native type rank.

Fresh58-module compilation PASSES19:29:58–19:32:42UTC (164s), with885own,
886aggregate closed reports,192new. Full recursive kernel checking PASSES
19:32:42–19:33:06 (24s); its complete context inventory equals fresh pristine
exactly: inherited functional_extensionality_dep only, no unsafe entries.
All61 before/after hashes agree; all50 earlier proofs, original12kernel files,
shared equality, MM0 and52Agda sources are unchanged; Dune changes only
the eight additive registrations. Two earlier audit runs are retained:
first a late Hilbert source addition races the snapshot (plus a repaired
count-gate assertion fallthrough); second complete fresh compilation/kernel/
inventory/source checks pass885own/886aggregate reports but the lexical safety
scan flags a pure predicate named Admitted. It is renamed FitsSyntax without
weakening the scanner. Final attempt03 passes all proof/integrity gates,
but its no-index whitespace command returns1 for clean new-file differences
with no diagnostic. The driver is NOT all-pass. Separate final recovery
checks correct this exit-code handling and verify unchanged fresh sources.
All ten final recovery gates PASS19:35:43–19:35:44UTC, exit0, including
unchanged proof/note hashes and clean/failing whitespace/count fixtures.
Live final logs _build/combinatory-mm0-bridge-final.LNIhbh; archive
verification/combinatory-mm0-bridge-2026-10-23/final.MjHIDx.
All proof/Dune sources remain frozen.
Live logs _build/combinatory-mm0-bridge-audit.BLPblO;
build /tmp/pts-rk-mm0-bridge.IH9mrh;
pristine /tmp/pts-rk-mm0-bridge-pristine.2MonTA;
archive verification/combinatory-mm0-bridge-2026-10-23/audit.HRs4x3.

Final note build/inspection passes19:25:55–19:26:12UTC:30pages, appendix3,
56Rocq/27Agda badges,44Agda links,124links. All pages render; changed pages and
the final theorem page visually checked. Final manifest: verification/
combinatory-mm0-bridge-2026-10-23/note.rQGnBx. All failures/commands retained.

Next exact verification command:
`bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/FINAL-CHECKS.sh`.
First remaining mathematical goal: internally represent guarded source proofs
and decoder provenance and prove reflection for arbitrary represented
witnesses, not an externally indexed family of emitted certificates.
Original-PTS-to-catalogue completeness and verified external MM0 text parsing
remain separate. This does not close the other self-consistency thread's
milestone4 or prove independent internal consistency. No commits/staging/
pushes, original kernel/Agda/MM0 edits, cleanup or unrelated-process changes.
HEAD remains6a8dc984fb59a9b3743503cd405ffe59a31d1978.

## Operation provenance — fresh compilation and kernel verification complete

Milestone 4 remains open. Seven new modules are freshly compiled and
kernel-checked, with 80 public endpoints: NamedBeta (11), BooleanAgreement (8),
ContextLookupCodes (13), InternalContextLookup (15),
ContextLookupRealization (16), InternalComparisonGraph (14),
ComparisonGraphRealization (3). All 80 appear in
OperationProvenanceAudit. Proof sources are frozen. Attempt01 stopped before
compilation on eight concurrent additive combinatory module registrations;
exact normalization was reviewed, with all old proof bodies retained.
Fresh attempt02 started19:27:45 UTC. Live logs
`_build/self-consistency-operation-provenance-audit.dLxE0S`, absolute build
`/tmp/pts-rk-operation-provenance-fresh.DkOoCf`, pristine
`/tmp/pts-rk-operation-provenance-pristine.Smzrtd`.
Fresh complete-closure compilation PASSES 19:28:08–19:56:57 UTC (1729s):
80 new closed reports, 81 aggregate. The driver then exits 2 before kernel
checking: editing its reusable file during the long build disturbed Bash's
later reads (unexpected EOF). Preserve both versions and the raw failure.
The first recovery stops on five more concurrent additive registrations;
all other 524 raw hashes match. Root reviewed exact normalization of all 13
additions. Immutable continuation 02 rechecks those inputs, pins 525 current
paths, and passes corrected declaration/report gates. Full recursive kernel
checking PASSES 20:03:03–20:24:26 UTC (1283s), exit 0, on the SAME fresh build.
Its complete inventory equals pristine exactly: inherited
functional_extensionality_dep only, no unsafe entries. All 18 continuation
gates pass by 20:24:40, including exact 525-path before/after agreement,
514 preceding source/registration checks, exact normalization, original kernel, frozen
ZFC, safety and whitespace. The original invocation is NOT an all-pass audit.
The declaration gate's earlier shell failure-propagation gap is corrected
and tested: missing one Print with all 80 Checks intact fails both wrappers.
The older full audit and repository-wide CI are not rerun.
All 14 final documentation/source gates PASS, 20:26:43–20:26:50 UTC, exit 0;
live logs `_build/self-consistency-operation-provenance-final.o9Z9IF`.
The audit-final and final-checks archives preserve exact raw logs and readable
copies, including all failures and empty outputs. Final note hashes agree.

Literal context codecs are faithful and distinct from certificate-context
serialization. The independent rank-18 lookup graph performs every original
Context.index shift, including zero; its rank-19-type output-scope consumer
applies to arbitrary represented witnesses. Whole-context scoping is a
separate rank-14 guard. Executable standard witnesses, original/raw lookup
agreement and context quotation injectivity compile. Internal extraction,
arbitrary endpoint coherence and dependent typing remain open.

Comparison Trace(x,y,z,b):U6 retains the actual Zip witness z and symbolic
outputs. Formation, scoped applications and all three local Same1 agreement
cases are checked for arbitrary open inputs. Full Trace constructors and
arbitrary-Trace induction are NOT proved. Several inference/conversion
attempts timed out; the unfinished candidates are outside theories. A
symbolic named-context lookup lemma would help the present constructor
implementation; the agreement fold may instead assemble the checked local
branches directly with NamedSpine, independently of constructor lookup.
This is a proof-engineering gap, not a mathematical obstruction.

Local next proof step: lambda-abstract those local cases, convert the four motive
heads structurally, and assemble the arbitrary-Trace fold. Then connect the
remaining endpoint/source graph internally; operational sufficiency and
finite-fragment dependent soundness are still separate obligations.
The read-only plan in verification/self-consistency-operation-provenance-2026-10-23/
NEXT-PROOF.md avoids constructor lookup: use exact applied-motive branch
annotations and NamedSpine. First establish the expanded Trace telescope's
formation by four FORWARD head reductions and subject reduction, not beta
equivalence alone. Its proposed final type rank is 7, still to be checked.
The concurrent Horn checkpoint above changes the preferred soundness backend:
reuse its arbitrary-proof consumer and target an INTERNAL original-source-to-
Horn bridge. Local comparison completion is needed only if that bridge uses
the present checker route. Original-PTS coverage and represented fragment
parameters remain open; this checkpoint does not inherit a completed
raw-source soundness theorem from the independently audited Horn modules.
UNIFORM-HORN-PLAN.md in the same evidence directory records an UNCOMPILED
fixed-carrier proposal: one X:A->U1 and represented premise positions give
proof rank max(a+2,c+2,p+3). First implement exact-rank premise-position/All
formation and independent guards; native list folds have varying result
ranks and do not supply that interface. Then derive actual model handlers
and source translation, not assume them as admission fields.
Next exact verification command:
`bash docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/FINAL-CHECKS.sh`.
All worker attempts are archived there. Preserve the earlier audits below.
The final roadmap builds/validates as eight pages and six links; final pages
2--6 are byte-identical to reviewed renders, and pages 1/7/8 are visually
reviewed anew. The new note-horn-final archive retains four build attempts,
two literal-text inspection failures and the repaired orphan-page layout.
It incorporates the concurrent arbitrary-proof Horn soundness advance
without claiming a uniform internal raw-source bridge or original-PTS
catalogue completeness. Final TeX/PDF hashes begin 85749fa0/97381411.
No staging, commit, push, cleanup, original-kernel or frozen-ZFC changes.

## Combinatory logic: explicit guarded quantified fragments

Seven new modules are individually compiled and recursively kernel-checked:
GuardedFiniteCarriers (28 closed reports), GuardedHornFragments (19),
GuardedHilbertModels (27), GuardedBetaGraphs (36), GuardedHilbertTables (36),
GuardedHilbertCoverage (20), MM0GuardedQuantification (29): 195 new endpoints.
All worker inventories match pristine inherited functional_extensionality_dep
only, with no unsafe entries. Fresh 50-module compilation passes
18:28:44–18:30:57 UTC: 693 own reports, 195 new, 694 aggregate. Complete
recursive kernel checking passes18:30:57–18:31:19; the entire inventory
equals fresh pristine exactly. All53 source/Dune/shared-equality/MM0 hashes
are unchanged. Original kernel, all43 preceding combinatory sources, MM0
and all52 Agda sources remain unchanged. No new Agda/MM0/full-CI run.
Live logs _build/combinatory-guarded-fragments-audit.ACxpVa; absolute build
/tmp/pts-rk-guarded-fragments.Hzzxi9; pristine
/tmp/pts-rk-guarded-pristine.HmTbHx. The final archival whitespace gate failed
(exit2); exact raw logs are retained as gzip and readable copies normalized.
Separate FINAL-CHECKS.sh reruns the gate and verifies all proof-source hashes;
do not describe the original driver invocation as all-pass.
All nine final gates PASS at18:37:10 UTC, exit0; live logs
_build/combinatory-guarded-final.ftRIP5. No proof-source or note hash changed.

Fixed finite positional native-syntax carriers have total app/Pi/lam/subst,
numeric input/output guards and explicit overflow. The qualitative model
advances P_h to P_(h+1); the executable model instead closes the entire finite
guarded clause set. All six Hilbert rule forms and ALL finite parameter
tuples are retained subject to independent syntax/path guards. The Boolean
beta graph bounds EVERY witness state. Semantic rule correspondence,
universal Void exclusion, nonempty typing and genuine Void representation
are proved. Generated native satisfaction certificates have rank at most4;
arbitrary fragment deductions compile to actual original PTS proofs.

Executable union coverage is exact for the INDEPENDENT catalogue, including
actual finite-carrier quoted queries, monotone budget enlargement and one
common budget for a finite proof family. This does not supply original-PTS
catalogue completeness, full55 MM0/native graph adequacy or uniform internal
reflection. Native canonicity supplies external Void exclusion. The separate
literal-MM0 guarded compiler has exact all-valuation conditional checking and
source/certificate correspondence, not unconditional full55 model existence.
State/path bounds are not bounds on all host allocations or generated terms.

The first fresh49-module audit hit `No space left on device` and was stopped
(exit137). No unrelated data/processes were changed. About260MiB subsequently
became available and writes recovered. Coverage then compiled and passed full
recursive kernel verification. First note build compiled but inspection found
a literal display caused by a trailing backslash; it was repaired. All
failures and exact worker commands are in
verification/combinatory-guarded-fragments-2026-10-23. Final note build and
validation pass18:27:19–18:27:34 UTC; PDF inspection passes: 30pages,
three-page MM0 appendix, 48Rocq/27Agda badges, 116links. All pages render;
guarded-content pages22–24 visually reviewed. Final source/PDF hashes are
recorded in note-final.sha256. No verified proof sources changed afterward.

Next verification command:
`bash docs/direct-r-handoff/verification/combinatory-guarded-fragments-2026-10-23/AUDIT.sh`.
First remaining mathematical goal: bridge the literal guarded MM0 graph
theory to this native guarded presentation, and internally represent the
source/provenance and bounded soundness invariant. External finite
certificates/coverage do not complete the separate self-consistency milestone4.
No commits, staging, pushes or changes to original kernel/Agda/MM0 sources.

## Source provenance and internal residual execution

Continuation adds CheckerSourceGraph (35 public endpoints),
InternalExecutionGraph (28), CheckerGraphRealization (27), and the complete
90-endpoint SourceProvenanceAudit. Fresh compilation passes
18:09:36–18:14:39 UTC (303s): all 90 new reports closed, 91 aggregate.
Complete recursive VM-enabled kernel verification passes 18:14:39–18:22:11
UTC (452s), without dependency skips/admissions. Its entire context inventory
matches fresh pristine: inherited functional_extensionality_dep only, no
unsafe entries. The post-build raw hash gate then stops on a concurrent
registration-only change; see below. Do not label attempt02 all-pass. Live logs
`_build/self-consistency-source-provenance-audit.RB1ktf`; fresh absolute build
`/tmp/pts-rk-source-provenance-fresh.yW2QOO`; pristine
`/tmp/pts-rk-source-provenance-pristine.D4McFy`.

The native source graph independently specifies all six local rules,
step/equality fields, context lookup, context checks and raw failures.
Induction derives compiler agreement, uniqueness, complete raw coverage and
both Boolean outputs. SourcedResources adds this graph to the existing
storage contract and excludes its previous self-comparison counterexample.
No graph/resource field assumes evaluator agreement, typing or rejection.
Native substitution, lookup and decoding remain explicit external operations.

The actual original-PTS Run relation has independent leaf/conjunction
constructors and rank five. One full-type-rank-six term proves agreement for
arbitrary represented Run witnesses by exact-rank-one predicate transport,
not beta equality or unproved parametricity. Standard execution witnesses
retain symbolic comparator applications and conjunctions. The integration
supplies both-output realization, actual ordinary acceptance (including a
sort example), and conditional rejection. False execution is a theorem
premise to establish, never resource admission. No source injection is
claimed for residual programs or their execution witnesses.

First remaining goal: represent source/endpoint provenance internally and
combine it with the residual execution law. Retain context, certificate,
subject, type and expression indices. Original context lookup requires all
enclosing shifts; the existing environment lookup is not that operation.
For annotated substitution, use the single-substitution environment and prove
the coherence actually consumed; general replacement environments may be
multivalued. Product-rank maximum and complete certificate/context parsing
(including failures) remain. Standard realization and arbitrary-output scope
do not discharge these internal endpoint laws. A total compiler and the
joint Zip builder are optional routes, not mandatory prerequisites.

Milestone 4 remains open. Even internal source agreement must be followed by
operational resource sufficiency and internal dependent preservation/terminal
exclusion or an adequate negative continuation. Do not derive those from
external soundness/canonicity. DIRECT_ROADMAP now separates these boundaries
in 492 lines/eight pages; build, validation, text/link checks and visual
review of all eight pages pass. README now uses the same six milestone numbers.

Audit attempt01 stopped at the old-source hash gate, exit1,
18:05:15–18:05:22 UTC: concurrent combinatory Dune additions only. Attempt02
started 18:09:13. It pins 510 paths (506 previous plus four new), preserves
all 503 prior nonregistration bodies, and checks exact normalization of
three additive registration files. After successful compilation/kernel checks,
the source-stable gate exits1 at 18:22:18: the same combinatory Dune file gained
two more independent module registrations. All other 509 hashes agree exactly.
Read-only review confirms that removing exactly the six new module/alias
entries recovers the previous hash; all prior dependencies/registrations are
intact. A seventh registration appeared during archival and received the
same exact read-only normalization check. These concurrent guarded-model
modules remain outside this proof closure; no prior body or actual kernel
dependency is exempted. All 13 post-build recovery/final checks PASS,
18:28:16–18:28:24 UTC, exit 0. All 509 other entries agree across
before/after/current; all 503 older bodies remain frozen and all three exact
registration normalizations pass. Live final logs
`_build/self-consistency-source-provenance-final.ddsFzI`. Full-tree snapshots
are informational. The original full audit and repository CI were not rerun.
All attempts, worker failures, exact commands and note evidence are in
`verification/self-consistency-source-provenance-2026-10-23/`.

Next exact verification command after source changes:

```sh
bash docs/direct-r-handoff/verification/self-consistency-source-provenance-2026-10-23/AUDIT.sh
```

HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978. Work is uncommitted;
no staging, commit, push, cleanup or unrelated proof edits were performed.

## Joint interface, storage coverage and a precise checker blocker

Current continuation stops before milestone 4 (internal finite-fragment
soundness). Three new modules add 59 public endpoints: InternalJointTraversal
(10), CheckerResourceBounds (38), ComputationBoundary (11). Fresh compilation
passes 11:17:31–11:22:22 UTC: all 59 new reports closed (60 aggregate).
Fresh audit PASSES all 24 stages, 11:17:16–11:28:25 UTC, exit 0. Complete
recursive VM-enabled kernel verification passes 11:22:22–11:28:19 (357s),
without dependency skips/admissions. Its entire context inventory equals
fresh pristine exactly: inherited functional_extensionality_dep only,
no unsafe entries. All 500 frozen previous entries remain unchanged and
all 506 current before/after hashes agree. Original kernel, frozen ZFC,
safety and whitespace checks pass. Old full audit/repository CI not rerun.
All ten final light checks pass, 11:33:35–11:33:41 UTC. Two earlier attempts
found only trailing blank lines in archived draft displays; byte-exact
originals and failed logs are preserved. Verified proof sources are unchanged.
Live logs `_build/self-consistency-joint-resources-audit.VWulyQ`,
fresh absolute build `/tmp/pts-rk-joint-resources-fresh.TqBIPV`, pristine
`/tmp/pts-rk-joint-resources-pristine.d7jjko`.

InternalJointTraversal retains literal J:U4, constructors, projections to
C:U2, independent GoodJ: J->U6 formation, and native telescope/head-reduction
lemmas. It does NOT provide generation constructors or buildZip. Large
conversion expansion was interrupted/killed; the compiled prefix passed
11:15:28–11:15:54 UTC. Unverified candidates and root realization draft are
archived outside theories. This is a proof-engineering limitation, not a
mathematical refutation of the joint construction.

CheckerResourceBounds faithfully serializes expressions and complete operands
at EVERY synchronized comparison node. Its exact/quadratic storage bounds
and original-PTS capacity witnesses cover source, residual expressions and
all recursive traversal payloads. Complete raw-code size fragments receive
one externally computed envelope, with malformed/rejected inputs included.
No runtime, emitted-term, compiler-intermediate or internal budget-selector
theorem is claimed.

ComputationBoundary proves the proposed resource-only contract FALSE:
scoped rejected bad_application q has actual generation/capacity/traversal
witnesses, but Compare(q,q) executes to true; its proper checker executes to
false and their PTS programs are not beta-convertible. The counterexample is
a native Rocq theorem about a contract collecting actual PTS witnesses, not
an internal PTS negation of the contract or a general consistency no-go.
Independent source-to-operation local clauses are indispensable. Defining
admission by evaluator/checker agreement would assume the missing theorem.

DIRECT_ROADMAP now has 432 source lines and 7 PDF pages (previous 1390/21).
All 7 pages visually reviewed; build/validation and text/link/render inspection
pass. Exact final source/PDF hashes and four build attempts (two failures,
one intermediate success, final success) are archived in
`verification/self-consistency-joint-resources-2026-10-23/NOTE-REVIEW.md`.
The note separates the finite internal schema from arbitrary-budget
soundness, retains the six milestone numbers and parallel logical-scope audit.

First remaining mathematical goal: a source-indexed checking/compilation
relation, with independent clauses for every original source rule, context
lookup and substituted endpoints, internal agreement for BOTH outputs and
separate standard coverage. A total internal compiler is optional. The
joint Zip builder is a narrower unfinished engineering step, not this theorem.
Then prove operational resource sufficiency and an internal dependent
invariant/normalization-or-negative-continuation with terminal exclusion.
External certificate soundness/canonicity, scope alone and All supplied as
admission cannot discharge milestone 4.

Next exact verification command after source changes:

```sh
bash docs/direct-r-handoff/verification/self-consistency-joint-resources-2026-10-23/AUDIT.sh
```

HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978. Work is uncommitted;
no staging, commit, push, cleanup or unrelated proof edits were performed.

## Residual checker execution verified, 10:04 UTC

Five new proof modules plus ComparisonExecutionAudit add 92 public endpoints:
InternalCodeComparison (14), CheckerComparisons (18), InternalComparisonFolds
(24), CodeComparisonRealization (17), CheckerExecution (19). Fresh integrated
compilation and full recursive kernel verification pass; all 92 new public
assumption reports are closed (93 aggregate including imported Ranks).

The unchanged native checker compiles externally to Truth/Compare/Both,
retaining full comparison operands. Independent Zip(x,y):U4 carries only
synchronized tree traversal, not equality/output/rejection. One literal PTS
comparator of full-type rank5 consumes it and computes structural equality.
One rank3 conjunction-expression carrier and evaluator of full-type rank4
execute all residual comparisons/conjunctions. CheckerExecution proves exact
forward-reduction iff correspondence with the original general and Bottom
checkers, including malformed and scoped rejected inputs; no assumed callback,
acceptance, normalization or rejection premise remains in those interfaces.

IMPORTANT: this is not a closed C->Bool checker. Parsing, context lookup,
endpoint/substitution computation and traversal generation remain external.
Comparator correctness covers canonical raw quotations with generated Zip;
expression correctness covers generated expressions. Do not claim arbitrary
Church-inhabitant correctness. Raw serialization/quotation is still injective;
distinct_sources_same_program formally shows residual programs are not.
Traversal-node count is not an emitted-syntax or execution-cost theorem.
Uniform dictionary branch generation and internal consistency remain open.

Fresh audit passes all 23 stages, 09:56:05–10:04:43 UTC, exit0:
`verification/self-consistency-comparison-execution-2026-10-23/AUDIT.sh`.
Live logs `_build/self-consistency-comparisons-audit.ftbRbY`;
fresh build `/tmp/pts-rk-comparisons-fresh.IyPIZj`;
pristine `/tmp/pts-rk-comparisons-pristine.7FBUEo`.
Fresh compilation passes 09:56:21–10:01:22 (301s). Complete recursive
VM-enabled kernel checking passes 10:01:22–10:04:36 (194s), without skip
or module-admission flags. Entire inventory equals fresh pristine exactly:
only inherited functional_extensionality_dep, no unsafe entries. All 92
declarations are covered; all 494 frozen prior entries unchanged, all 502
current before/after hashes agree. Original kernel, frozen ZFC, safety and
tracked/untracked whitespace checks pass. Old full audit/repository CI not rerun.

Roadmap/PDF builds and inspection pass: 21 nonempty pages, seven links,
all-page rendering; pages1/9/10/20/21 visually reviewed. Subsection4.4.2
states exact computation and staging boundaries. Note build
`/tmp/pts-rk-consistency-note.k6uAuy` (final); prior build B4XQac is preserved
as intermediate evidence. Final source hash c1a0a46279efcdf8e7a567006416807b6d2cf34569ec99e20519a374d43ae30f;
PDF hash 147e7a7824a499c742d3f8aabf77a230d604b38899f34c9c1d6e3ef70cb9a01a.
Detailed worker/integration failures,
successful commands and note evidence are archived in the verification folder.
HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978; work uncommitted.
No index changes, commit, push, cleanup or unrelated proof changes this turn.

First remaining goal: independently certified internal checker-compilation
and traversal evidence, with exact source-checker correspondence and
operation-specific resource sufficiency. A total internal compiler is optional
if a relational resource package instead supplies independent witnesses with
proved standard coverage and INTERNAL agreement. Never assume that agreement
as admission. Keep both Boolean outputs.
Then derive rejecting All branches by a separate internal finite-normalization
or other soundness argument; All must not become resource admission.

Concrete next candidate (DESIGN ONLY, not a checked theorem): replace a
naive nested fold over two separate Good guards by one represented joint
traversal J. Take J = forall X:U2, (C->X)^29 -> (C->C->X)^29 ->
(X->X->X) -> X, with constructors atom-left/right-data, pair-left/atom-right,
and paired child traversals. J has calculated rank4; folding at X=C gives
projections L,R:J->C. An independent constructor guard GoodJ_4:J->U6
would support one rank7-type term forall j:J, GoodJ_4 j -> Zip(L j)(R j)
by a single fold, using existing Zip constructors. Verify these literal
types/terms in Rocq first, then prove standard all-pair coverage. This does
not yet align two separately represented inputs, certify arbitrary comparator
inhabitants, supply full checker traces, or prove rejection. Naive nested
Good_r folding lacks both sufficient motive rank and child Good_r witnesses;
merely raising its outer rank does not fix the latter. This is a restriction
of that proposed proof, not an impossibility theorem for internal generation.

Next exact verification command after proof changes:

```sh
bash docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23/AUDIT.sh
```

## Fixed internal dictionary elimination verified, 09:05 UTC

The finite-fragment continuation now has ONE original-PTS consumer for
represented finite dictionaries, rather than an externally varying case
telescope. Three new modules plus FiniteDictionaryAudit add 56 endpoints:
InternalFiniteDictionaries (20), FiniteDictionaryRealization (24), and
DictionaryRejection (12). Existing proof sources are preserved; only Dune
and Audit.v registration change among the previous proof infrastructure.

For E:U1, List/Guard have rank3, All/Fill rank4, and the complete polymorphic
eliminator/consumer type rank5. The Church fold constructs the type telescope
internally using U3:U0. Only its final result is padded by D=(Top->Top):U2;
this keeps every accumulator at exact rank3 without cumulativity. Nil/cons/
append and separate All/Fill/Guard constructors are checked. Standard
list/evidence quotation is executable, the telescope beta equation is exact,
and list quotation is syntax-injective. Old source selectors retain their
stronger beta-injectivity. DictionaryRejection instantiates one consumer for
every complete-code bound and proves rejection for arbitrary admitted inputs,
with independent canonical coverage for every raw code at its own size.

IMPORTANT: uniform elimination is NOT uniform native-checker branch generation.
The list, actual checker table and All package are still generated externally
from b. The old branch proof uses external native normalization/canonicity
to justify conversion. A symbolic checker call does not beta-reduce to false;
folding identities cannot manufacture its All evidence. Never place that
evidence in resource admission or claim the final consistency theorem. Current
E:U1 fits selector domains, not the raw-tree carrier C:U2; exact-rank adaptation
is separate and is not a proved impossibility.

Fresh integrated audit PASSES all 22 stages, 09:04:26–09:05:22 UTC:
56 new closed reports (160 aggregate), full recursive checking of the complete
new closure, and exact complete pristine-inventory equality. Only inherited
functional_extensionality_dep; no unsafe entries. All previous proof-source
hashes, original kernel and frozen ZFC checks pass. Full older 495-report audit
and repository CI were not rerun. Incremental failures and exact commands
are preserved, not relabelled successful.

Roadmap source/PDF build passes: 20 pages, seven links, all-page rendering;
pages1/7/8/9/19/20 visually reviewed. Section4.4.1 states the checked interface
and the remaining generation boundary. Logs and exact commands:
`verification/self-consistency-finite-dictionaries-2026-10-23/COMMANDS.md`.
Live logs `_build/self-consistency-dictionaries-audit.PkYzEJ`;
fresh build `/tmp/pts-rk-dictionaries-fresh.KOCLBv`;
note build `/tmp/pts-rk-consistency-note.QJT5ss`.
HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978; work uncommitted.
No staging, commit, push, cleanup or unrelated source edit.

First remaining goal: construct checker-specific All evidence internally
from independent computation/finite-normalization certificates, with exact
correspondence to the unchanged checker. Also represent dictionary/budget
generation and prove sufficient-resource coverage/costs. A full dependent
typing reconstruction remains optional; All must be a derived conclusion.
A narrow next subgoal is output-neutral checker-trace reflection: independently
defined CheckRun(resource,input,trace,boolean) should imply agreement with the
represented checker for EITHER Boolean output. This is not rejection; a separate
finite normalization/model-preservation and terminal-exclusion argument must
exclude true. Never hide "every run returns false" in trace/resource validity.
Next exact verification command after proof changes:

```sh
bash docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/AUDIT.sh
```

## Finite-fragment internal rejection schema verified, 08:24 UTC

The user's selected route is implemented in six new proof modules plus
FiniteFragmentAudit (95 new public endpoints). FiniteCodeFragments enumerates
ALL complete raw codes by size, including malformed/rejected data, with exact
finite indexing/roundtrip. FiniteFragmentNormalization uses the improved
combinatory normalization and canonicity: accepted certificates share one
computed finite carrier at each source-family bound; every beta state and
the exact final native type are covered. Raw conversion intermediates are
not assumed typed or normalizing. The original checker is unchanged.

FiniteCaseGuards supplies independent arbitrary-arity internal case guards.
FiniteFragmentTables compiles actual checker values, with exact general
Boolean and judgment-checker correspondence. FiniteFragmentRejection proves
rejection_typed b and rejection_type_sorted b: for EVERY EXTERNAL bound b,
an actual original-PTS rejection term handles every guarded selector input,
with type rank FOUR. Standard coverage includes every raw code at its full
serialized size; FiniteSelectorSeparation retains beta-level injection.
No rejection/normalization/typing conclusion is hidden in admission.

IMPORTANT: rank uniformity is not interface uniformity. The arity, carrier,
case telescope, table and generated proof still depend externally on b.
There is no one internal all-budget consistency theorem and no proved
operation-cost bound for enumeration/generation. Full dependent history
reconstruction is now an optional alternative, not a gate to this completed
finite schema. The improved native finite-model no-go is respected: these
are genuinely growing guarded fragments, not one ungraded finite model.

Fresh integrated audit PASSES all 21 stages, 08:23:08–08:24:10 UTC:
95 new closed endpoint reports (199 aggregate), complete recursive checking
of the full new dependency closure, and exact complete pristine inventory
equality. Only inherited functional_extensionality_dep; no unsafe entries.
Original/common/previous consistency/combinatory proofs and frozen ZFC are
unchanged; before/after manifests match. Old full 495-report audit and full
repository CI are not rerun. First fresh run's pre-existing whitespace failure
is preserved; no previous proof was changed to fix it.

Note/PDF build and inspection pass: 19 pages, seven links, all-page rendering;
changed pages 1/7/8/18/19 visually reviewed. The roadmap's section 4.4 explains
the schema, its actual ranks and remaining uniformity obligation; the stale
all-true-model discussion now reflects the stronger combinatory results.

Logs: `_build/self-consistency-fragments-audit.qOXzIr`.
Fresh build: `/tmp/pts-rk-fragments-fresh.d7RHpo`.
Exact commands, failures, source hashes and evidence:
`verification/self-consistency-finite-fragments-2026-10-23/COMMANDS.md`.
HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978; all new work uncommitted.
No staging, commit, push, cleanup or unrelated proof edit.

First remaining construction: encode finite dictionaries and case evidence
at one fixed resource-relative interface, with internal elimination and
independent standard admission; prove generator/operation costs as needed.
Do not infer this from the external family or place its rejection in a guard.
Next exact verification command after proof changes:

```sh
bash docs/direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23/AUDIT.sh
```

## Quantified finite-model milestone verified; native boundary proved, 07:45 UTC

Eleven new combinatory modules give complete total-constructor search on
fixed finite domains, literal sorted MM0 schemas for all 55 axioms, exact
universal semantic grounding and independent source-deduction translation
into actual original PTS proofs. All constructor argument tuples and all
axiom valuations are covered. Candidate certificate inhabitability exactly
matches model existence for the supplied constructor algebra; certificates
have rank at most four. Successful search supplies both constructor/model
and native certificate. The explicit two-element subtheory has acceptance
discharged analytically, not as an input premise.

IMPORTANT: that subtheory omits sveq and f0. Substitution is identity and
form/ax are empty, disabling the entire positive catalogue. Both omissions
are explicitly refuted by the model; do not describe it as nearly full PTS.
The full55 singleton candidate is computed false. Search at every fixed
equicardinal domain is complete, but no full55 finite model or all-cardinality
nonexistence is established. Two-element existence does not execute 2^28
constructor tables. The textual MM0/AST crosscheck matches every expanded
axiom but remains an untrusted parser test, not native adequacy.

FiniteNativeModelBoundary proves the stronger requested full native interface
IMPOSSIBLE on one ungraded finite term carrier, even with directed reduction:
total compositional application + all native typing/beta soundness + semantic
conversion/type reduction + empty Void imply injectivity of every Church
selector family. A separate finite-test theorem proves the corresponding
cardinality lower bound without the global native-soundness premise.
This does not rule out genuine size guards, growing grades, or weaker selected
schemas. It does not transfer automatically to literal MM0 without adequacy.

Fresh integrated audit PASS, **07:43:26–07:45:14 UTC**, all 22 stages exit 0.
43 modules; **498 own closed reports, 140 new**, plus one imported Ranks report.
Complete recursive checking and full pristine inventory comparison pass:
only inherited functional_extensionality_dep; no unsafe entries. Original
kernel and all 32 previous combinatory sources/shared equality/MM0/52 Agda
sources are unchanged; all before/after current hashes agree. No new
Agda/MM0 checker/full repository CI run. All isolated failures/interruptions
are preserved; the final fresh run succeeds as one unit.

Final note/PDF build and inspection PASS, 07:41:38–07:41:53 UTC:
28 pages, three-page MM0 appendix, 41 Rocq / 27 Agda badges, 109 links.
All pages rendered; changed pages 1,18,20–22 visually reviewed.
Exact commands, statuses, hashes and evidence:
`verification/combinatory-quantified-models-2026-10-23/COMMANDS.md`.
Live logs: `_build/combinatory-quantified-models-audit.fUUdPV`;
fresh build: `/tmp/pts-rk-quantified-models.uhpkYv`.

First remaining decision: specify a genuinely size-/proof-depth-guarded
fragment and prove its exact bounded-source coverage, rather than silently
weakening full quantified axioms. Alternatively establish the missing native/
MM0 adequacy and transfer the obstruction. Finite proof translation is NOT
one uniform internal theorem over arbitrary Church-coded proofs/budgets.
No target switch or such uniform reflection theorem was made this turn.

HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978. Eleven new sources,
Dune registration, note/PDF and documentation are uncommitted; all pre-existing
dirty work preserved. No index action, commit, push or cleanup. Next exact
proof-change verification command:

```sh
bash docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/AUDIT.sh
```

## Combinatory Void-denying models verified, 06:51 UTC

The grounded-Horn loophole is repaired by actual negative constraints,
not a positive false atom. Eight new Rocq modules prove original native
Void canonicity, independent exact Hilbert-catalogue grounding and consistent
model existence without a target-consistency premise. Every such model
rejects all closed Void judgments. Finite ground fragments have executable
exact least models, native soundness and finite signed propositional
completion. The latter adds negative facts and is not the uncompleted theory.
Original-PTS Church table terms have proved typing and true/false beta
correspondence for these externally tabulated queries.

FiniteUniversalHorn proves complete grounding over ALL semantic valuations
of a supplied finite constructor interpretation and exact executable
candidate-model checking. It does not establish candidate existence or
schema adequacy for every quantified PTS fragment. FiniteModelBoundary
proves only the total UNTYPED equational K collapse; typed/graded, guarded
and directed-reduction candidates remain possible. Do not confuse the
singleton ground-predicate model with a finite quotient of PTS syntax.

Focused one-shot audit PASSES all 19 stages, 06:50:50–06:51:47 UTC, exit 0:
fresh 32-module build, 358 own closed reports (117 new; 359 with Ranks),
full recursive check and exact complete pristine inventory comparison.
Only inherited functional_extensionality_dep; no unsafe entries. All original
kernel files and all 52 previous Agda sources are unchanged. The source
manifest is stable before/after checking. No new Agda/MM0/full-CI run.
The two earlier failed audits are preserved, not relabelled successful.

Final note/PDF build and inspection PASS, 06:48:39–06:48:53 UTC:
27 pages, three-page MM0 appendix, 30 Rocq / 27 Agda badges, 98 links.
Changed pages visually reviewed. Exact commands, failures, source hashes,
inventories and logs:
`verification/combinatory-consistent-horn-2026-10-23/COMMANDS.md`.
Live final logs: `_build/combinatory-consistent-horn-audit.QbsFPC`;
fresh build: `/tmp/pts-rk-consistent-horn.2l5WGN`.

First remaining goal: construct an accepted finite constructor interpretation
for a precisely specified quantified typed/resource PTS fragment; prove its
schema agreement and coverage, then internalize soundness. External Church
lookup compilation is not internal uniform saturation/reflection. The
catalogue completeness/MM0/QIIRT bridges remain independent open obligations.

HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978. The eight modules,
registration, note and documentation are uncommitted. Existing dirty work
and simultaneous unrelated handoff additions are preserved; this work made
no index changes, commit or push. Next exact focused verification command:

```sh
bash docs/direct-r-handoff/verification/combinatory-consistent-horn-2026-10-23/AUDIT.sh
```

## Finite-fragment/draft comparison — analysis only, 06:27 UTC

The user's challenge corrects the scope of the preceding stopping gate.
Failure of the selected homogeneous original-typing invariant does NOT block
every bounded-consistency route. For an externally fixed finite domain of
COMPLETE certificates, checker tabulation plus independent finite-case guards
can yield internal rejection by exhaustive cases. FiniteRejection.rejection_typed
already implements a two-code pilot. General all-index guard/rejection generation
and its exact checker interface are still unformalized. This proposed family
is not one internal theorem over arbitrary represented budgets.

Read the original Zermelo draft consistency section and the actual combinatory
note/modules. The latter establish bounded execution carriers, graded native
soundness and actual fixed-table PTS programs; NOT fixed finite first-order
models or an internal uniform reflection theorem. Program ranks 1/2 are fixed,
but E_K interfaces, table size and unrolled iteration depend on external
alphabet/size/pass bounds. Subject size alone does not bound full certificates.

The draft offers a genuine weaker construction: its scoped graded analysis
calculus G drops type-formation/context-validity reconstruction, retains grades
and uses tagged-product projections plus elementary constant separation.
Only active evaluation and negative grade-zero terminal exclusion are needed.
No concrete mathematical flaw was identified in this review, but its source
packet, separation and polynomial-transport claims remain unformalized.
EA bounded induction and Pakhomov transfer supply the uniform logical step;
an EA/H-free route must replace that apparatus, not merely compile the reducer.

Important target difference: the draft fixes explicit typed-equality T^e;
NativeProofCodes uses arbitrary raw conversion. External equivalence does not
identify internal consistency formulas. No checker or target was changed.
Do not treat an internal conversion between these predicates as mandatory if
the user instead selects the draft's exact target. Design analysis and source
labels are recorded in DECISIONS below the corresponding date heading.

No proof/paper/PDF edits or new builds in this analysis turn; the preceding
495-report/full-recursive verification remains the last proof checkpoint.
Only STATE/DECISIONS were updated under the standing continuity instruction.
No staging/commit/push. Next inspect the smaller invariant before extending
the stronger route:

```sh
sed -n '1835,1925p' /Users/akuklev/Downloads/Logical_and_computational_strength_of_PTS_rk_Zermelo_revision.tex
sed -n '2219,2470p' /Users/akuklev/Downloads/Logical_and_computational_strength_of_PTS_rk_Zermelo_revision.tex
```

## Replacement milestone verified; dependent-coherence gate open, 06:14 UTC

Milestone 1 is complete. All six new modules pass isolated compilation and
all 69 new public reports are closed. The integrated snapshot-2 build now
also PASSES, **04:49:40–05:43:05 UTC**, 3205 seconds, exit 0, with exactly
**495 fresh closed reports** and no reported axioms. Before/build source
manifests are identical. Logs and exact staged commands:
`_build/self-consistency-replacement-progress.aS3W5y`.

The complete coherent isolated recursive check PASSES,
**05:29:20–06:11:50 UTC**, 2550 seconds, exit 0. Both new roots and their
entire dependency closure were checked with `-bytecode-compiler yes`, without
admit/skip flags. Complete inventory equals fresh pristine exactly: inherited
`functional_extensionality_dep` only, no unsafe entries. All mapped source
copies and before/after manifests match. Evidence:
`/tmp/pts-rk-replacement-realization.Fcusuc/kernel.*`, inventory-comparison
and kernel-source-stability logs/exits.

All 15 independent alternate-closure final stages pass at **06:13:32 UTC**:
495 fresh reports, both snapshot comparisons, inventory equality, original
kernel/frozen ZFC equality, all 74 previous-source entries and final 82-entry
manifest stability. The redundant fresh checker was then deliberately
terminated, **actual exit 143 at 06:14:19 UTC**; its staged record is not a
pass. Snapshot 1 remains superseded, exit 130. The focused verification is
complete through the explicitly recorded successful staged/isolated route;
the reusable one-shot script is syntax-checked, not claimed as a successful
one-shot run. Full repository CI was not rerun.

First remaining mathematical target: internal dependent coherence under
annotated substitution and arbitrary supplied conversion. The whole-history
motive is rank-feasible. A source-node closure/stack machine may avoid
reconstructing typing proofs, but first needs product-conversion injectivity
and conversion transport under represented environments: align the exposed
lambda's body context/type with the application's substituted codomain.
Native `DefEq.equiv_Π_inversion` and `replace_equiv` specify these laws but
do not supply internal PTS terms. Goals 2–4 remain open; the specific
same-index and conversion-intermediate obstructions are not a general no-go.

The requested weak-finite-satisfiability/Willard preparation is in the paper
and DECISIONS. Final roadmap build **04** passes in
`/tmp/pts-rk-consistency-note.kNYiVl`; PDF inspection passes: **18 nonempty
pages, 7 links**, required text/math and all-page rendering. Pages 14, 16–18
were visually reviewed. Source/PDF hashes are `final-note.sha256` in the
progress directory. No proof changes after the snapshot freeze, no staging,
commit, push or cleanup. HEAD remains
`6a8dc984fb59a9b3743503cd405ffe59a31d1978`; pre-existing dirty work is preserved.
Six new proof modules and their registration/documentation changes remain
uncommitted. Next exact inspection command for the remaining coherence target:

```sh
rg -n 'equiv_Π_inversion|replace_equiv|ConversionRule' theories/DefEq.v theories/self_consistency/NativeProofCodes.v theories/self_consistency/CertificateAdequacy.v
```

After meaningful proof changes, use the pinned environment and the focused
driver `bash docs/direct-r-handoff/verification/self-consistency-replacement-2026-10-23/AUDIT.sh`.
Its future wholly fresh build/check allowances are 7200/3600 seconds. Do not
weaken the independent checker, normalize all raw conversion intermediates,
or retain a semantic-validity/target-soundness assumption in the resource guard.

## Milestone1 complete; final audit running,05:29UTC

ReplacementRealization isolated attempt02 PASSES05:10:04–05:28:10UTC,
1086s,exit0;11freshclosed assumption reports,exit0. Logs/objects:
/tmp/pts-rk-replacement-realization.Fcusuc. All69newpublic endpoints now
compile with closed reports. Milestone1 fixed-environment annotated replacement
and exact standard/raw/decoded substitution with internal output-scope witness
is complete. No dependent soundness or consistency conclusion follows.

Complete recursive VM-enabled check started05:29:20UTC,session1929, over
the coherent isolated closure (both ReplacementRealization/InvariantObstructions
roots, noadmit/norec,timeout3600). Preflight compares every old/newsourcecopy
to currentrepo; its beforemanifest equals frozen snapshot2 byte-for-byte.
Willard owns the process/pristineinventory/sourcecomparison. FreshDune in
snapshot2 is compiling ReplacementRealization after all dependencies passed;
term_lookup owns495freshreports and finalsource/inventory checks. See staged
and alternative-continuation scripts/status in progress.aS3W5y. Do not claim
these ongoing stages passed yet; snapshot1 remains cancelled130.

First remaining mathematical gate: independently guarded hereditary
application/beta-splicing/query composition with standard coverage. The
whole-history motive avoids the bare rank cycle; low typing observations
still require low-graph inversion/substitution. Goals2–4 are open, not ruled
out. README/paper now identify milestone1 as completed. FinalPDF rebuild
and finalstatus/evidence updates remain; no commit/push authorized.

## Replacement template integration — in progress, snapshot 2

The original inlined InternalReplacement isolated run ended at04:45:23UTC,
exit124 (2400s timeout). Binder check and Qed passed807.268/836.205s;
timeout occurred during application checking, not a reported proof error.
The first fresh audit was deliberately interrupted BEFORE source edits:
fresh-build exit130 at04:45:34UTC, preserved in audit.vyvjwb/status.tsv.
Neither run is a pass. Its fresh Audit.vo had not been produced.

Native NamedTemplates.v now proves assembler/substitution/closed-fragment
congruence,16 public endpoints, isolated compilation exit0 in
/tmp/pts-rk-named-templates.c4yc2f. Generic binder/app checks and exact literal
PUBLIC TYPE specialization pass in temporary probes. New public constructor
terms apply those templates to actual term_at; graph clauses/public types
are unchanged. No target premise is retained. Helpers are local; public
count is now69new/495total across six new modules. Shared common/original
sources remain unchanged. This optimization is not a change of PTS rules.

The exact frozen scope probe passes337.774s checking+320.2sQed, then original
closed application, both assumptions reports closed. Logs:
/tmp/pts-rk-replacement-template.BtTZx5/scope-01.*.
Optimized full InternalReplacement compilation PASSES04:47:42–05:09:34UTC,
1312s,exit0 in /tmp/pts-rk-replacement-optimized.tifSP4. Separate assumptions
compilation passes,exit0,12closed reports. NamedTemplates also has16fresh
closed reports,exit0. All public types/graph clauses unchanged;26declarations
were compared literally against the first isolated copy and match.
Agent term_lookup owns staged fresh audit snapshot2, started04:49:40UTC,
session44302 in the SAME fresh /tmp/pts-rk-replacement-fresh.87Hwa9; it reuses
unchanged completed dependencies, not old public reports (Audit.vo absent
checked). Logs/scripts/status are in progress.aS3W5y. Initial snapshot,
safety, registrations and74prior-source checks pass; Dune3600 is running.
CompleteclosureVMcheck3600 follows. Agent willard reviewed integration with
no capture/interface issue and will compile ReplacementRealization against
the coherent isolated closure once InternalReplacement.vo exists. No source
changes after this freeze without explicitly superseding the snapshot.
Realization attempt01 exited127 because launcher omitted opam exec (no Rocq
process ran). Corrected attempt02 started05:10:04UTC in
/tmp/pts-rk-replacement-realization.Fcusuc,1800s. Willard then runs complete
recursive VM-enabled closure checking over this coherent isolated closure,
overlapping freshDune. If it passes, term_lookup will explicitly supersede
the duplicate fresh-kernel stage and run the separately recorded tail checks;
no cancelled stage will be relabelled passed. Fresh495reports still required.

README/roadmap describe implemented replacement with verification explicitly
pending. Goals2–4 remain open. A reviewed single WHOLE-HISTORY motive has
rankmax(3,historyRank+1,observationRank), so avoids the bare iteration cycle.
The concrete gate is independently guarded hereditary application/beta-splicing:
low typing demands low-graph inversion/substitution; scope is insufficient;
self-semantic environment guards risk recreating the cycle. Paper/DECISIONS
record this candidate and limits, NOT a general impossibility theorem. The Willard
preparation and earlier PDF build pass remain as recorded below. Rebuild PDF
after final verification/status edits. No staging,commit,push or cleanup.

## Replacement and invariant audit — in progress, 04:14 UTC

Active request: finish milestones 1–4 unless a concrete blocker; prepare goal5
by discussing weak local finite satisfiability and Willard in paper/internal
notes. Five new modules are registered (53 endpoints;479 total):
InternalTermLookup, TermLookupRealization, InternalReplacement,
ReplacementRealization, InvariantObstructions. All earlier38 proof modules
and original/common sources remain unchanged; only Audit/dune registrations
extend them. Old76 hashes passed before registration; afterward old74 excluding
Audit/dune pass. ZFC frozen comparison/index checks pass. No commit/push/cleanup.

InternalTermLookup isolated attempt01 passes, exit0,9closed reports, exact
relation18/bound19. Logs /tmp/pts-rk-term-lookup.LNt7Ed. TermLookupRealization
attempt01 passes04:05:49–04:10:37UTC,288s,exit0,7closedreports, logs
/tmp/pts-rk-term-lookup-realization.Q89Jed. InvariantObstructions attempt02,
14closedreports and recursive VM-enabled dependency check pass, exit0, logs
/tmp/pts-rk-invariant-obstructions.62zYsp. New InternalReplacement isolated
attempt01 is RUNNING since04:05:23,timeout2400, logs
/tmp/pts-rk-replacement.4FJeXN. ReplacementRealization is written/reviewed but
has NOT yet compiled. Do not claim goal1 complete until both pass.

New fresh one-shot audit started04:14:23UTC, shellsession18776:
bash docs/direct-r-handoff/verification/self-consistency-replacement-2026-10-23/AUDIT.sh
Fresh /tmp/pts-rk-replacement-fresh.87Hwa9; pristine
/tmp/pts-rk-replacement-pristine.k3FQjN; logs
_build/self-consistency-replacement-audit.vyvjwb. Limits3600freshbuild/3600kernel;
complete newclosure rootsReplacementRealization/InvariantObstructions,
supportedVMflag, noadmit/norec. Initial metadata/safety/registration stages
pass. Audit still RUNNING, not a pass. Sources frozen at launch; if a compiler
error requires edits, preserve this run's failure and record the changed source.
Progress/source manifest: _build/self-consistency-replacement-progress.aS3W5y.

Concrete goal2 restrictions now proved: implication has unique rankmax(r+1,s),
callbackE->P fitsP's rankr iff rankE<r, so a same-index graph-premise fold
cannot be repaired by raising the common index. A valid conversion certificate
forU1:U0 includes an untypable beta-self-loop intermediate; requiring all its
nodes strongly normalizing is false. These refute specific proof patterns,
not all interpretations. A low-target/high-source one-step theorem remains
possible, but needs a separately constructed history-stable invariant to
iterate. A fuelled homogeneous machine is also not supplied by the current
native normalization/finite-table APIs. Goals2–4 remain open.

Willard primary references1108.6330v8(Def5.10/Thm5.11) and1307.0150v2(Thm4.1)
are checked; DECISIONS and DIRECT_ROADMAP.tex now record the requested promising
direction and precise limits. All-true Horn singleton models do not separate
the contradiction atom; self-justifying extensions are not proofs in unchanged
PTS-rk. Roadmap build01 passes in /tmp/pts-rk-consistency-note.HjyM9x;
PDF inspector passes17nonempty pages/7links/all-page renders, changedpages13/15/16
visually reviewed. Logs note-build-01/pdf-inspection-01 in progressdirectory.
Substitution status prose still awaits final verification/update/rebuild.

Performance diagnostic at04:30UTC: inlined replacement binder tactic passed
in807s, Qed replay stillrunning; this is not yet completed modulecompilation.
A TEMPORARY generic-lookup template check passed in88.9s plus86.4sQed, but
naive eager specialization explodedmemory and that temp attempt was deliberately
cancelled(exit143), not a proof failure. Agents are testing lazy/structural
specialization in /tmp/pts-rk-replacement-template.BtTZx5; nothing adopted in
frozen repo sources yet. If adopting it, explicitly supersede this audit
snapshot; do not claim its old before/after manifests match changed sources.

Next: inspect current isolated/audit logs, compile ReplacementRealization once
InternalReplacement.vo exists, fix first compiler error if any; then finish
fresh reports/kernel inventory, update paper/README/evidence and rebuild PDF.

## Standard shift realization and substitution environments — checked

Four new modules: RenamingLookupRealization, RenamingRealization,
InternalSubstitutionEnvironment, SubstitutionEnvironmentRealization. They add
41 public Lemma/Theorem reports (426 total). Independent source review finds
no binder/annotation/rank or target-integrity issue. The generic renaming
generator assumes pointwise RenAt witnesses; its standard shift specialization
constructs them. Exact decoded/raw endpoints and application of the actual
internal renaming_scope term are included. The single-substitution environment
has rank13 and no output-scope premise in its clauses; its separate bound has
rank14. This is not yet binder-lifted term lookup or full internal substitution.

InternalSubstitutionEnvironment isolated attempt01 PASSES, exit0, in
/tmp/pts-rk-substitution-environment.1e757d. Lookup/environment-realization
compiled copies match final sources; their original shell exit statuses were
not recovered after user resume. The isolated RenamingRealization attempt01
was interrupted before binder-helper Qed and has no .vo: NOT a successful run.
Fresh Dune integration PASSES in /tmp/pts-rk-renaming-fresh.T1RZXE;
logs _build/self-consistency-renaming-progress.R8eFUQ/complete-build.log,
03:09:08–03:22:09 UTC, 781 seconds, exit0, all 426/426 reports closed.
Initial fresh-base wrapper was interrupted with no exit file; completion is
established by this separate successful command:
opam exec -- timeout 1200 dune build --build-dir /tmp/pts-rk-renaming-fresh.T1RZXE --display=short --no-buffer -j 2 @theories/self_consistency/audit

The PREVIOUS seven-module dependency closure now passes full recursive checking
with Rocq's supported -bytecode-compiler yes, no -admit/-norec: exit0,
02:06:14–02:16:57 UTC including pristine check; exact pristine inventory
(functional_extensionality_dep only, no unsafe entries). Logs:
_build/self-consistency-renaming-vm.gH0ToE. This uses the standard VM conversion
backend, including serialized bytecode; it does not erase the earlier
VM-disabled timeout or claim that that conversion path completed. Current
four-module recursive verification PASSES 03:22:22–03:36:57 UTC, 875 seconds,
exit0 within timeout1800, same VM flag. Roots RenamingRealization and
SubstitutionEnvironmentRealization and their COMPLETE dependency closure:
exact pristine inventory equality, inherited functional_extensionality_dep
only, no unsafe entries. Logs kernel.log, kernel-exit.txt/kernel-end.txt,
current-inventory.txt in the progress directory. Before/after frozen-source
checks both pass (76 entries); all 34 earlier proof sources and original/common
files remain unchanged, except the intentionally extended Audit/dune registration.
The frozen PR#1 ZFC model also matches. Note/PDF build 02 passes in
/tmp/pts-rk-consistency-note.SzSwbM, with clean diagnostics; inspector verifies
15 nonempty pages, four links, required math/text and all-page renders.
Changed pages 12/13/15 visually reviewed. Final source/TeX/PDF hashes:
_build/self-consistency-renaming-progress.R8eFUQ/final-sha256.log.

First mathematical goal after the shift bridge: fixed term-valued lookup with
independent weakening steps, then constructor-directed replacement and exact
Syntax.subst realization. Dependent typing/conversion, resource sufficiency,
raw admission, terminal separation and all-budget soundness remain open.
Audit the precise relational statement/derivability conditions alongside those
steps. No commit, push, staging or cleanup. Existing work remains intact.
HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978; index empty.
The next implementation is the independently defined binder-indexed term lookup
outlined in DECISIONS, not an assumed replacement theorem. After that change,
the exact fresh audit command is:
bash docs/direct-r-handoff/verification/self-consistency-renaming-2026-10-23/AUDIT.sh
That one-shot script is syntax-checked but was not run as one unit at this
checkpoint; the staged commands/results above are the actual evidence.

## Annotated substitution and fixed-environment renaming — built; recheck timed out

New CodeSubstitution, InternalBinary/BinaryRealization, InternalScope/
ScopeRealization and InternalRenamingLookup compile in the pinned environment.
Native raw replacement has exact annotated Syntax.replace/subst agreement,
independent relational agreement, scope preservation and scoped totality.
Internal binary carry and scope relations have actual original-PTS constructors
and executable standard witnesses, including every untyped original term.
Binder-indexed renaming lookup retains one F:C²->U12 under binders and proves
every output Index at fixed rank. Independent source-bounded shift supplies
the required FBound instance. No global functionality or inversion used.

InternalRenaming.v PASSES isolated compilation, attempt 05 exit 0:
00:44:53–00:58:24 UTC (811 seconds, filesystem timestamps). All 11 endpoints
compile: independent source-directed graph U16, exact output Scope motive12,
and actual preservation term with type U17. Final proof alone took about
182 seconds. Only evaluation fuel changed after earlier Undecided results:
binder/app 65536, final formation 16384, final fold 262144. An earlier restart
had inconsistent isolated dependency checksums; coherent default closure fixes
that. Attempt 04 was deliberately cancelled early (exit143), not a proof
failure or timeout. No checker/CI or mathematical contract changed. Fresh
dependencies pass at 01:05:26 UTC (1156 seconds); all 385/385 public reports
are closed at 01:06:20. Independent recursive checking exits 124 at 01:46:20
after its 2400-second limit, without reporting a proof error. It did not finish
or produce a complete inventory; this is NOT a passing complete audit.
Root progress logs:
_build/self-consistency-substitution-progress; isolated renaming logs:
/tmp/pts-rk-internal-renaming.LM9OJj.

Important boundary: RenAt does not assert target=base+depth; its checked
contract is boundedness, not an exact lifted-environment decoder. Native
substitution correctness and internal scope coverage do not themselves
realize the internal renaming graph. First subsequent goal: exact forward
realization of bounded-shift renaming on every original t -> shift t; then
fixed-base term-valued lookup and single substitution, followed by dependent
typing/conversion preservation. Resource sufficiency and consistency open.

Original/common sources and all 27 prior proof modules match the preceding
fully checked source manifest; Audit.v/dune register all 385 endpoints. Manual
post-timeout checks pass: fresh-audit before/after manifest equality, all eleven
frozen source/note/PDF hashes, prior original/common/proof hashes, and original
kernel comparison with pristine. Logs in the progress directory:
sources-after-timeout.log, final-hashes-checked.log, prior-unchanged-final.log,
original-unchanged-final.log. HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978;
index empty. No staging, commit/push or cleanup. Fresh audit started 00:46:00
UTC against the unchanged snapshot; all public reports pass. Its recursive
check ran 01:06:20–01:46:20 and
covers the complete NEW dependency closure only; unchanged older optional
modules retain the preceding full kernel audit below. Logs:
_build/self-consistency-substitution-audit.FlM4MI; fresh
/tmp/pts-rk-substitution-fresh.NONg0M; pristine
/tmp/pts-rk-substitution-pristine.qcNAzd. Reproducible audit command:
bash docs/direct-r-handoff/verification/self-consistency-substitution-2026-10-23/AUDIT.sh

First verification goal: finish the independent new-closure check and compare
its completed context inventory with pristine. COMMANDS.md in that directory
records the exact proposed 7200-second retry against the frozen fresh objects;
it has NOT been run. No CI check or timeout was changed to obtain success.
First mathematical goal remains exact forward bounded-shift realization above.
Roadmap/PDF build 02 passes with clean diagnostics; inspector checks all 15
nonempty pages, four links and required text/math; changed pages 11–15 reviewed.

## Consumer-directed preservation; mandatory obligations reviewed — checked

Four new modules, 488 lines: RelationalTransport, LookupHomomorphisms,
OccurrenceSafety, SimulationRealization. All 23 previous proof modules,
original kernel, C/Good/Look interfaces and common infrastructure match
their initial hashes. No existing rules, guards or proof definitions changed.

Original PTS terms prove rank-4 consumer descent and negative safety for
lookup/history; concrete Ext-absence propagates by transitivity, with actual
nonzero-leaf/pair absence from stop proved using independent observations
and exact padding. No external Bottom emptiness. Shape and generated filling
preserve Look_5/Look_6/Hist at the same motive ranks and with unchanged paths.
Standard realizations APPLY those maps to earlier lookup witnesses and
convert endpoints by proved beta laws. Filling is forward-only, with a
native non-reflection counterexample. These are not dependent substitution
or source typing/normalization soundness.

Review: full arbitrary-path functionality and matching-constructor inversion
have no implemented consumers; optional lemmas, no longer mandatory next
gates. For each actual consumer, prove every-output invariant preservation
and thread the same result, or prove the needed coherence. Structural
closure may replace internal numerical comparison. Preserving an independent
invariant may avoid complete typing-certificate reconstruction. Neither
option weakens independent acceptance, standard raw admission or actual
operation/resource sufficiency. Source terminal separation remains necessary.

Fresh audit started 23:29:14 UTC (22 October; 23 October local). Pristine
build/kernel pass. Fresh dependencies pass 23:33:26 (242 seconds); separate
reports 23:33:33, 283/283 closed (41 new). Recursive kernel checking passes
23:33:33–00:03:42 UTC (22–23 October), 1809 seconds within the up-front
2400-second limit. Complete inventory equals pristine exactly: unchanged
functional_extensionality_dep only, no unsafe entries. Inventory comparison,
original-source comparison and before/after source stability all pass at
00:03:42; EVERY audit stage exits 0, no timeout. Logs:
_build/self-consistency-relational-audit.ILJDGV; fresh
/tmp/pts-rk-relational-fresh.ZbkLf6; pristine
/tmp/pts-rk-relational-pristine.yosufK. Exact failures/contracts:
verification/self-consistency-relational-2026-10-23/COMMANDS.md.
Roadmap/PDF includes the obligation review and proposed exact substitution
contract; final build /tmp/pts-rk-consistency-note.mqU7eX passes with clean
diagnostics. Full PDFKit inspector: 14 nonempty pages, four links, required
text/math and all-page renders; changed pages 4, 10–12 and 14 reviewed.
No full CI, staging, commit, push or cleanup. HEAD remains
6a8dc984fb59a9b3743503cd405ffe59a31d1978; index empty; prior dirty work preserved.

FIRST NEXT GOAL: independent capture-avoiding replacement on annotated
source codes, scoped-environment lookup/lifting, internal scope preservation
and exact standard agreement with original Syntax.subst. Keep binary indices
and lambda annotations. This serves dependent ApplicationRule and beta
Contract; scope preservation alone is NOT their semantic/typing soundness.
Then prove the actual source invariant and substitution/conversion contracts,
operation sufficiency, standard resource admission and all-budget soundness.
Generic Good_1/Look_5 motives do not automatically support these new invariants;
check exact ranks without adding the preservation conclusion to graph rules.
Next exact verification command:
bash docs/direct-r-handoff/verification/self-consistency-relational-2026-10-23/AUDIT.sh

## Histories, stratified cases and structural capacity — checked

Six new modules (670 lines): LookupInversion, InversionRealization,
LookupHistory, HistoryRealization, InternalCapacity, CapacityBounds. The
original kernel, common infrastructure and all seventeen prior proof modules
match their initial hashes. C, Good_1, Look_5 and Look_6 remain unchanged.

Independent Look_9 supplies a rank-12 constructor-case eliminator with actual
Look_5 child proofs and executable standard coverage. This is not matching
constructor inversion. Full two-Look_5 functionality has only its precise
type formed at U8, not an inhabitant. Independent Hist (rank 10) uses root
and Look_6-segment rules; its rank-11 soundness term folds into the existing
Look_5 relation using the previous composition term. Executable histories
cover arbitrary finite successful segment lists, with exact sequential
erasure/typing and application of actual internal soundness. This is
fixed-rank history iteration, not same-rank Look_6 closure or arbitrary lifting.

Tag-erasing shape preserves generation. Cap = Ext(shape a,shape b), rank 6,
has original-PTS reflexivity/transitivity, extension/join and lookup/history
laws. Exact beta correspondence and native-to-PTS realization yield a common
structural budget for every supplied finite family. Packing/fill and flattened-
path/result bounds are EXTERNAL; no bound is extracted from arbitrary Cap inhabitants
and no full operation envelope is claimed.

Fresh audit passes EVERY stage, 22:21:28–22:41:15 UTC (22 October,
23 October local): pristine build/kernel pass; fresh dependencies pass
22:24:58; separate audit passes 22:25:04, 242/242 closed reports (48 new).
Recursive kernel checking passes 22:25:04–22:41:15 (971 seconds), within
the up-front 1500-second allocation, no timeout. Complete inventory equals
pristine exactly: only unchanged functional_extensionality_dep, no unsafe
entries. Original-source and before/after source-stability checks pass. Logs:
_build/self-consistency-closure-audit.lZcvKp, fresh
/tmp/pts-rk-closure-fresh.e4JV26, pristine /tmp/pts-rk-closure-pristine.j8Tmf6.
Exact commands/failures/contracts in
verification/self-consistency-closure-2026-10-23/COMMANDS.md.
Roadmap/PDF rebuilt and inspected: 13 nonempty pages, four links, all-page
renders; changed pages 8–10/12 visually reviewed. Final build
/tmp/pts-rk-consistency-note.plrNsb has clean diagnostics.
No full CI, staging, commit, push or cleanup. HEAD remains
6a8dc984fb59a9b3743503cd405ffe59a31d1978; index empty; prior dirty work preserved.

FIRST NEXT GOAL: internally justified matching-constructor inversion and
arbitrary-path functionality at the actual equality/motive ranks, or a proved
relational invariant sufficient to replace their use in soundness. Direct
functionality induction needs a rank-8 motive, above Look_5's exact rank 5;
native syntax injection and higher-rank standard coverage do not fix this.
No impossibility theorem is claimed. Operation-specific resource/proof-history
bounds, standard admission, all-budget soundness and consistency remain open.
Next exact verification command:
bash docs/direct-r-handoff/verification/self-consistency-closure-2026-10-23/AUDIT.sh

## Path composition and root/leaf separation — checked

Four new modules, 551 lines: InternalPaths, ResourceSeparation,
PathSubstitution, PathRealization. Original carrier/guard/Look_5 and all
thirteen prior proof modules unchanged. Originally typed total plug with
generation, associativity and guarded unit laws; exact beta correspondence
on every raw tree and on quoted path concatenation. Independent Look_6
has the same local rules at motive rank 6. Actual rank-9 composition term:
Look_6(a,p,b) -> Look_5(b,q,c) -> Look_5(a,plug(p,q),c).
Executable higher-rank witness generation has exact erasure/typing and
standard coverage. The integrated standard theorem applies the actual
composition term, then converts to the exact concatenated-path type.

Independent Atom/Stop observations give internal root equality in BOTH
directions, root functionality for Eq_0 (predicate rank 0), and leaf/step
rejection. These use explicit padding, not normalization or assumed
functionality. Eq_0 is not native syntax equality or higher-rank transport.

Fresh audit passes EVERY stage, 18:05:33–18:16:53 UTC: dependencies pass
18:08:11, separate public audit 18:08:17, 194/194 closed reports (28 new).
Recursive kernel check passes 18:08:17–18:16:53 (516 seconds), within the
new focused script's 900-second limit for the larger closure; no timeout.
Complete inventory exactly matches pristine upstream: only unchanged
functional_extensionality_dep, no unsafe entries. Original-source and
before/after source-stability checks pass; prior thirteen proof modules
and shared infrastructure match their starting hashes.
Logs _build/self-consistency-paths-audit.8JCUle; exact commands/failures:
verification/self-consistency-paths-2026-10-22/COMMANDS.md.

Roadmap/PDF rebuilt/inspected: 12 pages, four links, all-page renders;
changed pages 8–9/11 visually reviewed. Final build:
/tmp/pts-rk-consistency-note.10Zuu9. First inspector output-directory error
fixed; all build/inspection attempts retained. Final clean diagnostics.
No full CI or commit/push. HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978;
index empty; prior user changes preserved; this continuation uncommitted.

FIRST NEXT GOAL: arbitrary-path constructor inversion/functionality with
the exact required equality motives, then justify the fixed-interface
iteration/transport needed by the resource invariant. Stratified composition
does NOT lift arbitrary Look_5 to Look_6 or establish same-rank closure.
No impossibility theorem for alternatives is claimed. Size/capacity,
full envelope, standard admission and all-budget soundness remain open;
there is still no internal consistency theorem.
Next exact verification command:
bash docs/direct-r-handoff/verification/self-consistency-paths-2026-10-22/AUDIT.sh

## Fixed-rank structural resource graphs — checked

New ResourcePaths, InternalResources, ResourceRealization (548 lines).
Independent tree lookup and injective structural paths; append-only left-spine
prefix is distinct from two-sided subresource extension. Actual original-PTS
rank-6 prefix/extension relations have reflexivity, transitivity, joining and
generation-preservation witnesses. Independent rank-7 lookup has root/step
witnesses, root/path/value generation and lookup-to-extension. Step/extraction/
extension law types have rank 8 (root law rank 7). The carrier C : U2 and
Good_1 : C -> U4 are unchanged; explicit inhabited rank-4 padding provides
exact rank-5 motives, without cumulativity or stronger guards.

Executable external witness generation erases exactly to independent lookup
and returns an originally typed PTS proof for every successful standard lookup.
Every standard prefix/extension also has a realization. Exact EXTERNAL size
bound counts the selected subtree and complete serialized path. Definitions
assume no source acceptance, normalization, resource sufficiency or consistency.

Fresh focused audit 17:36:43–17:43:35 UTC, every stage exit 0: 166/166 closed
public reports (39 new); recursive kernel inventory exactly pristine, only
unchanged upstream functional_extensionality_dep, no unsafe entries. Kernel
check takes 295 seconds within unchanged 300-second timeout; no timeout or
termination this turn. Original kernel, common infrastructure and ten prior
proof modules match previous hashes. Before/after manifests stable.
Logs: _build/self-consistency-resources-audit.X6R16B; progress:
_build/self-consistency-resources-progress. Commands/failures/hashes:
verification/self-consistency-resources-2026-10-22/COMMANDS.md.

Roadmap/PDF updated and validated: 11 nonempty pages, four links, all-page
renders; changed pages 7–8 visually reviewed. Final note build:
/tmp/pts-rk-consistency-note.Mv8Vt6. No layout/reference/glyph failures;
two inherited hyperref math-bookmark warnings documented. No full CI run.
HEAD 6a8dc984fb59a9b3743503cd405ffe59a31d1978; index empty, no commit/push
or cleanup. Existing unrelated user work preserved; changes uncommitted.

FIRST NEXT GOAL: witnessed internal path composition and arbitrary-input
lookup functionality/no-junk at explicit motive ranks, then internal size/
capacity comparison and the complete resource envelope/admission. Ext only
transports rank-4 constructor-closed predicates, NOT arbitrary rank-7 lookup
claims; concrete joins have explicit path/witness updates. No converse
parametricity, internal total decoder, all-budget soundness or internal
consistency theorem has been constructed. Internal checker/compression,
operation/transport/history bounds remain open.
Next exact verification command:
bash docs/direct-r-handoff/verification/self-consistency-resources-2026-10-22/AUDIT.sh

## Fixed PTS carrier and guarded finite pilot — checked

New InternalCarrier, GuardedTables, FiniteRejection modules (465 lines).
Actual ORIGINAL PTS carrier C : U2 for all 29 tags and binary pairing;
independent constructor guard Good_1(x) : U4; pair generation type rank 5.
Executable quotation/generation covers ALL raw trees, including malformed
and rejected inputs; quotation is syntactically injective. Structural
generation is not parsing, acceptance or resource admission.

Actual closed PTS terms give binary case elimination, closure and pointwise
Leibniz equality for arbitrary guarded Boolean selectors. Four table entries
are ordinary arguments at one fixed type. Separate guarded expansion laws
handle lookup without eta. Exact motives have rank 1; quantified laws rank 4.
Can_2 supports the rank-2 rejection motive. The rejection pilot covers the
COMPLETE closed height-zero/labels<=1 native fragment (two sort rules),
with table generated from the independent raw checker and computation/
coverage proved. Local syntax checking supplies branch evidence, not global
normalization or Bottom emptiness. This does NOT extend to unbounded proofs.

Reuse unchanged common annotated builder/checker infrastructure, not either
arithmetic interpretation. Original kernel and seven earlier proof modules
match previous hashes. Fresh audit 17:09:43–17:11:55 UTC, all exits 0:
127/127 public reports closed; recursive kernel inventory exactly pristine,
only unchanged upstream functional_extensionality_dep, no unsafe entries.
Before/after source manifests include common infrastructure and are stable.
Logs: _build/self-consistency-guards-audit.fLkaOG. Exact commands/failures/
hashes: verification/self-consistency-guards-2026-10-22/COMMANDS.md.

Updated roadmap/PDF builds and validates: ten pages, four links, all-page
renders, changed pages 5–7 visually reviewed, clean diagnostics. Final note
build /tmp/pts-rk-consistency-note.AZ6Pl2. Progress logs/renderings:
_build/self-consistency-guards-progress. No full CI run. HEAD remains
6a8dc984fb59a9b3743503cd405ffe59a31d1978; no stage, commit or push.
Unrelated user work preserved; new proof modules and updates uncommitted.

FIRST NEXT GOAL: fixed-carrier resource graphs for lookup, prefix, size and
joining, with actual guarded operation/closure witnesses and explicit exact
motive ranks. Good_1 is not a cumulative induction principle. Internal scope/
checker/compression relations, standard resource admission (also malformed
inputs), cost/transport/history bounds and all-budget soundness remain open.
No internal consistency proof has been constructed.
Next exact verification command:
bash docs/direct-r-handoff/verification/self-consistency-guards-2026-10-22/AUDIT.sh

## Homogeneous serialization and scope decoding — checked

Three new modules: StructuralCodes, CertificateSerialization,
SerializationBounds. One finite-alphabet external tree carrier; canonical
binary labels and indices; exact scope decoders for ORIGINAL annotated terms,
all beta/equality/typing constructors, context certificates and complete inputs.
Both inverse laws and injectivity hold, including complete inputs across
scope indices. Successful decoding re-encodes the literal input tree; malformed
tags/arity/bits/scope are rejected, never repaired. Raw acceptance is sound and
covers every original derivable judgment in a well-formed context.

Raw compression preserves acceptance and has domain exactly successful parsing,
independent of acceptance. Well-scoped rejected inputs still compress; malformed
trees remain raw values to be admitted by the eventual resource interpretation.
Every compressed label is bounded by the complete serialized input node count,
including all binary payloads, annotations, context proofs, conversion witnesses
and repeated fields. This is a data-size theorem, not a machine cost bound.

Final fresh focused audit 16:34:14–16:34:45 UTC, all exits 0: 85/85 closed
reports (43 prior, 42 new); recursive kernel inventory exactly matches fresh
pristine, only unchanged upstream functional_extensionality_dep, no unsafe
entries. Original kernel and four prior certificate/compression files unchanged;
before/after source manifests stable. Logs:
_build/self-consistency-serialization-audit.IjtwrQ; incremental attempts:
_build/self-consistency-serialization-progress. Exact commands/errors/hashes:
verification/self-consistency-serialization-2026-10-22/COMMANDS.md.

Roadmap/PDF updated: first build/inspection pass, nine pages, four links,
clean diagnostics, all-page renders, changed pages 2/5 visually reviewed.
No full CI rerun. HEAD 6a8dc984fb59a9b3743503cd405ffe59a31d1978; no staging,
commit or push; existing unrelated changes preserved.

FIRST NEXT GOAL: realize the fixed finite-alphabet carrier and generation guards
as actual PTS terms, then prove internal finite-table laws for arbitrary guarded
inputs with explicit motive-rank calculations. Keep structural generation,
scope/acceptance and resource admission distinct. Internal decoder/compression
relations, proof-transport/history bounds and all-budget bounded soundness remain
open. The present external representation is not an internal consistency proof.
Next exact verification command:
bash docs/direct-r-handoff/verification/self-consistency-serialization-2026-10-22/AUDIT.sh

## Native certificate adequacy and source-rank compression — checked

New PTSrk.SelfConsistency library: NativeProofCodes, CertificateAdequacy,
SortRenaming, RankCompression and Audit. Independent executable six-rule
certificates, raw annotated beta instructions, conversion trees and context
declaration certificates. Exact original typing and context soundness/completeness;
no typing or normalization premise in acceptance. Compression counts distinct
support labels below each source label, fixes 0/1/Bottom, preserves used product
equations, checking and original typing, and preserves term node counts.
Support includes context PROOFS, annotations, explicit/computed ranks and
conversion instructions. Every original judgment in a well-formed context
has a compressible accepted input. Compressed labels are bounded by two plus
recorded label occurrences; support labels remain distinct.

Final fresh focused audit 12:38:45–12:39:13 UTC, every exit 0. 43/43 own
closed reports; recursive kernel inventory identical to fresh pristine,
only unchanged upstream functional_extensionality_dep, no unsafe entries.
Original sources unchanged; source manifests stable. An earlier counting
harness defect (43 own plus one upstream report; missing failure propagation)
was corrected and the entire fresh audit rerun. Logs:
_build/self-consistency-native-audit.4cor29; incremental attempts/note builds:
_build/self-consistency-native-progress. Full commands, contracts and hashes:
verification/self-consistency-native-2026-10-22/COMMANDS.md.

Updated roadmap PDF: nine pages; final build/inspection 0, all-page renders,
changed pages 1–2 reviewed. First overflow failure retained and fixed.
CI stage 01-self-consistency added; shell syntax and scoped whitespace pass.
No full CI claim. HEAD 6a8dc984fb59a9b3743503cd405ffe59a31d1978; no stage,
commit or push in this continuation. Existing unrelated changes preserved.

FIRST NEXT GOAL: homogeneous serialization and a scope/certificate decoder,
then fixed-carrier guards and internal finite-table elimination. The present
certificates are intrinsically scoped Rocq data; completeness is existential
in Prop. Binary operation costs, transported proof/history bounds, internal
compression and arbitrary-budget soundness remain open. No internal PTS
consistency inhabitant has been constructed.
Next exact verification command:
bash docs/direct-r-handoff/verification/self-consistency-native-2026-10-22/AUDIT.sh

## Scoped publication — three developments

Committed Combinatory PTS (7a08071), shared self-interpreter folds
(7854d1d), and the direct consistency roadmap (9531808), including sources,
notes/PDFs and their scoped verification records. Publication targets
origin/main by ordinary fast-forward push; unrelated BZC/manuscript changes
remain uncommitted. The integration checkpoint records only these developments.

Publication checks: scoped source whitespace and four build/check shell
scripts pass (exit 0). Earlier fresh Rocq/Agda/kernel and PDF checks remain
the evidence recorded below; no new full CI or consistency proof is claimed.
Publication smoke check in the pinned environment also exits 0:
opam exec -- dune build -j 2 @theories/CombinatoryLogic-rk/audit
@theories/self_interpreter/audit (both targets in the same invocation).
This working-build check is not a fresh pristine assumption/kernel audit.
Next formal goal remains native certificate adequacy and rank compression,
then fixed-interface internal bounded soundness on arbitrary resource codes.
Next exact command: bash theories/self_consistency/build-note.sh DIRECT_ROADMAP.

## Direct internal-consistency roadmap — documentation checkpoint

Added theories/self_consistency/DIRECT_ROADMAP.tex/PDF (eight pages), with
the direct route prioritized over interpreting H or constructing EA proofs.
Target is a SPECIFIED resource-relativized structural consistency sentence.
Use independent native certificates, complete-certificate rank compression,
guarded finite induction, one fixed-type resource language, internally
proved history soundness and terminal separation. Adm(q) packages a resource
existential at answer universe U1; a single internal BS(q,b) then eliminates
it directly into Bottom. The final assembly/rank calculation is a paper
schema, not a new Rocq theorem. All standard raw inputs must be admitted
independently of acceptance; raw conversion intermediates need not normalize.

Current combinatory model-soundness is external Agda graded SYNTACTIC
soundness, not internal PTS soundness or fixed finite first-order models.
General finite models, rank-only dependent PHOAS algebras, raw tags, CPS and
native Hilbert completeness are not prerequisites of the preferred route.
Original native certificates differ from the draft's typed-equality T^e;
identifying internal consistency sentences requires a proved comparison.
The Gödel/diagonal/derivability-condition audit is an early viability gate.

Final note build 12:01:53–12:01:58 UTC, exit 0,
/tmp/pts-rk-consistency-note.O8CmUV; PDF inspection 0, eight nonempty pages,
four links, clean diagnostics, all-page renders and visual review. Earlier
malformed-tag and renderer failures retained. 244 proof/Dune hashes unchanged;
no new Rocq/Agda/kernel/CI run or consistency proof. Exact commands/reviews:
verification/self-consistency-direct-roadmap-2026-10-22/COMMANDS.md.
Raw logs: _build/self-consistency-direct-roadmap.HYlErI. Broad dirty work
preserved; HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef; no stage/commit/push.

FIRST NEXT FORMAL GOAL: native certificate interface and rank compression,
with guarded internal finite-table correctness in parallel. The critical
later goal is ONE fixed-rank internal bounded-soundness term on arbitrary
represented budgets, not another externally indexed family.
Next exact document verification command:
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP

## Shared PHOAS algebra and numeral-free folds — checked

Seven new modules implement shared typed-telescope Algebra.fold, tag-free
full-dependent identity interpretation, a concrete STLC constructor observer,
originally typed CBN local handlers/type-rank obstructions, and intrinsically
faithful finite-dictionary combinatory folds including actual CBV CPS.
GenericFold adds an actual normal head per signature, with the algebra fields
as ordinary arguments; it embeds no selected filling. Explicit expansion
uses beta only, not eta. Exact STLC/combinatory adapters preserve the codes.
The same rank-correct combinatory code supports CPS and finite Boolean
observation. Catalogue extraction/coding is not native PTS completeness.

Fresh dependency build exits 0 at 11:14:37 UTC; 92/92 public reports at
11:15:07; recursive FoldAudit kernel check at 11:19:55. Entire assumption
inventory equals independently rebuilt pristine: only unchanged upstream
functional_extensionality_dep, no unsafe checks. Compatibility audit and
source stability exit 0 at 11:32:11. Then GenericFold was integrated
byte-for-byte from its separately compiled source: all prior dependencies
unchanged, fresh public audit **106/106** at 11:34:46, recursive GenericFold
kernel/inventory comparison at 11:35:00, working audit and source stability
at 11:35:31. Two harness failures (warning-prefixed raw logs; BSD sed
alternation) and all proof attempts are retained with exact corrections.
No proof checks weakened. Logs: _build/self-interpreter-fold-audit.7pRHdb.
Exact commands/hashes/failures: verification/self-interpreter-fold-2026-10-22/COMMANDS.md.
No new full-repository CI run is claimed.
After verification, removed only this run's two fresh/pristine temporary
build directories (321 MiB); all raw logs/manifests remain. Rebuild with the
fresh command below, not the historical extension-resume command.

README reduced from 1086 to 183 lines. Interpreter note reduced from 15 to
10 pages (682 lines), with current contracts instead of development history.
Both it and the updated 10-page consistency note build cleanly; all pages
rendered and changed mathematical passages visually reviewed. Main alias
retains compatibility Audit and new FoldAudit. No staging/commit/push;
HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef; prior broad dirty work preserved.

FIRST REMAINING PHOAS GOAL: construct an actual semantic-indexed dependent
nonidentity algebra and its substitution/coherence laws. Generic correctly
typed fields are a fold interface, not a realization of those laws. Separate
goals: rank-only common signature; intrinsic arbitrary-source payload parser;
full dependent CPS; accepted-certificate internal soundness. Recovery alone
gives normal-source injection through a common algebra; retain the old
faithful envelope for its stronger contract. The variable-free bridge fixes
its dictionary and does not internally unquote heterogeneous expansions.
Next exact scoped verification command:
bash docs/direct-r-handoff/verification/self-interpreter-fold-2026-10-22/AUDIT.sh

## Contextual certificate soundness, finite packages and external Void exclusion

Thirteen new Agda modules are integrated. NativeCertificates gives independent
decidable proof trees for all six original rules, soundness and certificate
completeness; CertificateContexts checks contexts/valuation images without
native judgment premises. NativeRankCoverage computes a sufficient redex
bound, so arbitrary original typed terms normalize without supplied bounds.
NativeValuations/ContextualNormalization prove comprehension, substitution
composition, conversion and proof/budget-independent decoded normal values.
FragmentAlphabet/AlphabetCoverage give injective coherent inclusions and
exact finite coverage of every native term/context/valuation.

FragmentUniverses/Interpretation/Packages count contexts/types/values and
both-context substitution packages jointly, with concrete finite injections.
Every typed valuation has a raw package at computed bounds; no unjustified
normalization of dependent tuple components. FragmentModelSoundness checks
raw ModelInput and gives normal subject/type with exact substituted source
typing, forward reductions and jointly finite packaging. Rejection is only
for invalid certificates. FragmentModelExamples checks closed identity,
dependent X↦U₀, nonempty-target X↦Y, recovery and malformed-input rejection.
NativeCanonicity proves external Void-empty and certificate rejection for
Void = Π X:U₀.X, not internal PTS self-consistency.

Final fresh safe closure .xZU85m, 11:04:13–11:04:58 UTC, exit 0:
52 project modules, no warnings, ignored interfaces, isolated config/data,
stable copied sources. Earlier 51-module .fMhbvK also passed.
Agda 2.8.0-3d04bac; pinned clean Cubical v0.9 b150186d.
Final note .5WV08w, 11:06:27–11:06:41 UTC, build/validation0, inspector0:
25 pages, 3-page MM0 appendix, 23 Rocq / 27 Agda badges, 89 links.
All pages rendered and changed pages visually reviewed. Exact commands,
incremental failures, hashes and PDF review:
verification/combinatory-fragment-soundness-2026-10-22/COMMANDS.md.
All 24 Rocq sources/Dune and 38 prior Agda modules except Everything match
prior audited hashes. No new Rocq/MM0/full-CI run. Broad dirty work preserved;
HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef; no staging/commit/push.

FIRST REMAINING MODEL GOAL: specify the logical fragment/signature and give
total operations on fixed finite domains, with coherent dependent fibres
and all selected axioms under every semantic valuation. Current soundness
is a graded syntactic interpretation, NOT finite first-order model existence.
Rank-one products at one label already have unbounded normal size, so
faithful bounded syntax is not closed under all constructors; this does not
rule out nonfaithful finite models. Internal checker/compiler correspondence,
reflection, native Hilbert/QIIRT adequacy and binary Church correctness remain
separate. Package finiteness does not bound proof trees or host allocations.
Next exact verification command:
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh

Older entries below record then-current obligations; the new contextual,
alphabet/type-carrier and external Void results supersede those gaps.

## Total typed Agda normalizer and graded fragment soundness

applyTypedWithin now returns TypedResult, not Maybe: actual IIR normal output,
exact original Y[y] typing, bounded forward-beta trace and the existing
Knuth cardinality bound. NativeTyping's original six rules/ranks unchanged.
New NativeAlgebra/Substitution/Confluence/Inversion/Preservation/Ranks/Safety/
Descent/RankPreservation/Normalization establish the necessary metatheory,
including all annotation reductions. No normalization assumption, postulate,
replacement checker or unsafe option. Full native normalize also proves
conversion adequacy, uniqueness, budget independence and idempotence.

New FragmentEmbeddings/Application give finite typed normal fibres,
injective coherent size embeddings, original conversion, dependent graded
application, equality of outputs for convertible inputs and reachable-state
typing/rank invariants. FragmentMachineSoundness proves original typed
soundness of the existing finite-indexed executor. ApplicationExamples
checks genuinely dependent application, converted inputs and annotation beta.

Final fresh safe closure .vPyHLe, 10:08:50–10:09:32 UTC, exit 0: 39 modules,
no warnings, ignored interfaces/isolated config/data/stable source copies.
Agda 2.8.0-3d04bac; pinned clean Cubical v0.9 b150186d. Final note .FofOTf,
10:11:02–10:11:16 UTC, build/validation 0, inspector 0: 23 pages, 3-page
MM0 appendix, 23 Rocq / 20 Agda badges, 77 links. Changed pages visually
checked, all rendered. Logs/failures/hashes and exact commands:
verification/combinatory-total-agda-2026-10-22/COMMANDS.md.
All 24 Rocq sources/Dune match the prior pristine-audited manifest. No new
Rocq/MM0/full-CI run. Broad dirty work preserved; HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef;
no staging/commit/push. All parallel proof work finished or integrated by root.

First remaining model goal: explicit bounded type/universe carriers and
alphabet-extension coherence, then arbitrary-valuation/substitution and
all-rule interpretation from independent certificates. Closed typed fibres
and their graded operations are NOT yet full fragment models or internal
consistency. The alphabet restriction, fixed-type finiteness, graded output
and distinction from runtime allocations remain. Separate native Hilbert/
QIIRT adequacy and binary Church compiler correctness are still open.
Next exact verification command:
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh

Older entries below are chronological evidence; their totality gaps are
superseded by this checked milestone.

## Future-work programme added to the combinatory note

Added three proposed directions before References: objective PTS-rk with
quadratic type checking (arXiv:2102.00905, Theorem 7); logic-free partial-
function arithmetic with graph extension, finite basis/core, exists_n,
induction, finite models for every truncation and quadratic proof checking;
and an effective interpretation of the former inside the latter. These are
research goals, not new axioms, proved results or changes to original PTS.

Final note .nY0x2K, 09:30:31–09:30:45 UTC, build/validation exit 0.
New future-work inspector exits 0: 22 pages, 3-page MM0 appendix,
23 Rocq / 11 Agda badges, 66 links. All pages rendered in
/tmp/pts-rk-future-work-review.ni5QCq; pages 17–18 visually checked.
All 24 Rocq sources/Dune and 25 Agda sources match the previous audited
manifests. No new proof build/full-CI claim. Commands, hashes and review:
verification/combinatory-future-work-2026-10-22/COMMANDS.md.
Existing dirty work preserved; no staging/commit/push. Proof obligations
in the next entry are unchanged. Next note verification command:
bash theories/CombinatoryLogic-rk/build-note.sh

## Finite Church programs and explicit internal-consistency boundary

NEW ChurchFinite.v checks original polymorphic finite selectors E_m^r,
unary table maps and their d-fold compositions: formation rank r+1 for
nonempty data, r+2 for operator types, and forward beta to canonical outputs.
Carrier/selector normality and exact annotated size 2m+3 are checked too.
There are 17 new closed assumption reports. No original PTS rules changed.

NEW FiniteMachine.agda implements total finite-indexed greedy/application
tables and proves decoded d-pass agreement on source tower-bounded inputs.
Overflow fallback is unreachable on those runs. NEW ChurchFinite.agda emits
actual original annotated Term 0 programs: compileMap/compileMap2,
passProgram/applicationProgram/reductionProgram/applyReductionProgram.
Agda checks all-index selector typing/normality/size and small map regressions.
All 25 project modules pass the fresh safe closure without warnings.

IMPORTANT: binary maps' all-index target typing/beta and the Agda–Rocq
compiler correspondence are not yet formalized. Native unary correctness
is universal, not just tested. The generated normalizer is code-to-code,
not a semantic inhabitant of Y[y]. The previous total typed Agda interface
still needs original subject reduction and rank descent; Maybe is retained.
Finite-state tables do not bound all host allocations or the generated PTS
program by the original source N (a selector alone has 2K+3 nodes).

The note gives explicit encodings/programs and a conditional Pakhomov-style
consistency programme, matching self_consistency/README.tex. Finite runs do
not yet give fragment models: graded closure, embeddings, internal finite
case principles, independent certificate soundness and interpretation J
remain. No internal consistency theorem or Void exclusion is claimed.

Fresh native audit .0ceAEs, 08:59:33–09:00:25 UTC, exit 0, 19/19 stages:
24 modules, 241 own / 242 aggregate closed reports; recursive assumptions
match independently rebuilt pristine byte-for-byte, unchanged upstream
functional_extensionality_dep only. Original kernel unchanged.
Fresh Agda .4jl4SO, 08:59:00–08:59:34 UTC, exit 0, 25 modules, no warnings.
Final note .2lG4Vk, 09:03:29–09:03:43 UTC, build/validation 0; inspector 0:
21 pages, 3-page MM0 appendix, 23 Rocq / 11 Agda badges, 65 links.
All pages rendered _build/combinatory-church-finite-pdf-final.DKzMEm;
new pages visually checked. Full commands/hashes/failures are in
verification/combinatory-church-finite-2026-10-22/COMMANDS.md.
No new full-CI or MM0 run; MM0 unchanged. Broad dirty work preserved,
HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef; no stage/commit/push.

Next Church goal: all-index binary-table typing/beta in ChurchFinite.v,
then explicit generator correspondence. Next typed Agda goal remains
NativeTyping subject reduction, not adding normalization as an input.
Next exact native verification command:
bash docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/AUDIT.sh

## Finite IIR normal syntax and bounded Agda reduction

Added thirteen Agda modules; the complete 23-module closure checks safely.
NormalForms gives genuine Nf/NonLamNf/erase IIR syntax and injective erasure.
TypedNormalFibres gives exact annotated length N and type-rank bound d using
the ORIGINAL six-rule typing relation and truncated certificates.
typed-normal-bound proves an actual injection into Fin((4N+4) ↑↑ (d+3)).
Fix labels : Fin a → Nat with a≤N: rank/length alone is false (all U_i:U_0).

RawSizeBounds/BoundedTrace prove size for every single-beta intermediate of d
greedy passes without typing assumptions. FiniteTrace computes the faithful
finite-indexed path and proves each state's cardinal bound. Whole walks and
host allocations are NOT bounded. FiniteApplication/TypedApplication implement
the bounded attempt; successful results are IIR normal forms with bounded
forward reduction. TypedInputs has legitimate original f/y/product-sort
premises only. Here d is the exact product sort rank and N=1+|f|+|y|.

IMPORTANT: the requested TOTAL typed Agda normalizer is still OPEN.
applyTypedWithin : TypedInputs a → Maybe(Result inputs), not TypedResult.
TypedResult's Y[y] fibre/cardinality is defined/proved, not its inhabitance.
Next proof target: NativeTyping subject reduction (original weakening,
substitution, conversion/context lemmas), then typed rank uniqueness/descent
and normal_application_rank_bound; eliminate Maybe without adding the desired
theorem as an input. A carrier-only evaluator is a further implementation
obligation; compiling an already constructed Raw trace to Fin is not that.

Fresh safe closure /tmp/pts-rk-combinatory-agda.7UFFIh, exit 0,
08:12:27–08:13:03 UTC, all 23 modules, no warnings, stable source copies.
Agda 2.8.0-3d04bac; clean Cubical v0.9 b150186d.
Note section 7 now immediately follows QIIRT; literal highlighted excerpts
and nine Agda proof badges. Final PDF .5X2knp, 08:17:32–08:17:45 UTC,
build/validation 0; inspector 0: 18 pages, 3-page MM0 appendix, 22 Rocq badges,
17 Agda links, 58 links. Renders _build/combinatory-finite-pdf.6WaFbZ;
changed pages visually inspected. Initial glyph failure fixed locally; no
validator weakened. No new Rocq/MM0/full-CI run: 23 Rocq sources and Dune
match the prior pristine-audited manifest byte-for-byte. No native source edit.

Exact commands, versions, hashes, failures and remaining goals:
verification/combinatory-finite-agda-2026-10-22/COMMANDS.md and
theories/CombinatoryLogic-rk/EVIDENCE.md. Existing broad dirty/intent-to-add
work preserved; HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef, no stage/commit/push.
Next exact verification command:
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh

## BCKW arithmetic, Knuth bounds and independent safe QIIRT

Current note: section 2 gives BCKW(I) arithmetic, n occurrences of W and
7n+2 atoms, succ/add/mul with 8/9/1 atoms, type ranks 2/3. The old abstract
sentence and affine-generator section are removed. B is composition, W is
duplication; AffineDuplication.v's constructor is corrected. BCKW.v checks
original annotated typing, counts, arithmetic and unapplied normalization.
KnuthBounds.v proves the comparison used for all displayed tetration bounds.

The independent 435-line agda/BCKW.agda gives B/C/K/W/I/P literal families,
guarded laws and structural contraction; note excerpts read this source.
It passes safe checking without the dependent S module. The full dependent
Hilbert/MM0 catalogue is RETAINED: simple BCKW substitution macros pass, but
specific dependent versions fail scoped typing tests. This is not a
nondefinability theorem or a native adequacy proof. Do not erase annotations
or rename the missing dependent scheme as BCKW. Old supporting Agda files
remain checked independently. The prose describes final constructions only.

Fresh focused 23-module audit exits 0, 19/19, 06:36:36–06:37:27 UTC:
_build/combinatory-bckw-audit.Hukon3. Fresh /tmp/pts-rk-combinatory-bckw.bnSrlP;
pristine /tmp/pts-rk-combinatory-bckw-pristine.p0tvSU. 224 own/225 aggregate
closed reports; byte-identical recursive assumptions against new pristine,
unchanged upstream functional extensionality only; no unsafe/new assumptions.
Fresh safe ten-module Agda closure exits 0 at /tmp/pts-rk-combinatory-agda.Td8Ru5
(06:31:13–06:31:36 UTC). MM0 .FNFzjw passes 4/4. Final note .2GZNlI passes
(06:40:36 UTC), 15 pages, 3 appendix pages, 22 badges, 43 links; inspector/renders
_build/combinatory-bckw-pdf.RO8PaR. Changed pages visually checked.
Exact commands, attempts and hashes: theories/CombinatoryLogic-rk/EVIDENCE.md
and verification/combinatory-bckw-2026-10-22/. No new full-CI claim.
HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef; no staging/commit/push.

First remaining basis goal: originally typed, annotation-preserving derivation
of dependent substitution from BCKW numeric families (or an explicit exact
obstruction). Simple macro failures do not settle general polymorphic schemes.
Native PTS-to-Hilbert completeness still needs major-chain shortening, typed
exposure and deduction; QIIRT logical coherence/adequacy and MM0/native
adequacy are separate. Normal binder-free output size is not proved.
Next exact audit command:
bash docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/AUDIT.sh

Older entries below are provenance, not current notation or proof status.

## Affine numeral fragment and elementary finite normalization

Four new checked modules in CombinatoryLogic-rk: AffineDuplication,
QuantitativeNormalization, FiniteNormalForms and GroundHorn. Native tagged
numerals have exactly n B and 2n+1 atoms and reduce forward to Church normal
forms. The note additionally gives an untyped universal affine J calculation
with n B and 49n+7 atoms; it is not a checked universal-J compiler. A full
dependent BJ replacement is NOT claimed, because dependent fibres and original
annotations need a separate typed compiler. The established Hilbert catalogue,
MM0 and Agda signatures remain in place. The requested substitution-index
subsection is removed, not the underlying safe two-index implementation.

For global redex-head bound d (including annotations), deterministic greedy
sequentialization keeps every single-beta intermediate within tower d N,
preserves typing and rank bound, and has the existing elementary abstract-cost
bound. For normal dependent application, d is the function's type rank.
Outer type rank alone is not this semantic bound. Rank/size alone do not give
finite normal terms: all U_i:U_0 are normal, rank 0, size 1. Fixing the input
label alphabet gives a complete raw carrier of capacity tower(d+2)(4N+4).
Bounds concern syntax states, not arbitrary typing witnesses/external types,
machine configurations or compiled normal BJ code.

The generic grounded-Horn derivability/consequence equivalence and all-true
singleton model are checked. Effective grounding gives a mathematical faithful
GROUND-QUERY reduction in infinite recursive vocabulary. It is not a faithful
finite syntax model, finite-signature quantified interpretation or MM0/native
adequacy theorem; it holds independently of the normalization bounds.

Fresh joint audit exit 0, all 19 stages, 05:25:45–05:26:34 UTC:
_build/combinatory-bj-bounds-audit.4WaD8n. Fresh 21-module build
/tmp/pts-rk-combinatory-bj-bounds.TgqGUp; independently rebuilt pristine
/tmp/pts-rk-combinatory-bj-bounds-pristine.de3PBe. 199 own/200 aggregate closed
reports; recursive inventory identical to new pristine (unchanged functional
extensionality only), original kernel and old 17 proofs unchanged. No unsafe
entries or new assumptions. Initial audit .E63DNW failed only on two Agda EOF
blank lines, removed before the full unchanged audit rerun. No full-CI claim.
Fresh safe Agda check .LMgEkR passes all 9 modules, 05:28:49–05:29:10 UTC;
MM0 .asWdz6 passes 4/4 stages. Final PDF build .DRrwv0 passes, 05:31:18 UTC:
15 pages, 3 appendix pages, 23 badges, 46 links; renders/inspection
_build/combinatory-bj-bounds-pdf-final.Ge5Gtk. Exact commands/failures/hashes:
theories/CombinatoryLogic-rk/EVIDENCE.md. HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef;
no staging, commit or push; unrelated user work preserved.

First remaining BJ goal: original-typed annotation-preserving dependent
affine/contraction compilation and a normal output size theorem. Existing
native PTS-to-Hilbert completeness still needs major-chain shortening/typed
exposure/deduction; Agda logical-guard adequacy and MM0/native adequacy remain
separate. Next exact command:
bash docs/direct-r-handoff/verification/combinatory-bj-bounds-2026-10-22/AUDIT.sh

## Linear note and complete safe Cubical signature

The note is reordered as requested: finite-basis obstruction follows the
calculus; the literal catalogue and MM0 are consecutive subsections of the
complete Hilbert presentation. History is removed from the exposition.
The actual Agda sources declare Con/Sub before Ty/Tm, use RankedTy and
document all four sorts. TargetView checks the source-only ctxOf comparison;
both round trips hold, but fixed-target projections add equality/transport,
so the core retains two indices. Exact contains a safe relative QIIRT and
ordinary representatives, not an original-PTS adequacy theorem.

Pinned Agda 2.8.0-3d04bac with Cubical v0.9 b150186d passes the fresh --safe,
--ignore-interfaces import-closure check in
/tmp/pts-rk-combinatory-agda.M1bpnK (exit 0, 04:41:14–04:41:34 UTC).
All nine modules are covered, with source-copy and final stability checks.
The four fixed I/K/S/P families and named guarded laws are present. S's literal
six-binder type uses seven proof-only annotation guards; SCanonical supplies
them uniformly, and SGuardIrrelevance proves their irrelevance and independence
of the resulting S atom/type. The public S family has only numeric indices.
Structural coherence guards and Exact's conditional witness-irrelevance
lemmas are proved. No postulates, holes, disabled checks or opaque/optimization
workarounds remain. Earlier three-atom checks are superseded; exact failed
positivity/expansion attempts, terminations and limits are in EVIDENCE.md.

Final PDF build /tmp/pts-rk-combinatory-note.c58OXY exits 0, 04:43:06 UTC, no
layout/glyph/reference/highlighting warnings. Inspector output
_build/combinatory-agda-pdf.QaZM2w: 13 pages, 3 appendix pages, 19 Rocq badges,
40 links, all pages rendered; changed Agda pages visually inspected.
Both long Agda excerpts remain unbroken. The note explains the fixed atom
types/laws and links the canonical S proofs. MM0 recheck
/tmp/pts-rk-combinatory-mm0.ITdtk4
passes all 4 stages. All seventeen Rocq files and Dune remain hash-identical
to the preceding fresh audit. No new Rocq/full-CI audit is claimed.
HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef; no staging/commit/push.
Next exact Agda verification command:
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh
First remaining Agda obligation: derive the logical beta/application-
naturality coherence guards from their intended typing premises. Native
interpretation and equality reflection remain separate. Original Rocq
completeness still requires general major-chain shortening, typed exposure
and deduction; no new source-completeness theorem is claimed.

## MM0 Hilbert specification and three-page source appendix

The new CombinatoryPTS-rk.mm0 independently presents the 65-shape Hilbert
system as a many-sorted Horn theory: explicit annotated de Bruijn syntax,
numeric/shift/substitution/reduction graphs, fixed ranked telescope builders
and six Hilbert rules. Its form relation is syntax-only, used solely by fixed
P11/I7/K17/S30 catalogue rows; there is no native typing oracle or arbitrary-
body scheme. The 156-line source is included literally in a highlighted
three-page appendix (PDF pages 12–14), with exposition/rule excerpt at the
end of Section 4. The complete PDF has 14 pages, 19 Rocq badges and 35 links.

Official MM0 tools pinned at 0d414c0bfdaaeb7fea571895127abc1fa5a3d956:
mm0-rs 0.1.0 (isolated Rust 1.99.1), mm0-c (Apple Clang 21.0.0). Four check
stages pass, exit 0, 03:15:15 UTC, logs /tmp/pts-rk-combinatory-mm0.Bl222O.
Both declarations and ten actual local .mm1 proof regressions pass the
independent checker against the same public specification. A deliberately
capturing substitution is rejected by compiler/checker with exits 1/3.
Tools, negative artifacts and build provenance: /tmp/pts-rk-mm0.lhphPY/AUDIT.txt.
No toolchain/global-security configuration changes. No timeout.

The mathematical encoding audit is NOT a machine-checked MM0/Rocq adequacy
bridge or source-completeness theorem. MM0 axioms specify the requested
logical theory; no new Rocq axioms. All seventeen Rocq files and Dune match
the previous fresh audit's hashes; no new assumption audit or full CI run
is claimed. Shell syntax and scoped whitespace checks pass.
Final PDF build /tmp/pts-rk-combinatory-note.rwsq7f exits 0, 03:16:56 UTC,
no layout/glyph/reference/highlighting warnings. New PDF inspector verifies
excerpt, full-source appendix, links and renders every page; final evidence
_build/combinatory-mm0-pdf.B8Ovnb. Initial rendered-listing defects were caught
by text inspection and fixed; exact paths, commands and hashes are in
theories/CombinatoryLogic-rk/EVIDENCE.md.
HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef; no staging, commit or push.
Unrelated changes and IDE intent-to-add entries preserved.

First remaining source-proof goal is still general major-chain shortening
with a valid sharing measure, then typed product exposure/internal type
correctness/deduction. An MM0/Rocq adequacy proof is a separate new obligation;
finite MM0 regression proofs do not discharge either one.
Next exact MM0 verification command:
MM0_RS=/tmp/pts-rk-mm0.lhphPY/upstream/mm0-rs/target/release/mm0-rs MM0_C=/tmp/pts-rk-mm0.lhphPY/mm0-c bash theories/CombinatoryLogic-rk/check-mm0.sh
Next proof-audit command remains:
bash docs/direct-r-handoff/verification/combinatory-completeness-2026-10-22/AUDIT.sh

## Contextual Hilbert proof steps, external completeness corollary and QIIRT

The note now explicitly proves the literal 66/65 catalogue's mathematical
completeness by finite symbolic-template inclusion and the EXTERNAL
Bunder–Dekkers Theorem 9.4. This is not a Rocq theorem or axiom. The requested
unconditional Rocq direction `typ ε M A -> CatalogueEconomy.Derives M A`
REMAINS OPEN; do not infer it from the following supporting results.

Six new modules: ContextualHilbert defines independent H+ with no lambda/Pi
rule and no native typing constructor premise; it proves context validity,
internal start/variables, convertible application and empty-context 65/66
equivalence. ContextualSubstitution proves general and single substitution
with H+-certified images. ProductExposure proves literal subject/type-prefix
compatibility and forward beta simulation along application spines, preserving
annotations. CatalogueShapes isolates exactly seven neutral-ended atoms and
their strict body-application count decrease. HilbertAbstraction proves exact
I/K and P/S assembly with needed family derivations explicit. HilbertReplay
uses finite shared-reference application graphs and checks local dependent-S
six-to-three contraction at the same exact type with original forward beta.
None proves arbitrary-chain shortening or assumes it as a target hypothesis.
All eleven preceding proof modules remain byte-identical.

The Agda signature is now natural-model QIIRT: Tm Gamma has no type index,
tyOf returns a ranked Sigma type, Ford-style guards retain intrinsic typing,
and recursive clauses handle term paths and set truncation. Ordinary Agda
retains explicit typed setoids. Weak GAT and exact native-expansion quotient
stay separate, without lambda, eta or unrestricted quotation. The snippets
have minted/Pygments Agda highlighting, but are NOT typechecked Agda. Installed
2.6.0.1 fails the unchanged paper artifact targeting 2.8.0 at Prelude:47;
no artifact postulates or unchecked eliminators were adopted.

Fresh focused audit passes all 19 stages, exit 0, 02:24:10–02:25:00 UTC:
159 own closed reports, 160 aggregate; seventeen-module recursive kernel
inventory byte-identical to freshly built pristine upstream, only unchanged
functional extensionality and no unsafe entries. Original-source comparison,
source stability and safety checks pass. Logs
_build/combinatory-completeness-audit.fG2a7B; fresh build
/tmp/pts-rk-combinatory-completeness.0GagN7; pristine
/tmp/pts-rk-combinatory-completeness-pristine.9z34Nq. Full local CI/actionlint
passes 227/227 stages without retry, exit 0; logs
_build/combinatory-completeness-full-ci.1noh6m, exit-file 02:24:40 UTC.
Final highlighted PDF build /tmp/pts-rk-combinatory-note.xQ0lm0 exits 0,
ten pages, finished 02:30:59 UTC; no layout/glyph/reference/minted warnings.
PDFKit verification renders all pages and checks nineteen local proof links
plus eleven references. Text/link/render evidence and the failed Agda-version
compatibility probe are retained in _build/combinatory-completeness-pdf.mMbycs.
Changed pages 5–10 were visually inspected; exact commands and source/PDF
hashes are in theories/CombinatoryLogic-rk/EVIDENCE.md.
First audit's CatalogueShapes tactic-name failure and all targeted failures
are retained and summarized in theories/CombinatoryLogic-rk/EVIDENCE.md.
HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef; no staged content, commit or
push. Existing unrelated changes and IDE intent-to-add entries preserved.

First remaining formal goal: replay arbitrary major-premise chains with
interleaved weakening/conversion/reduction and prove a decreasing shared
measure. Ordinary tree size AND maximum proof height fail for S duplication.
Then prove length-controlled typed product exposure, internal correctness of
types and deduction admissibility. Catalogue maps, syntactic exposure and
local shared S shortening do not alone supply these results. The alternative
route would formalize symbolic catalogue inclusion AND the external theorem;
merely citing it must never create a Rocq axiom. Four-core completeness and
intrinsic equality reflection are separate open goals.
Next exact verification command:
bash docs/direct-r-handoff/verification/combinatory-completeness-2026-10-22/AUDIT.sh

## Combinatory GAT/QIIT specification and checked 65-shape economy

The nine-page CombinatoryPTS-rk note now specifies a first-order contextual
GAT with Con/Ty/Tm/Sub and idealized Agda QIIT syntax, plus a distinct exact
typed-expansion quotient. The latter explicitly uses original Typing.typ;
it is not an independent checker or completeness proof. Typed endpoints,
dependent transport, original universe ranks and set truncation are explicit.
No lambda, function eta or unrestricted type-to-term quotation is added.
Neither QIIT pseudocode nor its native interpretation/reflection is claimed
machine-checked. New QIIT primary references and thirteen proof badges included.

New IdentityCatalogue I7, ConstantCatalogue K18 and SubstitutionCatalogue S30
uniformly prove original typings, ranks and literal type/exposure maps.
CatalogueHilbert combines P11/I7/K18/S30, internally derives every declared
type and catalogue-atom exposure, and proves original soundness/extraction.
CatalogueEconomy removes redundant local K13 by an independently typed K/P5
application macro. derives_iff proves EXACT Hilbert judgment equivalence of
the explicit 65/66 systems; all indices remain numerical. This reconciles
our economy target, not the paper's unlisted numbering or its shortness proof.
Original-PTS completeness, general symbolic fresh-sort closure and equality
reflection remain open. The six preceding proof files are byte-identical.

Fresh audit passes all 19 stages, exit 0, 01:36:23–01:37:09 UTC: 92 own closed
reports, 93 aggregate including upstream. Fresh original snapshot/build,
all-eleven-module recursive kernel checks, byte-identical inventory comparison,
original-source comparison, safety and source-stability checks pass. Only
unchanged upstream functional extensionality is loaded, no unsafe entries.
Logs _build/combinatory-gat-audit.FoWhA6; build
/tmp/pts-rk-combinatory-gat.hDbC80; pristine
/tmp/pts-rk-combinatory-gat-pristine.bwllE6. Complete local CI/actionlint passes
227/227 stages without retry, 01:36:24–01:36:53 UTC, exit 0; logs
_build/combinatory-gat-full-ci.ZhCicn. Existing combinatory stage covers the new
modules; no CI stage was weakened or removed.

Final TeX build /tmp/pts-rk-combinatory-note.B5iS8i exits 0, nine pages with
no LaTeX/layout/reference/glyph warnings. Exact QIIT block stays on page 8;
references on page 9. PDFKit text/link/render checks pass: thirteen proof
links, eight reference links. Final visual evidence:
_build/combinatory-gat-pdf-final.wm5Jze. Detailed commands, failed attempts,
versions, hashes and boundaries: theories/CombinatoryLogic-rk/EVIDENCE.md.
HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef, no staged content, commit or
push; existing unrelated work and IDE intent-to-add entries preserved.

First remaining goal: define contextual Hilbert H+ and prove length-controlled
product exposure for ARBITRARY derived products, not only scheme atoms. This
must supply internal correctness of types and deduction admissibility; do not
use native type correctness as a substitute for an internal Hilbert witness.
The GAT soundness/strong-equality comparison is a separate formalization goal.
Next exact verification command:
bash docs/direct-r-handoff/verification/combinatory-gat-2026-10-22/AUDIT.sh

## Combinatory Hilbert continuation — renamed library, note and product catalogue

The physical directory is theories/CombinatoryLogic-rk; the logical library
remains PTSrk.Combinatory. CombinatoryPTS-rk.tex and its five-page compiled PDF
give the logical/Hilbert presentation, proofs-as-terms explanation, external
Bunder–Dekkers completeness theorem and nine local formalization badges.
All original annotations and beta-only conversion are retained. Core,
Presentation and FiniteBasis are byte-for-byte unchanged from the preceding
checkpoint. No primitive, typing rule or external Rocq axiom was added.

ProductCatalogue uniformly types all eleven product schemes, proves their
exact type ranks and literal declared-type/product-exposure maps. P4/P5
compile into the existing four-family grammar with independent HasType
derivations and literal forward-beta recovery. Hilbert independently defines
scheme/universe axioms and application/conversion/subject/type reduction;
soundness and typed applicative extraction are proved for separately verified
catalogues. ProductHilbert discharges the catalogue premise for numerical
I/K/S plus eleven product schemes, and derives each product atom's type at
its exact rank INSIDE Hilbert inference. Extracted codes are certified through
original typing of their expansion, not a full independent code-typing system.
Full 65-shape completeness and four-family completeness remain unproved.

Fresh audit: exit 0, all 19 stages pass, 00:59:24–01:00:00 UTC. 51 own closed
reports, 52 aggregate including upstream. Separate pristine upstream build,
recursive kernel checks of all six modules, byte-identical inventory
comparison, original-source comparison, source stability and safety checks
pass. Only unchanged upstream functional extensionality is loaded, no unsafe
entries. Logs: _build/combinatory-hilbert-audit.H87sn7. Fresh absolute build
/tmp/pts-rk-combinatory-hilbert.ZBLheh; pristine snapshot
/tmp/pts-rk-combinatory-pristine.iMsccY. The driver adds stage 01-combinatory;
complete local CI/actionlint passes all 227 stages, exit 0, no retry,
00:59:31–01:00:01 UTC; logs _build/combinatory-hilbert-full-ci.OO1Ub7.

Final PDF build /tmp/pts-rk-combinatory-note.Y2Kfbl exits 0, without LaTeX,
layout/reference/glyph warnings. PDFKit text/link/render checks pass for five
pages, nine source badges and three reference links; all pages visually
inspected. Logs/images: _build/combinatory-hilbert-pdf.dyMANc. Exact commands,
versions, all failed attempts and source hashes: current
theories/CombinatoryLogic-rk/EVIDENCE.md. Earlier entries below keep historical
paths and superseded status statements for provenance.

HEAD remains cb76553b03d536743e36c4e2c7e5a1c7c1669bef; no staged content,
commit or push. Existing unrelated edits were preserved; some older new files
retain IDE intent-to-add entries. Rename/new work is uncommitted.
First remaining proof goal: auxiliary I/K/S catalogues, internal type/exposure
derivations, then original-PTS-to-Hilbert completeness. Compiling all remaining
auxiliaries into the four-family grammar is a separate smaller-basis question;
do not assume the dependent abstraction recursion is well-founded.
Next exact verification command:
bash docs/direct-r-handoff/verification/combinatory-hilbert-2026-10-22/AUDIT.sh

## Combinatory PTS-rk — finite-basis obstruction and indexed core

New independent library PTSrk.Combinatory uses original annotated Term nat,
Typing.typ and RankSorts. FiniteBasis.no_finite_typed_basis proves that finitely
many fixed closed typed atoms, even with EVERY universe atom, cannot beta-
represent all closed typed terms through originally typable application trees.
The proof uses type-rank monotonicity along applications and explicit inhabitants
at every rank; it permits conversion, not merely forward recovery.

Core proves arbitrary-index original typings, exact type-sort ranks and literal
beta laws for I, ordinary K, dependent S, product P and optional dependent K.
Presentation supplies binder-free subjects, an independently inductive mixed
typing relation, original soundness and weak-reduction simulation. Its types
remain original PTS syntax; equality is beta conversion of expansions. No
completeness of this four-family core or of the proposed telescope families.
FORMULATION.md specializes the external supersorted Hilbert completeness theorem
and records the dependent type-family recursion/equality gaps. No external
theorem was added as a Rocq axiom and no source rule was changed.

Fresh focused audit exits 0, 00:35:48--00:36:22 UTC, all 17 stages pass.
32 own reports are closed (33 aggregate including unchanged upstream).
Separate pristine upstream build, recursive kernel checks and byte-identical
assumption-inventory comparison pass. Original kernel source comparison and
source stability pass. Only unchanged upstream functional extensionality is
loaded; no unsafe entries. Raw logs: _build/combinatory-audit.ZXAnfW.
Fresh directory /tmp/pts-rk-combinatory-audit.vEp9MB; pristine snapshot
/tmp/pts-rk-combinatory-upstream.AkuTX9. Duplicate same-source dependency-path
warnings are retained. This is not a new full staged local-CI result; its
driver is unchanged. Exact commands/failures/hashes: theories/Combinatory/EVIDENCE.md.

HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef, index empty; new work uncommitted.
No commit/push; existing unrelated edits and running audits preserved.
First remaining goal: compile the finite auxiliary type-family/product-exposure
catalogue into the proposed telescope combinators, uniformly in numeric ranks,
with original typing and annotated beta recovery. Then establish completeness;
do not assume inferred domain/codomain recursive calls are well-founded.
Next exact command:
bash docs/direct-r-handoff/verification/combinatory-2026-10-22/AUDIT.sh

## Uniform closure head and internal-budget boundary

The five new self_consistency files were committed, as requested, in
cb76553b03d536743e36c4e2c7e5a1c7c1669bef. No push was requested this turn.
Current self-interpreter continuation changes are not committed.

FixedInterface supplies one original normal decoder for normal closures
carrying a hidden domain, program and runner; it computes runner(program),
not a precomputed result. RankPadding realizes exact common sorts without
cumulativity. FragmentClosureInterpreter.every_bounded_original fixes k
before independent source fragment membership and proves one head of exact
type-sort k+10. Its application spine is head(k) (Pad_k(nf T)) code d_k,
originally typed at T and reducing to literal source t. Normality and
cross-budget syntax/conversion injection are retained. Only source TYPE is
normalized; the runner remains plan/type-specific. The final fixed argument
uses the supplied type's explicit function shape, not an eliminator for
arbitrary types of the common sort. Underlying capped literal type-program
recovery remains separate. This is a common closure execution interface,
not a common PHOAS constructor algebra or internal reifier.

BudgetInternalization proves the precise bounded-literal obstruction for
fixed reifier/evaluator pairs with arbitrarily many represented inputs.
It does not obstruct fixed fragments or Bottom-specific internal soundness.
FiniteLiteralBank proves one normal rank-2 decoder for each finite sort bank,
using normal literal-zero Church selectors. NumericLiteralBank now proves
actual Church-numeral selection: a normal original rank-4 head recovers
U_min(i,k); normal numeral inputs have literal ceiling zero. The monomorphic
state carrier depends on k; overflow saturates rather than rejecting. This
does not establish correctness for arbitrary inhabitants/accepted proof codes.
FixedInterface.inhabited_iff makes the internal reifier's soundness content
explicit; no independent certificate acceptance theorem is claimed.

All six new proof modules compile in the pinned environment. Fresh aggregate
compilation in /tmp/pts-rk-self-uniform-audit.ZjpFUy passes: 2706 own closed
reports plus one unchanged upstream report across the three fresh build stages;
1112 public Check/Print pairs and 129 source/Dune manifest entries. Both fresh
recursive kernel checks pass; interpreter check 00:27:42--00:36:42 UTC,
exit 0. Historical and freshly rebuilt pristine inventories agree; original
frozen-source comparison, all 129 stability checks and source safety/whitespace
checks pass. The loaded inventory contains only unchanged upstream functional
extensionality, with no unsafe/type-in-type/assumed-positivity entries;
own endpoints are closed.
Complete local CI/actionlint passes all 226 stages, exit 0, with no retry.
The expanded note builds warning-free to 15 pages in
/tmp/pts-rk-self-note.PKoaj6; PDF inspection passes. The consistency note's
status update builds warning-free to ten pages in
/tmp/pts-rk-consistency-note.7u3pxt. Exact evidence, hashes and build script:
verification/self-interpreter-uniform-interface-2026-10-22.
First remaining mathematical goal: an independently defined certificate
trace/domain and actual internal accepted-code reification at Bottom, with
internal resource/budget handling. Full-source numeric literal reification
at unbounded ranks is ruled out only under the stated bounded-literal premise.
No CPS translation is formalized. Next exact audit commands: run AUDIT.sh
pristine, then prebuild, then default mode in the evidence directory above.
Full-CI mode is ci.
The completed fresh Dune directory and independent pristine snapshot were
removed after verification (644064 KiB total); raw logs, working build and
all sources/PDFs are retained. Re-run pristine/prebuild to recreate caches.

## Internal consistency — research note and two formalization routes

Created theories/self_consistency as a documentation-only future development,
with README.tex/PDF, README.md, build-note.sh and EVIDENCE.md. The nine-page
note extracts the supplied Zermelo-revision draft's precise predicate-only
consistency target and tower-witnessed EA soundness construction. It maps
existing normalization, original certificates, arithmetic deduction and capped
PHOAS results to their actual contracts. No new Rocq proof or Dune target.

The requested higher-order H^omega_<omega route is distinguished from the
draft's first-order H_<omega route: external Pakhomov Lemma 3.11 uses S and
H^omega; Corollary 5.3 uses 2S and H. Higher-order comprehension and a stable
rank policy need their own direct interpretation. The second route constructs
a fixed resource-restricted proof arithmetic and internal checker-to-PHOAS
reification. Uniform fragment interpreters would simplify that interface,
but external indices, domain closure and internal soundness remain obligations.
A consistency-specific evaluator can omit the syntax tag/fidelity layer.

Final document build: /tmp/pts-rk-consistency-note.KlGtoS, exit 0, nine pages,
no layout/reference/glyph warnings. PDFKit inspection exits 0; pages 1,3,5,7,9
visually checked. Raw inspection: _build/self-consistency-note-2026-10-22.
EVIDENCE.md records input hash, exact declarations, all failed layout attempts,
versions and final hashes. No new Rocq/CI result is claimed. Existing proof
sources, toolchain and unrelated dirty work are preserved.

The five self_consistency files were subsequently committed in cb76553;
this entry describes their document-only verification, not a new proof audit.
First proposed proof task: fix independent T^e rules and binary certificates,
acceptance-to-original-typing bridge, and a syntactic NormalBottom lemma.
Do not treat the draft or external Pakhomov transfer as a Rocq axiom.
Next exact document command: bash theories/self_consistency/build-note.sh.

## Scoped publication and completed-cache cleanup

The user requested commit/push of the two capped-fragment milestones below.
The enclosing publication commit includes only self-interpreter work and its
handoff/evidence; unrelated BZC, CI and documentation edits are excluded.
Proof and PDF bytes are unchanged from the retained verification manifests.
Publication-time FINAL-CHECKS revalidated source hashes and kernel/CI evidence,
then stopped at git diff --check: an extra EOF blank line in
CappedCodeAlignment.v. This whitespace warning is retained to preserve the
audited source hashes; no fresh kernel or complete CI rerun is claimed.
Completed external Dune caches were cleaned after checking their .db/default
markers and that no Rocq/Dune processes remained. Sources, pinned toolchain,
working build and all retained raw verification logs were preserved.
Available space rose from 398964 to 2807888 KiB (about 2.3 GiB reclaimed).
Exact targets and publication/check commands:
verification/self-interpreter-capped-publish-2026-10-21/COMMANDS.md.
The next mathematical goal remains the common interpreter term described below.

## Capped quotation — full-source coverage at a common rank bound

The capped port now compiles through CappedDependentInterpreter. All six
original source rules are handled by CappedRecursiveQuotation, maintaining
the local binder-rank invariant from the empty initial state. Equality slots
are computed from independent original endpoint evidence and the proved
formation bound, with actual normal typed transport and literal erasure.
CappedFullQuotation and CappedApplicationQuotation thread numeric plans;
CappedProgramInterpreter packages the resulting programs and proves the same
plan-independent type-sort bound max(k+7,r+6).

CappedDependentInterpreter.quote_at accepts a caller-fixed k and independent
source data with pruned quotation budget <=k. every_bounded_original covers
every closed judgment in that fragment, with original typing, normal P/Q/I,
literal recovery and the common rank bound. The fragments cover every original
closed judgment. Literal type recovery, pruning/padding invariance, full open
coverage by annotated closure/reopening, and syntax injection across budgets
and derivations (including beta-conversion comparison) are retained.
Open-source rank statements use the budget of the annotated closure.

The uncapped public quoter and cost/extraction evidence remain unchanged.
No CPS formalization, source-rule change, axiom or admission. Plan-specific
signatures/fillings still select different interpreter TERMS. A single head
per whole fragment and the source-side bridge from normalization redex bounds
to quotation budgets remain open; do not infer either from this rank theorem.

Incremental aggregate and fresh aggregate compilation pass, with 2549 own
closed reports plus one unchanged upstream report; 1034 public Check/Print
pairs and 123 source/Dune manifest entries. Fresh directory:
/tmp/pts-rk-capped-audit.lpDpbN. Both recursive kernel checks and pristine
inventory comparison pass. Aggregate kernel checking ran
10:19:54--10:28:56 UTC, exit 0. All own endpoint reports are closed;
the loaded inventory contains only unchanged upstream functional extensionality,
with no unsafe/type-in-type/assumed-positivity entries. Original proof comparisons,
all 123 source/Dune stability checks and FINAL-CHECKS pass.
Full local CI passes 226/226 stages on retry after a Dune concurrency-lock
failure; no proof or CI driver was weakened. The updated 13-page note builds
without TeX layout/reference/glyph warnings in /tmp/pts-rk-self-note.KAJfjK,
with PDFKit extraction/render inspection and changed pages visually checked.
Raw logs: _build/self-interpreter-capped-quotation-2026-10-21.
The old successful /tmp/pts-rk-fragment-audit.umlOaP regenerable cache was
cleaned after checking its success records; raw prior evidence remains.
An attempted copy of its nonexistent `log` failed; no copied trace is claimed.
New module aliases were expanded into qualified references to avoid duplicating
large compiled environments. The first state build and first incremental audit
were intentionally interrupted (130) during this resource correction.

HEAD remains 1d1f2462b1d5dff9f94f8f1f3247f40d34769a90, index empty; this and
the previous fragment milestone are uncommitted. Preserve unrelated dirty
documentation/BZC/CI edits. Exact evidence:
verification/self-interpreter-capped-quotation-2026-10-21/COMMANDS.md.
First remaining goal: replace signature-specific application by one fixed
originally typed interface for varying capped environments (or generic coherence
schemes), retaining normal codes and literal recovery. Do not merely re-encode
the plan as a number or equate a common rank bound with a common term.
The normalization-redex/source-budget bridge remains independently open.
Next exact focused command, under the pinned environment:
opam exec -- dune build theories/self_interpreter/CappedDependentInterpreter.vo

## Fragment uniformity — capped ranks, varying signatures

The previous improvements were committed/pushed as
1d1f2462b1d5dff9f94f8f1f3247f40d34769a90, confirmed against origin/main.
The user's subsequent request concerns one interpreter per whole rank-bounded
fragment, with no CPS formalization.

Three new independent modules compile. FragmentUniformity proves an actual
LocalCodeAlignment.request has formation rank <=k+2 under its explicit local
profile bound, and builds a capped allocator preserving original typing,
normal signatures/fillings and arbitrary-layer declaration bounds. The actual
base signature has bound k+3. CappedInterpreter supplies executable lookup,
inherited realization, normal typed interpreters and rank_uniform: type-sort
indices <=max(k+7,r+6), independent of plan lengths and numerical budgets.
FiniteCoherenceCatalogue proves that even at formation rank 2 and literal
ceiling zero no finite literal catalogue covers every accepted field; its
telescope family has 2*h+11 nodes. Generic law schemes are not excluded.
Bounding conservativeRank instead yields a finite syntax vocabulary.

Full-source quotation into the new capped family is NOT yet proved, and the
interpreter syntax still varies with its signature. The published quoter and
its full dependent coverage/fidelity endpoints are unchanged. The local rank
invariant must be threaded through recursive quotation, then a fixed typed
interface for varying environments or reusable coherence laws constructed.
There is no general impossibility theorem for fragment-uniform PHOAS.
The k bound is the formation/literal quotation budget; identifying it with
the normalization redex bound d is a separate, unproved source-side bridge.

Fresh aggregate in /tmp/pts-rk-fragment-audit.umlOaP exits 0 with 2347 own
closed reports plus one upstream report. Both recursive kernel checks exit 0;
pristine inventories and original proof/Dune comparisons pass. The 115-entry
source manifest is stable; own assumptions are closed and the loaded inventory
has only unchanged upstream functional extensionality, with no unsafe entries.
Complete local CI exits 0, all 226 stages PASS. FINAL-CHECKS exits 0.
Incremental new-module checks exit 0.
The updated note compiles warning-free to 12 pages (final TeX build
/tmp/pts-rk-self-note.k3lPRz), with final PDF text/render inspection. Exact commands,
attempts and final results:
verification/self-interpreter-fragment-uniformity-2026-10-21/COMMANDS.md.
The continuation is uncommitted; the index is empty and unrelated edits remain.
First remaining implementation step: parameterize equality allocation so
RecursiveQuotation can use the capped family while preserving source recovery.
Next exact command for a focused check:
opam exec -- dune build theories/self_interpreter/CappedInterpreter.vo.

## Self-interpreter improvements — allocation, pruning and uniformity limits

The requested non-CPS continuation reconciles all six committed paper versions
in theories/self_interpreter/OBLIGATIONS.md. Full dependent coverage/recovery
obligations were already discharged; the independent elementary compiler,
numeric dependent reifier, canonical source elaborator, smaller coherence
interface and general rank-only family remain separate extensions.

SizedSyntaxEnumeration now directly generates exact node sizes, with complete
membership agreement and exact cardinality recurrence. Both equality allocators
prefilter original-typed carriers/operands and reject invalid telescope prefixes
before expansion; iff proofs preserve all reference-accepted fields. SourcePruning
removes literal-reflexivity conversion nodes and proves original judgment
preservation, idempotence, non-increasing size/repair count, and arbitrary padding
invariance. FullDependentInterpreter applies pruning before selecting its budget;
all original recovery, typing, normality and fidelity endpoints still compile.

QuotationCost proves actual plan length = 2*Pi + lambda + 2*application +
2*conversion, less than derivation size, after pruning at the final endpoint.
PlanNonuniformity gives nested identity applications at result rank 0, literal
ceiling 0 and redex bound 1 with actual length 3*h. Conversion detours for the
IDENTICAL judgment U0:U0 survive pruning and have actual length 7*h. These refute
rank-only/source-only bounds on the implemented quoter's plans, not every possible
rank-indexed interpreter or canonical elaborator. No CPS formalization was added.

All changed proof targets pass incremental compilation. Full unchanged local CI
exits 0, 226/226 stages PASS, including unrelated unpublished BZC stages. Fresh
aggregate in /tmp/pts-rk-self-improvements-audit.vjkEgS exits 0 with 2287 closed
self-interpreter reports plus one unchanged upstream normalization report.
Core and aggregate recursive kernel checks pass; pristine core inventories
match. All 112 source/Dune manifest entries remain stable. The original-source
comparison's initially overbroad Git pathspec was corrected; FINAL-CHECKS exits
0, including unchanged original core/normalization/ZFC proofs and Dune files.
Loaded kernel inventory has only unchanged upstream functional extensionality,
no unsafe/type-in-type/assumed-positivity entries; all own endpoints are closed.
Extracted actual sort quotation passes three normality checks; lambda/application
each timeout at 30 seconds (124), so practical non-leaf execution remains open.
Actual direct-enumeration counts 68/1209 at node bounds 5/7 pass. The paper builds
to 11 pages, warning-free; changed pages visually inspected. Exact attempts,
commands and raw-log paths: verification/self-interpreter-improvements-2026-10-21/COMMANDS.md.

The enclosing publication commit is based on published
f5fdac0c1deeeb43d6138f8de3178224b79d42a4 and contains this verified continuation,
its note/PDF and evidence. Publication was requested after verification.
Unrelated changes are preserved. One validated
completed Dune cache was cleaned to make space; raw audit logs/trace were retained.
First remaining implementation goal: avoid allocating a complete equality layer
when type-code alignment is already literal, retaining annotation normality and
literal recovery. Then pursue canonical computational source elaboration and a
small uniform coherence interface. CPS stays excluded by the user's instruction.
Next exact command after reviewing the ledger and pinned environment:
opam exec -- dune build theories/self_interpreter/RecursiveQuotation.vo.

## Self-interpreter exposition streamlined — final construction first

The research note now presents the completed interpreter directly: motivation,
original calculus and main theorem, finite dependent code interface, checked
equality repairs, faithful packaging/evaluator, structural quotation proof,
Brown--Palsberg comparison, CPS feasibility and a short formalization guide.
The source shrank from 17,474 to 3,929 whitespace-delimited words and the PDF
from 42 to 11 pages. Intermediate weak/shallow interpreters, standalone STLC
quotation, canonicalization detours, detailed auxiliary-law developments and
the module-by-module inventory were removed from the exposition. Their proof
sources and historical records remain intact.

Retained boundaries: original annotated typing/reduction, ordinary represented
type argument, numerical plans beyond ranks, literal term/type recovery,
syntax fidelity, open-context closure, limited fixed-head obstruction, and
the distinction between the proved interpreter and paper-level CPS analysis.
The explicit faithful evaluator was checked against FaithfulProgramDecoder;
the theorem and recursion summary were checked against FullDependentInterpreter
and RecursiveQuotation. No theorem contract or proof source changed.

Four fresh note builds exit 0. Final build /tmp/pts-rk-self-note.0KH9o2;
PDFKit extraction/rendering exits 0, 11 pages, visually reviewed. Final TeX
log has no overfull/underfull boxes, LaTeX warnings or missing glyphs.
Raw logs: _build/self-interpreter-exposition.aNUfvF. Exact commands, versions,
scope review and hashes: verification/self-interpreter-exposition-2026-10-21/COMMANDS.md.
No new Rocq/CI run is claimed for this editorial change.

The user requested commit and push. The enclosing publication commit is based
on 2da7627ede1e78fc7bdf1a3d48068b2acac1e07b and contains the note/PDF,
exposition evidence and only the new scoped handoff entries. Unrelated local
changes are preserved. Publish with git push origin main and confirm using
git ls-remote origin refs/heads/main.
The editorial request is complete. The next mathematical question remains
an internal dependent CPS handler with a realized contextual equality law;
rank-only uniformity also remains open. Next exact review command:
git diff -- PTS-rk_self_interpreter.tex.

## Brown--Palsberg comparison and CPS feasibility — discussion completed

The requested discussion is now Section 12 of the research note. It compares
the completed full-dependent numerical-plan family with POPL 2016 Sections
3, 5--8: strong recovery, annotation-sensitive fidelity, external quotation,
uniformity, deep folds, self-application and proof/experimental evidence.
The appropriate description is Brown--Palsberg-style indexed strong unquoter,
not their single fixed interpreter or full deep-operation suite. The existing
fixed-head rank obstruction remains applicable; it does not refute families.

CPS is assessed, not implemented. New paper-level calculations give exact
finite continuation ranks, a simply typed CBN translation and an example of
unbounded translated rank at source type rank 1. The current Tarski product
and identity-validated equality fields block the naive continuation instance.
A CBV example refutes beta-only preservation of unrestricted source conversion,
not all dependent CPS. Related positive papers do not instantiate unchanged
PTS-rk directly. External CPS plus re-quotation and a genuine internal fold
are distinct next projects. First substantive remaining CPS goal: construct
a typed continuation product/application handler and an actual contextual
equality instance, or establish a precisely scoped obstruction to that interface.
The general dependent CPS question and rank-only uniformity remain open.

Verification: three fresh note builds exit 0; final PDF has 42 pages. PDFKit
extraction/rendering exits 0; discussion pages 35--41 visually inspected.
Final LuaLaTeX log has no overfull boxes, LaTeX warnings or missing glyphs.
One pre-existing overflow in the endpoint summary was repaired by prose
reflow. No proof/Dune/core/NormalizationComplexity source changed; endpoint
hashes still match the published fresh audit. No new Rocq/CI run or CPS kernel
verification is claimed. Evidence and exact commands:
verification/self-interpreter-discussion-2026-10-21/COMMANDS.md.
Raw logs: _build/self-interpreter-discussion.GAMEGX;
final fresh TeX directory: /tmp/pts-rk-self-note.pVKShq.

HEAD is the already published ade6387531ac460c791e375419ef5724154d2ea0.
The user subsequently requested commit and push. The enclosing publication
commit contains this discussion/PDF, the development README, its inspection
script/evidence and only the new scoped entries in shared handoff documents.
Unrelated existing worktree changes are preserved. Publication uses ordinary
git push origin main; confirm with git ls-remote origin refs/heads/main.

## Full dependent PHOAS publication — scoped snapshot

The user requested commit and push. The enclosing publication commit contains
the full self-interpreter sources, Audit/Dune registration, research note and
37-page PDF, curated verification records for the seven dependent-development
milestones, and self-interpreter portions of shared documentation. The parent
is e822cd62df393faf4d5e4ed0c4c8fed173ccba6f; publication targets origin/main.
Unrelated BZC, paper-editing, tool/CI changes and bulky local logs remain local.
Shared documentation is staged selectively; its remaining worktree changes
belong to the excluded work and are preserved.

The published proof sources and Dune file are byte-identical to the successful
fresh audit:2229closed self-interpreter reports, recursive kernel/pristine
checks and original-source comparisons all pass. The retained226-stage CI
run covers the shared workspace, including54unpublished BZC stages; those
script changes and BZC sources are outside this publication. Original published
CI already includes the self-interpreter audit. No proof changed for publication.
Source/PDF hashes match the final note-04 record. git diff --check passes.
The complete numerical-plan result has no remaining proof obligation;
rank-only uniformity remains the next research question. Next exact review
command: git log -1 --oneline. Remote confirmation is obtained with
git ls-remote origin refs/heads/main after the ordinary push.

## Full dependent numerical-plan interpreter — completed and verified

The positive full-source endpoint is constructed and independently verified.
FullDependentInterpreter attempt02
exits0 with14 own closed reports. every_closed_original covers every ORIGINAL
closed typing judgment using ranks plus a finite purely numeric allocation
plan, ordinary type/term arguments, original typings, full normality and
literal unreduced-source recovery. closed_type_recovers covers the represented
type. every_original closes/reopens literal annotated open inputs in originally
well-formed contexts. Syntax/conversion injectivity is independent of derivation
and signature choices, at fixed source scope for open terms. It is NOT a
rank-only fragment-uniform family, a single all-rank head, or an efficient
enumerator. No semantic source value is precomputed by the interpreter.

RecursiveQuotation implements all six source rules and passes scoped recursive
kernel0. ApplicationQuotation uses exactly two actual checked layers; conversion
uses independently recovered endpoints. FullDependentInterpreter has independent
paper/rank/audit reviews PASS. All proof sources, Dune and Audit are frozen for
final checks. Audit contains885 Check/Print pairs;107 proof modules contain
2229 Print statements in total. LayerCodeAlignment's final alias-only cleanup
also passes18closed and kernel0. The actual extracted OCaml closed U0 quotation
path returns four true checks (empty plan, normal term, normal type program,
normal faithful program),0.37s under60s cap. Opaque-body warnings retained;
no direct vm_compute or general application performance claim.

Full CI:226/226PASS, exit0, raw evidence
_build/self-interpreter-open-telescope-final-review.d0SH8N. The independent
fresh aggregate retry also exits0 with2230closed reports:2229self-interpreter
(885Audit+1344module) plus unchanged upstream Ranks.strong_normalization.
Retry build /tmp/pts-rk-self-open-telescope-audit-retry.cdzdRH; raw evidence
_build/self-interpreter-open-telescope-final-review-retry.mfFz4Q. All14 final
audit stages and FINAL-CHECKS exit0; the audit completed at06:55:34UTC.
Recursive Audit/core kernel checks pass; the loaded inventory has only
unchanged upstream functional extensionality and no unsafe/type-in-type/
assumed-positivity entries. All self-interpreter endpoint assumptions are
closed. New pristine723cf2 build and kernel check pass, with core inventory
byte-identical to both new and retained pristine. Frozen original core,
NormalizationComplexity and PR#1 ZFC comparisons pass. All110 manifest
entries are hash-stable; initial and retry manifests agree. Pristine path
/tmp/pts-rk-self-open-telescope-pristine.oGwrNN. Exact commands/results are in
verification/self-interpreter-open-telescope-2026-10-21/final-review/COMMANDS.md.

First fresh audit /tmp/pts-rk-self-open-telescope-audit.DTgliS failed with
No space left on device (Dune trace writing), not a proof rejection. Its raw
failure is preserved. Completed scoped caches nr1PlD and QR0a4s were validated
inactive and cleaned with Dune (cache-clean8/9, both0), recovering about900MiB;
the inactive failed audit cache was also cleaned. Sources/raw logs remain.
The successful retry used a new empty directory. Note-04 and PDFKit inspection
both exit0:37pages, /tmp/pts-rk-self-note.PfjEfO; pages1,31,32,37 visually PASS.
The note and self README now distinguish earlier module limitations from the
completed all-source theorem and the remaining rank-only uniformity question.

First remaining research goal beyond the constructed full-source family:
determine whether a single rank-only index can cover an entire rank-bounded
fragment, removing per-derivation plan growth. Practical equality-layer
enumeration and extracted execution beyond leaf regressions are separate
engineering questions, not assumptions of the source-coverage theorem.

HEAD remains e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. No Git/index mutation,
commit, push or merge; index is empty. This milestone and preceding local
self-interpreter developments remain uncommitted alongside preserved unrelated
user changes. git diff --check exits0. The older entries below are provenance,
not current claims that source coverage remains open. No required proof or
verification remains for the numerical-plan result. Next exact safe review
command: git diff --check. Any new fresh build should first check disk space
(about652MiB free at final audit); do not delete active or unrelated caches.

## Active continuation: full dependent PHOAS interpreter or a genuine no-go

The user requests persistence to that terminal outcome. Neither outcome is
established yet; this is an in-progress checkpoint, not a completion claim.
Do not infer general impossibility from the existing restricted obstructions.

OpenTelescopeRecovery now handles arbitrary open bodies and LITERAL lambda
closures. It provides executable inverse scope renamings, original typing
transport in both directions across the realized telescope, and independently
types concrete closure arguments. Its scoped fresh build and recursive kernel
check pass (23 closed reports); evidence is in
verification/self-interpreter-open-telescope-2026-10-21/open-recovery/COMMANDS.md.
ContextualTelescopeRun compiles (attempt08,12 closed): actual telescope
applications, original typing, literal beta recovery, substitution/renaming,
normality, and argument congruence. Raw logs: _build/telescope-run.rwugef;
fresh build: /tmp/pts-rk-telescope-run.QR0a4s.

ConcreteContextualBeta is frozen at attempt13 (20 closed): actual finite-field
application to independently typed concrete open A,B,f,u; literal filled
identity recovery; full guarded normality and syntax/conversion injectivity
of all four payloads at fixed W/q. SourceValidity is frozen (15 closed),
TelescopeEquality (15 closed), ContextualTransportLaw (23 closed),
NormalNeutralSubstitution (10 closed), QuotationTree (11 closed),
BoundedSyntaxEnumeration (12 closed), ContextualEqualityRealizer (12 closed),
and ContextualEqualityExtension (17 closed). Scoped evidence is under the
same open-telescope verification directory; each owner records exact kernel
status. Root RealizedEquality compiles with eight closed reports.
OriginalTypecheck is frozen at typecheck-07 with eight closed reports:
executable inference/sort extraction/checking is sound AND complete for the
unchanged original typing judgment in valid contexts. Root's four-module
combined scoped recursive check exits0 in _build/telescope-run.rwugef/kernel-01.log.
CodeAlignment (11 closed), CheckedEqualityFields (24 closed),
CheckedContextualFields (31 closed), QuotationCache (13 closed),
QuotationViewRenaming (9 closed), and QuotationViewSubstitution (7 closed)
now compile. Owners record their exact scoped kernel results separately.
TelescopeInstantiation (5 closed) and DependentProgramDecoder (26 closed)
are frozen with an independent full-source review and recursive kernel0:
_build/telescope-run.rwugef/program-decoder-kernel-01.log. The latter supplies
actual ordinary P/Q arguments, direct original typing, exact formation rank,
normality and literal closure recovery, but NOT source-quotation coverage.
FaithfulProgramDecoder now supplies normal syntax-faithful packaging of the
ACTUAL PHOAS program: its interpreter projects and RUNS that program, not a
precomputed source value. Its scoped build has 12 closed reports and recursive
kernel0, with independent review. SourceQuotationBudget computes an executable
budget covering every recursive premise, including large literal sort labels;
10 closed reports, recursive kernel0 and three independent reviews.
GlobalEqualityInsertion, CheckedEqualityLayers, QuotationJudgment,
LocalQuotationSpine, LayerCodeAlignment and NormalEqualityFill now have scoped
successful builds/kernel checks. Their owners record exact hashes/status in
the phase directory. FullQuotation's alias-free execution infrastructure
compiles, but its six-case recursive quotation is still being implemented.
LocalSpineNaturality's complete same-profile presentation/body/unbody adapter
compiles (attempt10,6 closed) and passes recursive kernel0 plus independent
review. ClosedQuotationPackage is frozen (16 closed/kernel0, two reviews),
LocalInitialState is frozen (12 closed/kernel0). FullQuotation infrastructure
is frozen at attempt10,16closed: typed Pi/Lam constructors, source-bound
proofs, state sequencing and literal-code-preserving reframing. The active
files are RecursiveQuotation (six-case source recursion), ApplicationQuotation
(two checked-layer repairs), LocalCodeAlignment (local adapter), and root
IndexedProgramInterpreter (uniform numeric-plan family).
Latest milestone: RecursiveQuotation attempt02 compiles the COMPLETE
structural six-case quote_derivation with four closed reports; no target
quotation/coherence premise. ApplicationQuotation is frozen at attempt05,
nine closed reports, exactly two real numeric layers. LocalCodeAlignment
is frozen at attempt13, seven closed reports. Their scoped recursive checks
are running. IndexedProgramInterpreter is frozen (13 closed), SourceClosure
is frozen (five closed), and their combined recursive check with refreshed
LocalSpineNaturality exits0. Root FullDependentInterpreter.v is the final
closed/open original-source coverage assembly, now being compiled.
Do not claim completion until that assembly, fresh aggregate and full CI pass.
New modules are registered in Dune but NOT YET added to aggregate
Audit. No new aggregate audit or complete CI yet. The note/PDF were updated
and compiled successfully through note-02 (/tmp/pts-rk-self-note.OSFq1g,
36pages), including faithful actual-program packaging, source budgets and
literal local scopes. PDFKit extraction/render exits0; pages1,30–31 reviewed
visually and pass. Full coverage is still explicitly open in the note.

Practical build finding: redundant exported module aliases cause severe
environment duplication (QuotationJudgment.vo184MiB, LocalQuotationSpine.vo85MiB).
FullQuotation's initial mechanically expanded tranche compiled to21KiB. Owners
have completed alias-only cleanup in QJ/QVS/LS/NF; scoped sources/evidence
have new hashes, and rebuilds have17/7/26/6 closed reports. LS/NF also pass
the refreshed recursive kernel. Do not attribute old hashes to rewritten
sources. Seven exact completed Dune caches were cleaned
after confirming their logs were retained; only regenerable cache data removed.
Disk headroom is limited; reuse each owner's current cache, never delete active
ones. Raw cleanup logs: _build/telescope-run.rwugef/cache-clean-1 through7.

The immediate task is six-case original source quotation using the now
constructed typed finite views and their structural substitution, plus
integration of actual global allocation with independently enumerated numeric
layers. A cache's literal Pi constructor view is kept apart
from its possibly coerced root code; independently typed realized equality
aligns those codes without changing the filled payload. The candidate now
uses syntax/literal/layer budgets, not a claimed rank-only universal fragment.
See the newest DECISIONS entry. Full recursive coverage and its actual numeric
allocation remain to prove; the generic closed dependent P/Q interface and
faithful-envelope injectivity are now constructed.
No target quoter or semantic lookup table may be
assumed. Original calculus and prior injectivity remain unchanged.

HEAD remains e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. No Git/index mutation,
commit, push or merge in this continuation. Existing unrelated changes and
historical verification logs are preserved. Next local command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-telescope-run.QR0a4s --display=short --no-buffer theories/self_interpreter/LocalSpineNaturality.vo
```

## Contextual beta families and uniform finite telescope signature

The requested three components are constructed in eleven new modules:
original contextual cast-beta formation under arbitrary dependent telescopes;
independently typed identity realizations; and full annotation normality with
a finite syntax-free length/rank-vector interface. ContextualTelescope retains
literal annotations and independent original formation. ContextualBeta compares
complete multi-lambda endpoints. TelescopeBetaFamily binds A,B,f,u and its
plain-annotation identity witness reduces after four applications to literal
reflexivity. Only the witness TYPE is converted, never subject expansion.

UniformTelescope binds Xi : Pi previous_domains.U_ri and uses neutral Xi
spines as its generated domains. Formation/normality and replacement
naturality are proved. UniformTelescopeRecovery.realize computes actual
lambda-closed declaration values from every originally formed concrete W,
proving original TypedSub and annotation-wise beta recovery. Its exact final
closure theorem ends in U_s; arbitrary open-body/lambda-closure transport
is still a separate obligation, not hidden in the premises.

UniformContextualBeta has an independently typed CLOSED NORMAL identity
program for every rs,a,b,d. TelescopeBetaSignature adds exactly
(sum j=0..L (k+1)^j)*(k+1)^3 such fields over the unchanged local-beta
signature, with executable lookup, computed descriptor budgets, original
wf/normality, actual identity TypedSub and closed package/run contracts.
Each added declaration's proved rank is <=k+3. ContextualBudgets proves
that rank1 permits arbitrarily long zero-rank vectors: length is a separate
finite-interface index. ContextualBetaFamily/Signature retain the explicit
one-binder specialization, literal five-argument recovery and local input
syntax/conversion injectivity. RealizedSignature separately packages actual
independently typed closed finite realizations. No full quoter is assumed.

All eleven modules compile, with 187 new closed module reports, independent
mathematical reviews and scoped recursive checks. Fresh aggregate build
/tmp/pts-rk-self-contextual-beta-audit.tzMxfv exits 0 with 1140 closed reports;
340 aggregate Check/Print pairs are registered. Original core and aggregate
recursive kernel checks exit 0; the original inventory matches pristine
upstream. The loaded inventory retains only unchanged upstream dependent
functional extensionality, with no unsafe features. Frozen original kernel,
NormalizationComplexity and PR #1 ZFC comparisons pass; all 68 proof/Dune
manifest entries stayed byte-identical. Complete local CI/actionlint passes
226/226 stages, including fresh pristine upstream. No final-audit failure or
timeout. Audit ran 03:30:55–03:37:31 UTC; CI 03:30:56–03:33:13 UTC.
Raw final audit:
_build/self-interpreter-contextual-beta-final-review.nNuNVo.

Note/PDF updated and compiled successfully: 33 pages, 353260 bytes, final
build /tmp/pts-rk-self-note.dWRjMd. No overfull boxes, missing glyphs or
undefined references; five mild underfull boxes. All-page text extracted;
pages1,26–33 visually checked. README and TeX independently reviewed.
Exact commands, all intermediate failures and hashes:
verification/self-interpreter-contextual-beta-2026-10-21/COMMANDS.md.

Disk-full interrupted two development builds. Only three exact old temporary
Dune caches were removed to resume; source, PDF and verification logs were
preserved. They can be regenerated. Prior raw evidence remains available;
the historical cache paths are not live verification promises.
HEAD remains e822cd62df393faf4d5e4ed0c4c8fed173ccba6f; no commit/push/merge
or Git/index mutation. This and five preceding local Tarski milestones remain
uncommitted. Unrelated workspace changes are preserved.

First remaining goal: extend UniformTelescopeRecovery from annotation-wise
and U_s-ending closure recovery to arbitrary OPEN bodies and lambda closures,
then construct typed applications of the finite uniform contextual beta fields
to concrete dependent telescopes and payloads. Retain literal annotations,
normality guards and original typing. Compose that with executable full-source
derivations and conversion joins to generate internal substitution/reduction
coherence, then compatible context/type/term translation, global quotation
normality, strong recovery, source fidelity and full original coverage.
Neither general function extensionality, neutral cast cancellation, eta,
cumulativity nor the desired quoter may be assumed. Existing raw-HOAS/STLC
injectivity is unchanged; full dependent PHOAS remains open, not ruled out.
Next exact fresh check after that proof continuation:

```sh
next_build=$(mktemp -d /tmp/pts-rk-self-next.XXXXXX)
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir="$next_build" --display=short --no-buffer @theories/self_interpreter/audit
```

## Internal dependent equality and executable source substitution verified

Five new modules extend the full-PTS PHOAS infrastructure without changing the
original calculus. IndexedEqualityLevels constructs equality lowering/reversal
from predicate level max(a+2,d+1) to d, joins forward witnesses, and specializes
type-law reversal at U_c from c+2 to c+1. Direct original typing, replacement,
reflexivity computation and guarded normality are checked; this is neither
cumulativity nor same-level symmetry.

DependentEquality constructs synchronized graph equality of indices and fiber
values, at sort max(a+2,b+2,d+1). Dependent congruence consumes equality at the
SAME predicate level d. Fixed-fiber embedding, original typing, substitution
and literal reflexivity computation are checked. This does not identify its
evidence with equality after an independently prescribed transport.
TarskiGraphBeta connects that embedding to the ACTUAL finite beta-law field.
Constructive identity filling yields graph reflexivity at the literal replaced
decoded domain and lambda fiber; no eta or subject expansion is used. No
normality is claimed for the lambda-family graph certificate.

BinderCongruence lifts an OUTER equality through a common map whose body can
depend on both its parameter and the bound variable, with binder domain and
codomain independent of the outer parameter. Its actual product-code
specialization has original typing and literal reflexivity recovery. It is
not an arbitrary pointwise-to-function equality rule, and administrative beta
redexes remain. SourceSubstitution transparently replaces/renames supplied
FullSource derivations and constructs derivations of literal beta contracta.
Type-valued variable evidence has Prop-valued inhabitation iff original
TypedSub. No Prop-to-Type extraction, new well-formedness restriction or
target substitution-coherence assumption is introduced.

Fresh aggregate /tmp/pts-rk-self-coherence-audit.mM2Zir exits 0: 895 closed
reports (66 new module reports plus 29 new aggregate reports; 282 aggregate
endpoints total). Recursive core/aggregate kernel, pristine core inventory,
frozen ZFC/core/NormalizationComplexity and all 57 proof/Dune hash-stability
checks pass. The loaded inventory retains only unchanged upstream
extensionality; all new theorem reports are closed, with no unsafe features.
Full local CI/actionlint passes 226/226 stages, including pristine upstream.
Independent mathematical and final prose reviews pass. Raw audit/CI:
_build/self-interpreter-coherence-final-review.qs3wIG.

Updated note/PDF: 31 pages, 342548 bytes; build exit 0 in
/tmp/pts-rk-self-note.IN9im0. No overfull boxes, missing glyphs or undefined
references; five mild underfull boxes. All-page text extracted; pages
1,22–27,31 visually inspected. Exact commands, intermediate compiler failures,
versions, hashes and contract boundaries:
verification/self-interpreter-coherence-2026-10-21/COMMANDS.md.

HEAD remains e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. No commit/push/merge
or index mutation; staged diff empty. This and four preceding local Tarski
milestones remain uncommitted. Unrelated workspace changes are preserved.

First remaining goal: construct INTERNAL source-reduction coherence under
dependent binders beyond the restricted common-map construction. A prospective
generator is the specific cast-beta law under an entire dependent telescope,
whose identity endpoints should reduce to one literal multi-lambda. This is
NOT proved: original formation, annotation normality, contextual closure and
sufficient telescope-length/rank-vector budgets remain to establish. Rank
alone is not yet shown to bound those indices. Then construct mutually
compatible translated contexts/families/types/terms, quotation-substitution
coherence, global normality, strong literal recovery, source fidelity and
full original coverage. SourceSubstitution is computational source evidence,
not that target coherence. Do not assume funext, neutral cast cancellation,
eta, cumulativity or the desired quoter. Existing raw-HOAS/STLC injectivity is
unchanged; full dependent PHOAS remains open, not ruled out. Next exact command:

```sh
next_build=$(mktemp -d /tmp/pts-rk-self-next.XXXXXX)
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir="$next_build" --display=short --no-buffer @theories/self_interpreter/audit
```

## Full source conversion certificates and finite beta interface verified

Six new modules advance the dependent PHOAS infrastructure. ScopedTarski
extends smart binder/Abs/App and sort/code views to arbitrary dependent scopes,
with exact renaming/weakening, original typing, normality and local fidelity.
Concrete spines compute each child environment and lifted identity fill;
nested_binder_typed connects these operations at arbitrary depth. Recovery
retains literal substituted annotations; a separate corollary contracts the
identity decoder. This is not yet recursive source quotation.

FullSource supplies Type-valued exact original typing/conversion/step data,
with propositional inhabitation iff the original relations and computed
finite literal/explicit-rule ceilings. Original typing coverage includes
arbitrary contexts; no Prop-to-Type extraction or target-property premise.
FullConversion computes forward normalization traces and structural endpoint
comparison. On original wf/typed inputs it decides conversion, returns a
normal join and preserves original typing at EVERY forward stage. Success
is sound even on raw syntax; untyped completeness is not claimed.
CanonicalSource transparently transforms supplied derivations in wf contexts,
replacing arbitrary zigzags by those joins while preserving every original
term/type/context/annotation literally. Output certification and full original
wf coverage are proved. These are metalevel certificates, not internal
equality witnesses or a full target quoter.

TarskiBeta forms the actual four-argument beta-evidence type, rank
max(c+1,max(b+2,d+1)) for c=max(a+1,b), and independently constructs its
closed normal identity inhabitant. TarskiBetaSignature adds (k+1)^3 fields
to the unchanged TS signature, with actual wf/normal context, bounded lookup
typing, constructive identity TypedSub and literal reflexivity recovery.
Its inherited typed environment supports ScopedTarski typing/normality;
concrete-spine recovery is not automatically instantiated by that bridge.
The additional field is not derived from arbitrary old product-law evidence.
Neutral casts still do not beta-cancel, and dependent binder congruence is open.

Fresh aggregate /tmp/pts-rk-self-conversion-audit.SRZ7pU exits 0: 800 closed
reports (107 new module reports plus 47 new aggregate endpoints; 253 aggregate
endpoints total). Recursive core/aggregate kernel, pristine core inventory,
frozen ZFC/core/NormalizationComplexity and all 52 proof/Dune hash-stability
checks pass. All new theorem reports are closed; the loaded inventory retains
only unchanged upstream extensionality, with no unsafe features. Full local
CI/actionlint passes 226/226 stages, including pristine upstream. Independent
mathematical and prose reviews pass. Raw audit/CI:
_build/self-interpreter-conversion-final-review.1Axp2t.

Updated note/PDF: 28 pages, 330639 bytes, final build exit 0 in
/tmp/pts-rk-self-note.nyJwvf. No overfull boxes, missing glyphs or undefined
references; four pre-existing mild underfull boxes. All-page text extracted;
final pages 1,21–24,28 visually inspected (earlier build also 20,25).
Exact commands, all intermediate failures, versions, source/PDF hashes and
contract boundaries: verification/self-interpreter-conversion-2026-10-21/COMMANDS.md.

HEAD remains e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. No commit/push/merge
or index mutation; staged diff empty. This and three preceding local Tarski
milestones remain uncommitted. Unrelated workspace changes are preserved.

First remaining goal: construct compatible represented families/terms/types
from CanonicalSource data, using arbitrary-scope smart operations; generate
INTERNAL substitution/reduction coherence along the typed forward traces,
especially under dependent binders. The finite beta fields solve a local
law, not that induction. Then prove full normality, strong recovery, faithful
source syntax and coverage with a sufficient target rank/literal budget.
Do not assume pointwise-to-function equality, cast cancellation, eta,
cumulativity or a target-quotation premise. Existing raw-HOAS/STLC injectivity
is retained; full dependent PHOAS remains open, not ruled out.
Next exact fresh verification command:

```sh
next_build=$(mktemp -d /tmp/pts-rk-self-next.XXXXXX)
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir="$next_build" --display=short --no-buffer @theories/self_interpreter/audit
```

## Sort quotations and normal local dependent binders verified

Four new modules extend the finite original Tarski interface. TarskiSorts
constructs normal closed quotes of U_r:U0 using universe law ZERO, with direct
identity-application typing and literal U_r recovery. TarskiContext constructs
arbitrary independently sorted dependent extensions, their actual identity
contexts/TypedSub and fresh-variable preservation. Its inherited fields and
generic operations accept arbitrary terms in the new scope and retain original
typing and literal identity recovery. Instantiated-context normality is not
asserted.

TarskiBinders contracts only the administrative application of a lambda family
to the freshly bound variable. Exact renaming and one-way substitution reduction
are proved. Smart decoded annotations are normal from normal A/B; local Abs/App
now need no separate decoded-annotation normality premise. Actual dependent
lambda-family binder introduction, normality, recovery and fixed-index local
input/conversion injectivity are checked. Its recovery target retains the
literal substituted decoded domain annotation. These smart operations use the
fixed signature plus one fresh binder for their bodies; arbitrary-spine smart
operations and recursive source quotation have NOT yet been composed.

TarskiRoundtrip proves that existing neutral casts do not beta-cancel, in an
actual wf original context for every external c, including at dependent K-indexed
types. The compared terms/types are normal, typed and distinct. Actual reflexivity
specialization still recovers the input. This is a precise limitation of those
neutral casts, not a PHOAS impossibility theorem or absence of internal equality.

Fresh aggregate /tmp/pts-rk-self-binders-audit.xrjN04 exits 0: 646 closed reports
(80 new module +39 new aggregate reports; 206 aggregate endpoints total).
Recursive core/aggregate kernel checks, pristine core inventory comparison and
frozen ZFC/core/NormalizationComplexity comparisons pass. All 46 proof/Dune files
are hash-stable; unsafe inventories are empty. The loaded inventory has only
unchanged upstream extensionality, while all new theorem reports are closed.
Full local CI/actionlint pass, 226/226 stages including a fresh upstream build.
Independent mathematical and final prose reviews pass. Raw audit/CI evidence:
_build/self-interpreter-binders-final-review.r6pl8m.

Updated note/PDF: 26 pages, 322023 bytes; build exit 0 in
/tmp/pts-rk-self-note.pGxQyu. No overfull boxes, missing glyphs or undefined
references; four mild underfull boxes retained. All-page text extracted;
pages 19–23 and 26 visually checked, including new formulas and boundaries.
Exact commands, all intermediate compiler failures, versions, hashes and
contract limits: verification/self-interpreter-binders-2026-10-20/COMMANDS.md.

HEAD remains e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. No commit/push/merge
or index mutation; no staged diff. This continuation and the preceding two
local Tarski milestones remain uncommitted. Unrelated work is preserved.

First remaining goal: combine the smart binder with arbitrary dependent
signature environments, then define independent FULL original source derivation
data and recursive quotation with compatible represented families, terms and
types. Generate internal source-substitution/conversion witnesses, especially
under binders; prove global normality, strong source recovery, faithful source
syntax and coverage. Do not assume neutral cast cancellation, function
extensionality, literal smart-substitution naturality or the desired quoter.
Existing raw-HOAS/STLC fidelity is unchanged. Next exact verification command:

```sh
next_build=$(mktemp -d /tmp/pts-rk-self-next.XXXXXX)
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir="$next_build" --display=short --no-buffer @theories/self_interpreter/audit
```

## Finite dependent Tarski signature and applied operations verified

The local Tarski operations now have an ACTUAL finite normal original
context and concrete identity TypedSub. New TarskiLawFamily binds A and B
in one product-law field per pair, sort c+2 for c=max(a+1,b), with a closed
normal identity inhabitant and literal beta specialization. TarskiPalette
builds four layers (carriers, decoders, universe codes, universe laws) for
r<=k+1. TarskiSignature adds product and law fields for a,b<=k, exactly
4(k+2)+2(k+1)^2 declarations. Original wf, all six field typings, normal
declarations, constructive fill and exact field equations are checked.
Telescope closure preserves original typing, normality and syntax; identity
application is directly typed and reduces to the actual substituted body.

TarskiOperations derives law evidence by applying the finite field, with no
extra local-law premise. Product/Abs/App typings and actual-fill recovery
to literal product, law, replaced f and replaced f applied to replaced u are
proved. Cast normality explicitly requires normal decoded annotations.
IndexedCoherence constructs homogeneous composition and nondependent map
congruence at the same predicate rank, with substitution/reflexivity laws;
arbitrary-evidence identity equations are applied-only, without eta.

Fresh aggregate /tmp/pts-rk-self-signature-audit.qlUK8l exits 0 with 527
closed reports (68 new module reports +41 new aggregate endpoints; 167
aggregate endpoints total). Recursive core/aggregate kernel checks, pristine
core inventory and frozen ZFC/core/NormalizationComplexity comparisons pass.
All 42 proof/Dune files are hash-stable. Full local CI and actionlint pass,
226/226 stages including a fresh upstream build. Only unchanged upstream
extensionality is in the loaded-library inventory; all new reports are
closed and unsafe inventories empty. Independent math/API/prose reviews pass.
Raw evidence: _build/self-interpreter-signature-final-review.rFr76B.

Updated note/PDF: 24 pages, 296163 bytes, build exit 0 in
/tmp/pts-rk-self-note.QLXAnK. No overfull boxes, missing glyphs or unresolved
references; five mild underfull boxes retained. All-page text extracted;
table/theorem/equations/boundary/closing pages visually checked. An earlier
successful build rendered an unsupported pipe table literally; the final
source uses a correctly rendered mathematical array. Exact commands, all
attempts/failures, hashes, versions and theorem boundaries:
verification/self-interpreter-signature-2026-10-20/COMMANDS.md.

HEAD remains e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. No commit, push,
merge or index mutation in this continuation; no staged diff. Both local
Tarski milestones remain uncommitted, with unrelated work preserved.

First remaining goal: derivation-directed FULL dependent quotation over the
finite interface, including represented families and generated internal
substitution/conversion coherence under binders. Prove full annotation
normality, identity recovery, faithful source syntax and coverage. Generic
closure of an independently typed body does not construct that body. The
budget covers a,b<=k with carriers through k+1, not closure at every available
carrier rank; literal labels need a sufficient external ceiling as well.
Neutral casts do not definitionally cancel and pointwise family witnesses
are not object-function equality. Full dependent PHOAS remains open, not
ruled out. Existing raw-HOAS/STLC injectivity is unchanged. Next exact check:

```sh
next_build=$(mktemp -d /tmp/pts-rk-self-next.XXXXXX)
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir="$next_build" --display=short --no-buffer @theories/self_interpreter/audit
```

## Object-language Tarski codes and dependent casts verified

Seven new self-interpreter modules now construct actual original PTS terms:
IndexedEquality, TarskiProducts, TarskiUniverses, TarskiCasts, TarskiIdentity,
ClosedTarskiCasts and EtaBoundary. Rank-indexed Leibniz equality supports
both cast directions using arrow motives at predicate rank c+1, with law
rank c+2. The genuinely dependent product-code interface has sort a+2 and
decoded product sort c=max(a+1,b). Universe laws have sort 2 and actual
identity witnesses for every external rank. Closed casts and their types
are normal, with exact program-type rank c+3. Direct original typing and
actual beta recovery are proved: identity-specialized Abs/App return literal
f/f u, without eta, subject expansion or precomputed semantic payloads.

Fresh aggregate /tmp/pts-rk-self-tarski-audit.OveK1T exits 0 with 418 closed
reports (63 new module reports and 29 new aggregate endpoints). Recursive
original/aggregate kernel, byte-identical pristine core inventory and frozen
ZFC/core/NormalizationComplexity source comparisons pass. All 37 proof/Dune
files remain hash-stable. All 226 full local CI stages and actionlint pass,
including a fresh upstream build. New public theorem reports are closed;
the loaded-library inventory has only the unchanged upstream extensionality
declaration and no unsafe checks. Independent API/math/prose reviews pass.

Updated note/PDF: 22 pages, 284951 bytes, build exit 0 in
/tmp/pts-rk-self-note.dAmCLX. No overfull boxes, missing glyphs or unresolved
references; four mild underfull boxes retained. All-page PDF text extracted;
new equations/theorem/boundary and closing pages visually inspected. Exact
commands, tool versions, hashes, every compiler failure and review:
verification/self-interpreter-tarski-2026-10-20/COMMANDS.md.
Raw audit/CI: _build/self-interpreter-tarski-final-review.VnAQed.

Publication e822cd62df393faf4d5e4ed0c4c8fed173ccba6f is now confirmed on
origin/main and local main; the former Keychain pause is resolved. This new
Tarski continuation is uncommitted, with an empty index. No unrelated work
was committed or rewritten. Historical pending-publication entries below
are superseded by the confirmed remote hash.

First remaining goal: close these local operations over a finite dependent
rank palette and generate internal conversion/substitution coherence from
independent original typing derivations. Prove identity computation and full
annotated quotation normality. Local neutral-cast normality does not supply
that induction; generic casts do not definitionally cancel, and pointwise
family equality is not host-function equality. EtaBoundary proves this
beta-only distinction, not impossibility of full dependent PHOAS. Existing
raw HOAS injectivity and the finite STLC strong decoder are unchanged.
No full dependent PHOAS interpreter is claimed. Next exact fresh check:

```sh
next_build=$(mktemp -d /tmp/pts-rk-self-next.XXXXXX)
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir="$next_build" --display=short --no-buffer @theories/self_interpreter/audit
```

## Publication confirmed; object-language PHOAS transport work resumed

User requested continuation after the Keychain pause. Pending push session
20431 completed with exit 0; git ls-remote origin refs/heads/main independently
confirms e822cd62df393faf4d5e4ed0c4c8fed173ccba6f, equal to local main.
No further commit/push is implied by this continuation. Unrelated work remains
preserved. Source implementation now proceeds in separate self-interpreter
modules: IndexedEquality, TarskiProducts, TarskiCasts and a limited EtaBoundary
regression. Construct actual object terms and identity witnesses first;
global quotation/transport coherence remains an obligation, not a premise.

## Canonical milestone committed; push awaiting macOS Keychain

At the user's new commit/push-then-develop request, scoped commit
e822cd62df393faf4d5e4ed0c4c8fed173ccba6f contains the four canonical modules,
Audit/Dune/README, note/PDF, concise evidence and scoped shared handoff entries.
Root main and the isolated publication branch both point to that commit;
index is empty. No unrelated BZC/source/log changes were committed. Root
branch/index synchronization used compare-and-swap and read-tree WITHOUT -u;
all 3588 pre-existing files passed byte-preservation checks. Backup/index,
manifest and results: /tmp/pts-rk-canonical-publish.ByVRjo.

Fresh isolated audit /tmp/pts-rk-canonical-publish-build.80zkDC exits 0 with
326 closed reports. Recursive original/aggregate kernel, pristine inventory,
frozen ZFC/core/normalization and source-stability checks all pass. The actual
PDF has been regenerated externally: 20 pages, 274101 bytes, SHA-256
861d0d4b7e28d0afd216b73412c925c5bb155ad857814cd4ac72d0e8d6a08719.
Source hash is unchanged; actual PDF text and theorem page were inspected.
Details: verification/self-interpreter-canonical-publish-2026-10-20/COMMANDS.md.

Ordinary git push origin HEAD:main in the isolated worktree has not returned.
It is waiting in the configured git-credential-osxkeychain helper. Last
read-only ls-remote still reports b6c81d1c24404835f5665b8bf4c263379dee5202.
The push is running in exec session 20431 (git PID 24562, helper PID 24573;
recheck process identity before any process action). No push exit code exists
yet, and no push success is claimed. The Air ask-user tool failed with
Transport closed; a normal user-facing Keychain-approval request was sent.
Do not extract credentials or bypass the helper. User can approve Keychain
or push local main through Air. Next exact command: git ls-remote origin
refs/heads/main, then resume/check the pending session before retrying a push.

To honor the requested ordering, no new proof source was edited before push
completion. Parallel READ-ONLY research selected a concrete next construction:
rank-indexed Tarski code carriers C_a:U0 and El_a:C_a->U_a, universe codes,
and product-code constructors with actual internally encoded transport laws.
Identity specialization C_a=U_a, El_a=id and p_ab=lambda A B.Pi x:A.B x
has original typing and genuine beta equations; no eta rule is needed locally.
Next modules: IndexedEquality (actual Leibniz reflexivity/transport and rank
accounting), TarskiProducts (code product sort/closed identity operation),
TarskiCasts (typed dependent Abs/App with reflexivity beta recovery).

For c=max(a+1,b), product constructor type has rank a+2. Use its type-equality
law at predicate level c+1, whose law type has rank c+2. Motives X->T and
T->X plus id_X give both cast directions; do NOT assume predicative Leibniz
symmetry at the same predicate rank. Global source conversion/quotation is
still open: neutral proof casts do not definitionally cancel, and pointwise
Leibniz evidence is not automatically equality of host families. Local laws
must be given actual identity witnesses, not assumed global interpreter laws.

## Full-PTS canonical contexts and hereditary type indices verified

New post-publication milestone: OpenCanonical computes full open-context
normal forms from context/term syntax, proving its budget sufficient from
original wf/typing. CanonicalSubstitution proves actual dependent TypedSub
for normalized entries, hereditary substitution, normalized term/type typing,
identity, composition and conversion coherence. CanonicalContexts constructs
normalized original wf contexts and identity TypedSub in both directions;
the original typing equivalence preserves literal terms/types/annotations.
It also proves normal declarations, idempotence and original context reduction.
CanonicalTypeIndex separates faithful raw HOAS syntax from canonical type
indices identifying exactly source beta conversion, with hereditary laws and
a checked normal-substitution-creates-redex regression. All apply to the full
dependent original PTS; they are executable METALEVEL syntax operations.

Fresh aggregate /tmp/pts-rk-self-canonical-audit.JWgIgs passes, exit 0:
326 closed reports (43 new module reports plus 19 new aggregate endpoints).
Recursive kernel/pristine inventory checks and unchanged ZFC/core/normalization
source checks pass. Independent API/prose reviews pass. All 226 stages of
the full current-root local CI pass, including actionlint and fresh upstream.
Ignored raw evidence: _build/self-interpreter-canonical-final-review.TPZ60J.
The separately published snapshot passes all 172 stages; the difference is
unrelated unpublished developments in this root worktree, not weakened CI.

Updated note/PDF: 20 pages, 270656 bytes, build exit 0 in
/tmp/pts-rk-self-note.zjmn3r. No overfull boxes, missing glyphs or unresolved
references; three mild underfull boxes. All-page text extracted and new
theorem/context/index/closing pages visually checked. Exact commands, all
compiler failures, tool versions, source/PDF hashes and theorem boundaries:
verification/self-interpreter-canonical-2026-10-20/COMMANDS.md.

HEAD and origin/main remain b6c81d1c24404835f5665b8bf4c263379dee5202 after
the completed requested commit/merge/verification-commit/push. Index is empty;
this new canonical continuation remains uncommitted. Unrelated pre-existing
changes and logs are preserved. First remaining mathematical goal: realize
the distinct syntax/canonical-index interface as originally typed internal
dependent families and a reifier, proving their coherence without assuming
El or a successful quotation theorem. No full dependent PHOAS evaluator or
general impossibility result has been claimed. Next verification command in
the pinned environment: opam exec -- dune build @theories/self_interpreter/audit;
allocate a fresh absolute --build-dir for new assumption output.

## Scoped publication merged and pushed; full-PTS canonical continuation

At the user's explicit request, committed the self-interpreter snapshot as
3411f31f007caecfe5251dacb276583edbd4bba9 and merged documentation branch
docs/finished-developments at 6820469a75acf5a1adda248c193930a9b22daa6a.
Actual two-parent merge 64864e36b4d748cf117f830cdc4438d4d4054a2f was pushed
normally to origin/main; git ls-remote confirms that exact tip. Three handoff
conflicts were resolved by retaining both complete sets of entries.

Publication was prepared in /tmp/pts-rk-phoas-publish.x7qwoT/worktree, without
unrelated BZC changes or bulky historical logs. Its fresh self-interpreter
audit gives 264 closed reports and passed recursive kernel/pristine checks.
The clean cold full CI passes all 172 stages, exit 0, 10:31:23--10:40:39 UTC,
with raw evidence in /tmp/pts-rk-self-publication.KX9EQK. The separate
verification commit b6c81d1c24404835f5665b8bf4c263379dee5202 was also pushed
and confirmed by git ls-remote; original main now has that exact HEAD.
Concise commands: verification/self-interpreter-publish-2026-10-20/COMMANDS.md.
The earlier 226-stage audit included unpublished unrelated developments.
Original main was fast-forwarded by compare-and-swap ref update and read-tree
WITHOUT -u, after verifying no staged content. All 3576 pre-existing worktree
files pass the before/after SHA-256 check. The original index is backed up in
/tmp/pts-rk-phoas-publish.x7qwoT/root-index-before. No worktree file was reset,
stashed or overwritten; excluded intent-to-add files remain local/untracked.

New proof work now starts from the published snapshot: executable open-context
canonical normalization, hereditary typed substitution, and separate faithful
syntax/canonical type codes. These are metalevel original-syntax constructions,
not yet an internal dependent PHOAS evaluator. Current first goal: compile
OpenCanonical, CanonicalSubstitution and CanonicalTypeIndex without extra
assumptions, then fresh audit and document the exact dependent boundary.
Next pinned command: opam exec -- dune build @theories/self_interpreter/audit.

## Finite indexed PHOAS, strong closed STLC decoding and dependent boundary

Latest self-interpreter milestone: the finite closed PHOAS package that was
open at the preceding checkpoint is now constructed for independent
Church-STLC. PHOASPackage closes actual original annotated syntax over one
ground binder, k+2 interpretation families and 2*(k+1)^2 polymorphic handlers.
PHOASAlgebra/PHOASFaithful prove original typing, full normality and exact
annotated-source injectivity, including comparison by target conversion.
PHOASTelescope/PHOASRecovery discharge actual finite substitution and
sequential application, without subject expansion or an infinite context.
Every independent term-closed source derivation has a sufficient computed
budget. No normal source value is precomputed and stored in these codes.

PHOASDecoder.closed_phoas_interpretation provides the ACTUAL closed decoder
and its original typing: applying it to the normal quote reduces to the
original, unreduced lambda o:U_0.t. The outer ground abstraction is part of
the decoder. Its external indices are budget k AND the FULL simple type A,
not just the order of A. At fixed (k,A) the decoder is independent of source
program size and derivation. A computed budget-one regression has a reducible
source, normal code, and strong recovery. No closed-form numeric sort bound
for this new package/decoder is claimed: universe witnesses are proved.

DependentPHOAS proves genuinely dependent local Abs/App handler formation,
actual typed identity interpretations and beta recovery, plus a candidate
universe decoder. It does not recursively translate an arbitrary dependent
family from A to abstract F_a(A). PHOASConversion proves a LIMITED obstruction:
a normal syntax-injective code cannot also preserve source conversion as a
semantic type index, even up to pointwise beta agreement with a second map.
Its witnesses already fit fixed small independent bounds. Genuinely distinct
syntax and semantic indices escape this obstruction. Full dependent indexed
PHOAS is neither constructed nor ruled out; substitution/conversion coherence
remains the central missing theorem. No parametricity/no-junk axiom is used.

Fresh aggregate build /tmp/pts-rk-self-phoas-final.t8AzBr exits 0 with
264 closed assumption reports. Recursive kernel checking, byte-identical
pristine core inventory comparison, unchanged frozen ZFC/original core and
source-stability checks pass. No new axioms or unsafe checks. Pinned versions:
Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1.
Independent contract review passes. Full local CI passes actionlint and
226/226 stages, exit 0; no stage was weakened. Scoped whitespace and shell
checks pass. This is local worktree verification, not a remote CI result.

Updated native LaTeX–Markdown note/PDF: 18 pages, build exit 0 in
/tmp/pts-rk-self-note.545XF9. No overfull boxes, missing glyphs or unresolved
references; three mild underfull boxes. All-page text and new theorem,
dependent-handler, obstruction and closing pages visually inspected.
Exact commands, intermediate failures, versions, source/PDF hashes and limits:
verification/self-interpreter-phoas-2026-10-20/COMMANDS.md.
Ignored raw aggregate logs: _build/self-interpreter-phoas-final.AM5spg;
full CI: _build/self-interpreter-phoas-ci.v3H6S5. Module attempts are recorded
in the linked subreports; new bulky raw logs are not source artifacts.

HEAD remains 73c4303dca2228bb6b3a8ec6ba5099a86da00bb0. No commit/push
requested or performed in this continuation; no staged content diff. The
large existing dirty worktree and unrelated BZC/documentation changes remain
preserved. Eight new proof modules, Audit/Dune integration, research note/PDF,
READMEs and handoff are uncommitted. Original rules and frozen ZFC unchanged.

First remaining PHOAS goal: construct compatible dependent context/type/term
translations with distinct semantic indices and syntax codes, proving actual
substitution and conversion coherence rather than supplying it as a premise.
Separately, internalize the STLC decoder's full-A interpretation argument.
The elementary compiler/numeric normalization route remains independent and
open. Next exact smoke command in the pinned environment:
opam exec -- dune build @theories/self_interpreter/audit
Use a fresh absolute Dune build directory for new assumption reports.

## Full-PTS complexity route, canonical HOAS and weak interpretation

This is the preceding self-interpreter milestone, after the HOAS/PHOAS work
below. The note now opens with the user's positive non-uniform argument:
fixed-budget full-PTS normalization is elementary; manuscript non-uniform
elementary representability would implement its numerical coding. Source
audit found no Rocq generic elementary compiler, and a concrete manuscript
modulus callback typo (r f x, not r X f x). The conditional numerical
proposition is not added as an axiom and does not assert typed unquotation.

RankedNormalization connects the actual executable original normalizer to
raw HOAS. Its canonical codes identify exactly original beta conversion,
including annotations. Automatic coverage has only original closed typing
as premise. Normalization-stage costs and separate code-size bounds are
proved; no internal PTS normalizer or complete serialization runtime claimed.

LiteralObstruction proves maximum literal r in quote r t and impossibility
of fixed-head unquotation for all normal sorts U_k from these codes. They
all have redex bound and result-type rank zero. This does not exclude
families with a literal ceiling or the conservative rank bound containing it.

WeakFullInterpretation.full_closed_weak_interpretation covers EVERY closed
original dependent t:A. Its total external quoter constructs a normal packet
of nf(t), typed at nf(A), plus the faithful raw HOAS tag of t. Original
validity supplies the exact sort witness A:U_s. The actual closed decoder
has type rank max(s+3,r+6), returns nf(t) in five beta steps, has original
result type A and is beta-convertible to t. Separate code conversion
injectivity retains literal annotated source syntax, not the supplied type
or derivation. No target inhabitance is assumed. This is a WEAK semantic-
payload interpretation: the decoder ignores the HOAS tag and normalization
is EXTERNAL. Pure-HOAS/PHOAS evaluation and strong dependent recovery remain
open. Earlier independent strong STLC and indexed PHOAS components remain.

Fresh aggregate build /tmp/pts-rk-self-complexity-final.sOJTwD exits 0:
179 closed assumption reports. Recursive kernel check, byte-identical core
inventory comparison with pristine upstream, frozen ZFC comparison and
original core comparison all pass. No new axioms or unsafe checks. Pinned
Rocq 9.2.0/Stdlib 9.1.0/Equations 1.3.2+9.2/OCaml 4.14.2/Dune 3.23.1.
Full local CI passes actionlint and all 226 stages. No stage was weakened.
This is later than the historical documentation-task concurrent Fold failure.
Independent source/contract review passes. Scoped whitespace and shell checks
pass; source hashes are unchanged across verification.

The revised LaTeX–Markdown note/PDF compiles to 14 pages, exit 0 in
/tmp/pts-rk-self-note.W7xAaD. No overfull boxes, missing glyphs or unresolved
references; three mild underfull boxes. PDF text and representative equations
visually checked. Full attempts, commands, versions, exact limits and hashes:
verification/self-interpreter-complexity-2026-10-20/COMMANDS.md.
Raw aggregate logs: _build/self-interpreter-complexity-final.jKsix8;
full CI: _build/self-interpreter-complexity-ci.4sCyGR. Module attempt paths
are in the concise checkpoint; new bulky logs are not source artifacts.

HEAD remains 73c4303dca2228bb6b3a8ec6ba5099a86da00bb0; no new commit/push
requested or performed in this continuation. No staged content diff.
Preserved the large existing dirty worktree and unrelated proof/docs work.
New theorem sources, Audit/Dune integration, research note/PDF, READMEs and
handoff are uncommitted. Reference ZFC and original PTS rules are unchanged.

First remaining goal on the complexity route: implement the all-rank numeral
family and a checked compiler for explicit elementary programs, correcting
the modulus callback, then compile fixed-budget numeric normalization.
Typed adapters and dependent normal-form reification must still be built;
the runtime argument alone does not construct them. The independent finite
closed normal PHOAS package and strong dependent coherence remain open.
Next exact pinned-environment command:
opam exec -- dune build @theories/self_interpreter/audit
Allocate a fresh absolute build directory for new assumption reports.

## Finished-development expositions and repository hygiene

Publication update: the user subsequently requested commit and push.
Prepared the documentation-only branch docs/finished-developments from
origin/main at ffa7131 in an isolated checkout. This excludes the separate
unpushed self-interpreter note at 73c4303 as well as all concurrent proof
work. The shared checkout/index remains with its active agent. Navigation
uses committed reference-model audits, without links into excluded sources.
The isolated PDF rebuild exits 0 in /tmp/pts-rk-development-docs.2eouKv;
all five documents retain their 38-page total. DOCUMENTS.sha256 records
these publication outputs. Commands and scope are in the same checkpoint.
The following audit and cleanup paragraphs describe the earlier shared
checkout snapshot; they do not assert a failure in this isolated branch.

Completed documentation for all five finished AI-assisted development groups:
shared arithmetic, relational arithmetic, functional arithmetic, normalization
complexity and the reference set model. Each has a substantive native
LaTeX–Markdown README.tex and compiled README.pdf, indexed by
docs/developments/README.md. Lengths are 6, 7, 9, 9 and 7 pages (38 total).
The set-model exposition is at docs/developments/ZFC_model so the entire
theories/ZFC_model directory remains byte-identical to PR #1 ffa7131.
The original handwritten kernel and ongoing BZC/self-interpreter work are
excluded. No Rocq source, Dune theory or proof statement was changed.

Original audit build: bash tools/build-development-docs.sh, exit 0, fresh directory
/tmp/pts-rk-development-docs.yJpNLU. All logs are free of overfull boxes,
missing glyphs and unresolved references. All-page PDFKit text scans and
representative visual inspection pass, including a corrected silent math
parse issue. Exact failures/commands and source/PDF hashes are recorded in
verification/development-docs-2026-10-20/COMMANDS.md and DOCUMENTS.sha256.

Fresh finished-development audit in /tmp/pts-rk-finished-audit.WOMXfC:
exit 0, 1,127 closed assumption reports. Recursive kernel check exits 0;
only unchanged upstream functional_extensionality_dep in the loaded global
context, no unsafe checks. Fresh core inventory matches retained pristine
upstream byte-for-byte. Pinned Rocq 9.2.0/Stdlib 9.1.0/Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Frozen ZFC and finished proof-source comparisons,
scoped whitespace, shell syntax and documentation-link checks pass.

Complete local CI was attempted, not green: actionlint and pristine upstream
pass, followed by normalization; the excluded, concurrently edited
self-interpreter failed in ChurchSyntaxFold.v at line 72 (congruence failed).
Later stages were not run. This is the observed concurrent snapshot, not
a claim about later self-interpreter edits. No excluded proof was edited and
no CI stage was weakened. Raw audit, kernel, PDF and failed-CI logs remain
local in _build/development-docs-audit.Pyd9JH; no remote success is claimed.

Moved 17 disposable artifacts (14 Python bytecode caches, .lia.cache,
and two generated Markdown–TeX sidecars) to the ignored recovery directory
_build/obsolete-generated.713zwP; removed their intent-to-add cache entries
and added ignore rules. Tests, provenance packages, dated verification logs
and unrelated user work are preserved. At that authoring checkpoint there
was no staged diff, commit or push, and shared HEAD was 73c4303.
Existing large dirty proof work remains intact.

This documentation task is complete; no theorem status changed. The first
unrelated CI issue to recheck is the concurrent self-interpreter stage.
Material BZC and dependent-unquotation goals remain with their ongoing owners.
Next exact documentation command: bash tools/build-development-docs.sh

## Markdown runtime, dated title and Figure 2 ready for publication

Added authorsonlines=true (default false) to the locally vendored class and
enabled it for the paper; explicit YAML date 16 October 2026 renders below
authors/affiliations. Four fresh metadata regression fixtures pass (true,
default, false, scalar/empty date). Tests also exposed/fixed external-preamble
catcode restoration and fragile email URL handling in authblk arguments.

Figure 2 had an empty display paragraph and display skips inside its float.
The figure-local mathpar binding now uses the same public mathpartir line/
rule bindings in a vbox without the $$ wrapper. It preserves external float
and caption spacing. An isolated test measures 42.944pt versus 21.944pt,
removing 21pt internal padding. Title/Figure 2 visually checked. More Unicode
aliases include leadsto, double parentheses/brackets, logical constants,
arrows and large operators, all mapped to the original TeX glyphs. Copied the
existing traditional paper's full TOWER-hardness badge disclaimer into Markdown.

Fresh final command: bash tools/build-markdown-paper.sh; exit 0, 40 pages,
1037340 bytes. Directory /tmp/pts-rk-markdown-paper.PBYDVw. All 72031 canonical
body characters and 818 ordered math fragments match; 32 labels, 103 citations
and byte-identical BBL match the traditional baseline. Final pass has no missing
glyphs/undefined references. Metadata tests: bash tools/check-markdown-class.sh,
exit 0, /tmp/pts-rk-markdown-class.rx9TmK. Exact logs, commands and limitations:
verification/paper-title-figure-2026-10-16/. Traditional paper.tex/pdf untouched.

User requests commit/push. Commit only the Markdown runtime/class/tests and
paper/build/docs/evidence; exclude existing dirty Rocq work and unrelated CI,
cache and proof logs. Publish using ordinary origin/main push, no force/merge.
No new Rocq proof/build claimed. Material-BZC next goal is unchanged: original
typing input bounds, then internal semantic totality. Next paper checks:
bash tools/check-markdown-class.sh and bash tools/build-markdown-paper.sh.


## Repository reorganization — verified under theories

The latest requested destination is theories/, superseding the interrupted
models/ request. Interpretation_of_R/ and ZFC_model/ now reside in
theories/Interpretation_of_R/ and theories/ZFC_model/. All 169 moved .v files
are byte-for-byte identical to parent b4fb83b; original kernel files, vendor
sources, and Rocq namespaces are unchanged. Build scripts target the new paths.
The set model has an audit alias; the same 91 modules are retained. Root and
subfolder READMEs and the rewritten AGENTS.md describe all projects and their
actual proof boundaries. Historical raw logs/packages retain their old paths.

The carried-forward BZC audit was committed separately as b4fb83b. This entry
belongs to the atomic layout/build/documentation commit on that parent,
message: Reorganize Rocq libraries under theories and refresh documentation.
Ordinary commit and push to origin/main are authorized by the current task;
no history rewrite or force-push. Existing user logs/ and generated .lia.cache
are preserved and excluded. Inspect git log/status for the final commit hash.

Verification, all exit 0 unless explicitly noted below:

- Pre-move bash tools/check-local-ci.sh: actionlint and all 171 stages passed,
  including pristine upstream.
- Fresh timeout 1200 dune build --build-dir /tmp/pts-rk-theories-layout-fresh.ifuGK9
  --display=short --no-buffer -j 2 @all: all developments compiled; 1257
  closed source-level assumption reports. All four new-path audit aliases pass.
- Fresh AUDIT.v against that build prints the public theorem types and 12
  closed transitive Print Assumptions reports. The first CLI invocation exited
  1 because output PUBLIC_AUDIT.vo did not match source basename AUDIT.v;
  changing only the output basename to AUDIT.vo passed. Both logs are retained.
- Recursive rocq check for both arithmetic public theorems, ModelSoundness,
  Normalization, and STLCEmbedding passed. An independent check of the unchanged
  core Ranks passed with the identical dependency-context functional
  extensionality axiom; no type-in-type, unsafe fixpoint, or positivity flags.
- Post-move bash tools/check-local-ci.sh: actionlint and all 171 stages passed,
  with unchanged coverage/results. The smaller check-direct-r.sh also passed.
- Source comparison, bash -n, actionlint, and all 81 current relative Markdown
  links passed. No proof compiler failure or build timeout occurred.

Exact commands, versions, raw outputs, and stage tables are in
verification/theories-layout-2026-10-14/. Temporary output is also retained in
/tmp/pts-rk-theories-layout-*.log and _build/local-ci-logs/theories-layout-*.
Local success does not claim remote GitHub CI success.

Theorem status is unchanged: Theorems 4/7 and effective Theorem5Target are
proved; original set-model soundness is proved with explicit supplied
parameters. Material BZC reduction remains OPEN, as does formalizing the
external STLC hardness theorem. First remaining foundation goal: a bounded
denotation-witness formula with original-typed agreement; then material
cardinal/GCH/hierarchy bridges. Next exact baseline command, with documented
OPAMROOT/PATH:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer theories/ZFC_model/Denotation.vo theories/ZFC_model/BoundedFormulaSelection.vo theories/ZFC_model/MaterialZermelo.vo
```

## BZC foundation audit — collected hierarchy needed; formal reduction OPEN

Source/mathematical audit is in ZFC_model/BZC_AUDIT.md. Under the
injection-gap formulation of GCH actually used by this construction,
BZC + GCH alone does not guarantee its supplied envelope. In an ambient
ZFC + GCH universe, M = V_(omega+omega) satisfies BZC and injection-gap
GCH; carrier n has rank omega+n, so no H in M contains every carrier n.
This is a relative-model argument, not a new Rocq theorem. It concerns
this collected set-sized construction, not all possible class interpretations.
Do not silently assume ordinal-cardinal representatives in weak GCH.

Supplying the actual V_(omega+omega) permits W = V_omega and supplies
the model's finite-level bounds. The global decoder and selector can use
fixed finite powersets beyond H, available in BZC; no additional collected
omega-sequence above H is identified. This does NOT certify arbitrary
Comp predicates. The first remaining formal goal is a bounded formula for
the original denotation-witness relation used by DenotationChoice and
PairedChoice, with an agreement theorem on original typed valid valuations.
The audit records a least-closed-relation construction over a fixed set J
and Power J as a method to instantiate, not as an already proved certificate.
Material cardinal comparison/GCH and hierarchy bridges remain unformalized.

HEAD c91f956; proof sources unchanged. This continuation updates audit and
handoff documentation only; no commit/push was performed for this check.
User logs/ and generated .lia.cache remain preserved. Targeted baseline
build exited 0 (cached); newly executed AUDIT.v exited 0 with all 14 closed
reports and full conditional theorem types. No timeout or compiler failure.
Exact commands and logs: verification/bzc-foundation-audit-2026-10-14/.
The proof audit is not a proof of BZC derivability.
Next exact baseline command, with the documented OPAMROOT/PATH:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo ZFC_model/BoundedFormulaSelection.vo ZFC_model/MaterialZermelo.vo
```

## Original model soundness — proved and freshly verified

ModelSoundness.original_typing_sound now proves the ORIGINAL typing
fundamental theorem with NO conversion, coherence, certificate-totality,
normalization or local-realization premise. The original denotation,
valid_valuation, annotated terms, PTS rules and target domain are unchanged.
ModelSoundness.original_membership_sound handles arbitrary original term
and type denotation witnesses; original_denotation_coherent and
original_rank_sound are proved too. sound_model_exists constructs an actual
global selector using ordinary Choice, and sound_nontrivial_model_exists
also proves its Bottom interpretation empty. closed_bottom_uninhabited is
an external corollary, not internal arithmetic self-consistency.

The final typing theorem's complete parameter list is:

```coq
forall W H s : Ens,
  transitive_set W -> INC omega_codes W -> tower_envelope W H ->
  (forall P : Prop, P \/ ~ P) -> cardinal_comparability ->
  infinite_powerset_gap -> family_choice -> selects_global_witnesses H s ->
  forall n (G : Ctx nat n) (t T : Term nat n),
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  forall rho, valid_valuation H s G rho -> realizes H s G rho t T.
```

The existence theorem removes the selector premise by constructing s; it
retains the explicit W/H, classical, cardinal and Choice hypotheses. Those
are model-construction principles, not assumptions of semantic soundness.
The FULL types, including original arbitrary-denotation conversion, are
printed in verification/model-soundness-2026-10-14/pts-rk-soundness-assumptions.log.

Fresh combined Dune build, five source comparisons, recursive kernel check,
theorem-type/assumption audit and full local CI ALL exited 0. All 171 stages
passed, including pristine upstream. The selected fresh dependency build
printed 420 closed reports. All 14 explicit audit reports are closed. The
recursive kernel summary lists only upstream functional_extensionality_dep,
and no unsafe settings. No new axiom, admitted proof or PTS change was made.
No timeout occurred. These are local workflow-driver results, not a hosted
GitHub Actions result. Exact commands, all failures, raw successful logs,
AUDIT.v, compiler versions and stage results are retained in
verification/model-soundness-2026-10-14/COMMANDS.md and adjacent files.
Fresh build directory: /tmp/pts-rk-soundness-fresh.q3YE9C.

Key proof: RankedHereditary handles every cut rank and both syntactic
outputs, including empty domains. RankedNormalization preserves actual
original denotation values, derives certificates from original validity,
and proves conversion. ModelSoundness supplies that theorem to the earlier
conditional fundamental theorem. No semantic proof obligation remains for
this supplied-hierarchy model.

REMAINING FOUNDATION GOAL: justify this SAME construction internally in
BZC + GCH + existence of V_(omega+omega). Material BZC satisfaction alone
does not establish this. Define/relate the actual material GCH/hierarchy
statements and certify bounded definability of the denotation predicates
used in relation_candidates/paired_relation_choice. Supplying an ambient
bound is insufficient for an arbitrary Rocq Prop. Only after completing
this milestone investigate removing hierarchy existence, per user direction.

Parent eb835a2. This continuation is being committed as
"ZFC model: prove original typing soundness and semantic conversion" and
ordinarily pushed under the standing authorization. Existing user logs/
and generated .lia.cache are preserved and excluded. Earlier entries below
are historical; their open semantic obligations have now been discharged.
Next exact baseline command, using the documented OPAMROOT/PATH:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ModelSoundness.vo ZFC_model/MaterialZermelo.vo ZFC_model/BoundedFormulaSelection.vo
```

## Original semantic conversion — compiled; soundness packaging in progress

RankedNormalization.original_typed_decoded_conversion compiles without a
conversion or certificate-totality premise. Its environmental premise is
the ORIGINAL valid_valuation. original_valid_variable_certificates derives
the required variable certificates by induction on original context
well-formedness. original_denotation_normalizes preserves every existing
original denotation value while reducing its term/type to a ranked
certificate. Consequently original_typed_conversion_values proves equality
of actual values of originally typed beta-convertible terms. These proofs
use the existing explicit W/H/selector/classical/cardinal/Choice parameters.

Standalone normalization attempts 1–8 exited 1,1,0,1,0,1,1,0: duplicate
scratch loadpath, explicit parameters, a missing context argument, variable
valuation reconstruction, then explicit conversion parameters. All raw logs
are /tmp/pts-rk-ranked-normalization-N.log. The successful command is:
opam exec --switch=pts-rk-ci -- timeout 180 rocq c
-Q _build/default/vendor/zfc ZFC -Q _build/default/theories PTSrk
-Q _build/default/ZFC_model PTSrkModel
-Q /tmp/pts-rk-normalization.RhcGEd PTSrkModel
-o /tmp/pts-rk-normalization.RhcGEd/RankedNormalization.vo
ZFC_model/RankedNormalization.v > /tmp/pts-rk-ranked-normalization-8.log 2>&1
All five Print Assumptions reports are closed. No timeout.

Next goal: instantiate original_realization_from_conversion with this proved
lemma and export original typing soundness, membership, and model existence.
Fresh combined checking, CI and final audit remain pending. HEAD eb835a2;
changes uncommitted. Internal BZC + GCH + hierarchy derivations remain OPEN.
Next command with the standard OPAMROOT/PATH below:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedNormalization.vo ZFC_model/RealizationInduction.vo
```

## All-rank hereditary substitution — compiled; original soundness bridge OPEN

RankedHereditary.hereditary_substitution now compiles for EVERY cut rank.
It assumes actual source and image certificates, original well-formed
contexts/typed substitution, bounded nonvariable cuts and target variable
certificates. It produces reductions of BOTH substituted term and type to
normal terms with a certificate retaining the SAME semantic values. These
are explicit inductive invariants, not an assumption of original soundness.
Empty domains are handled by selecting syntactic normal forms first.
Only the newly exposed lambda case invokes the smaller-rank induction.

The exact command used the standard OPAMROOT/PATH below and:
opam exec --switch=pts-rk-ci -- timeout 180 rocq c
-Q _build/default/vendor/zfc ZFC -Q _build/default/theories PTSrk
-Q _build/default/ZFC_model PTSrkModel
-Q /tmp/pts-rk-hereditary.S3MBci PTSrkModel
-o /tmp/pts-rk-hereditary.S3MBci/RankedHereditary.vo
ZFC_model/RankedHereditary.v > /tmp/pts-rk-hereditary-7.log 2>&1
Exit 0; three closed reports, including the general theorem. Earlier
attempts 1–7 exited 0,1,1,0,1,1,0 as the helper and full theorem grew;
all raw logs retained in /tmp for later durable archival. No timeout.
RankedSubstitution helper attempts 1,2 exited 1,0 (dependent Fin index);
RankedRootBeta certified_root_body attempt 1 exited 0. The latter now
identifies the actual body value for arbitrary certified arguments.

Pristine-upstream/full local baseline before edits exited 0, 168 stages:
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/hereditary-baseline"
bash tools/check-local-ci.sh > /tmp/pts-rk-hereditary-baseline.log 2>&1.
Integration/fresh final audit for the new theorem is pending. HEAD eb835a2;
proof work uncommitted. User logs/ and .lia.cache remain untouched.
Next proof goal: certificate totality from original typing and valid
valuations, then agreement with arbitrary original denotations. The
original_realization_from_conversion premise is still OPEN. The internal
BZC + GCH + supplied-hierarchy justification is independently open.
Next command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedHereditary.vo ZFC_model/RealizationInduction.vo
```

## Ranked certificates and material BZC — verified; full soundness OPEN

The integration note below is superseded by this fresh verification:
combined fresh build, seven source comparisons, recursive kernel audit,
theorem-type/Print Assumptions audit and complete local CI all exited 0.
All 168 CI stages passed, including pristine upstream. The selected fresh
dependency build printed 523 closed reports, including 53 in the seven new
modules. All 12 explicit audit reports are closed. The recursive kernel
summary lists only existing functional_extensionality_dep and no unsafe
settings. Original PTS sources/rules are unchanged. Closed assumption reports
do not discharge explicit theorem premises.

RankedSubstitution attempt 3 also proves normalized-binder lifting,
extension of certified variables, and the rank-zero case of the GENERAL
simultaneous bounded-cut invariant. NeutralCutRank attempt 8 proves strict
actual lambda-domain rank descent for arbitrary typed substitutions. Its
bound concerns nonvariable images and is stable under arbitrary binders.
RankedRootBeta attempt 1 derives body membership and ranks from actual
certificate children and preserves an arbitrary canonical redex value for
normal nonlambda arguments. All three builds exited 0.

The three main open obligations are all-rank hereditary substitution;
certificate totality from ORIGINAL typing/valid valuations and agreement
with arbitrary original denotations; and internal BZC + GCH + hierarchy
certification of this SAME model. The original_realization_from_conversion
type still explicitly assumes semantic conversion. MaterialZermelo proves
Ens satisfaction of syntactic BZC under explicit classical logic and ordinary
family_choice, not a BZC derivation of the PTS construction. Merely supplying
the hierarchy does not certify arbitrary denotation predicates as bounded.

Exact next goal: extend certificate_rank_zero_substitution to every r,
producing normal N,C with replace sigma t ->* N and replace sigma T ->* C,
and a certificate retaining the SAME semantic indices v,a. Under binders,
choose syntactic normal forms independently of semantic values (domains can
be empty), then align pointwise results by uniqueness. For a head that stays
neutral, use the result-type certificate child: its function rank can exceed
r. Use bounded_exposed_lambda_domain_rank when the head becomes a lambda.

Raw failed/successful logs, commands, printed theorem types, assumptions,
versions and CI results: verification/ranked-certificates-2026-10-14/.
Fresh build directory: /tmp/pts-rk-ranked-fresh.kI0Mjw. No compiler error or
timeout remains. Parent commit is 3454c9f; accumulated proof work is being
committed as "ZFC model: certify bounded constructions and ranked semantic substitution"
with an authorized ordinary push. User logs/ and generated .lia.cache are
preserved and excluded. Earlier status entries below are historical.
Next exact baseline command with the standard OPAMROOT/PATH below:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedRootBeta.vo ZFC_model/MaterialZermelo.vo ZFC_model/RealizationInduction.vo
```

### Historical integration note (before final verification)

The resumed continuation has compiled NeutralCutRank (all-rank neutral-spine
and exposed-lambda domain descent), RankedDenotation (structural normal
term/type certificates with actual formation/body children),
CanonicalValuationTransport (validity transport from actual same-value
declarations), and MaterialZermelo (explicit first-order BZC axioms and Ens
satisfaction under explicit classical logic and ordinary family_choice).
None supplies original typing totality or a BZC internal derivation of the
PTS model. The previous 161-stage verification predates these files.

RankedTransport now compiles in the integrated Dune tree (attempts 1,2,3
exited 1,1,0). This fixes the isolated .vo dependency mismatch by rebuilding
dependencies consistently, then explicit rank inference and a missing
AbstractRewriting import. Renaming, weakening, original context transport
and normal type/code alignment preserve both semantic indices.
RankedSubstitution now compiles (attempts 1,2: 1,0), proving substitution
for the FULL structural certificate with normal nonlambda images, including
its normalized-result-type child. General lambda-image hereditary
substitution and the original-denotation/valuation totality bridge remain
open. The next proof step is the ranked application/substitution induction,
using NeutralCutRank for active-head descent and RankedTransport for binders.

Commands and raw logs are currently /tmp/pts-rk-ranked-integrated-{1,2,3}.log
and /tmp/pts-rk-ranked-substitution-{1,2}.log. Each command used the standard
OPAMROOT/PATH below and timeout 180 dune build --display=short --no-buffer,
target ZFC_model/RankedTransport.vo or ZFC_model/RankedSubstitution.vo.
Fresh combined build, recursive audit and complete CI are still pending for
this continuation. No final success is yet claimed for the combined edits.
HEAD remains 3454c9f; existing work and user logs/ preserved. User has now
explicitly authorized commit and push; neither has yet been performed.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedSubstitution.vo ZFC_model/MaterialZermelo.vo ZFC_model/RealizationInduction.vo
```

## Canonical substitution and material deduction — verified; soundness OPEN

Eight new modules now pass fresh compilation and the recursive kernel audit:

- CanonicalRenaming: arbitrary renaming, normality, same semantic values.
- CanonicalRealization: local membership/rank from unconditional canonical
  coherence, variable/sort/product and normal-codomain lambda realization.
- CanonicalSubstitution: normal nonlambda substitution, including every
  normal argument whose type has rank zero. No semantic-conversion premise.
- CanonicalRootBeta: aligns arbitrary canonical redex witnesses with a
  normal original domain annotation; proves actual product-domain rank
  descent and same-value root reduction in the proved substitution case.
- CanonicalContext: same-syntax/same-value transport through original
  context typing morphisms and converted well-formed contexts. Does NOT
  assert valuation validity transports across declaration conversion.
- CanonicalApplication: actual application realization for normal inferred
  product and normal nonlambda argument, with no coherence premise; rank-zero
  corollary. Local constituent realizations remain explicit.
- CanonicalHereditary: normal rank-one application reaches a normal,
  originally typed term, and its substituted type is normal. The normal
  lambda branch preserves exact canonical value, membership and code rank.
  This is the application rank-one -> substitution rank-zero step, NOT the
  full rank-one substitution theorem, and NOT all-rank soundness.
- MaterialSetTheory: independent first-order natural deduction, guarded
  bounded-formula embedding, syntactic bounded-separation schema, actual Ens
  satisfaction of that schema, and its logical soundness without a theory
  satisfaction premise. Classical logic remains explicit. General BZC/GCH/
  hierarchy certification and weak-foundation justification remain open.

Baseline and first integrated build exited 0. Isolated compilation exits:
renaming 0; realization 0,0; substitution 1,0; root beta 1,1,0,1,0;
context 0; application 1,1,1,1,0; hereditary 0; material theory 1,0,0,0.
Failures were inference/import/dependent-pattern issues; no theorem was
weakened to fix a compiler error. No timeout in this continuation.

Fresh combined build, all eight source comparisons, recursive kernel audit,
theorem-type/Print Assumptions audit and full local CI ALL exited 0.
All 161 CI stages passed, including pristine upstream. The selected fresh
dependency build printed 397 closed reports, including 58 in the eight new
modules. All nine explicit audit reports are closed; the combined kernel
summary lists only existing functional_extensionality_dep and no unsafe
settings. The original PTS sources/rules are unchanged.

Exact commands, raw failed/successful logs, audit source, printed theorem
types, assumptions, toolchain versions and CI results are retained in
verification/canonical-substitution-2026-10-14/COMMANDS.md and adjacent files.
The fresh build directory was /tmp/pts-rk-canonical-substitution-fresh.lltB68.

No compiler error remains. FULL SOUNDNESS IS NOT PROVED: the original
conversion premise displayed below and in the fresh audit remains unproved.
The next mathematical goal is joint semantic hereditary substitution for
higher-rank normal lambda arguments, preserving actual values while
normalizing substituted terms AND inferred type witnesses. Its invariant
must retain actual product-domain/codomain rank certificates and pointwise
body membership; bare realizes loses those decompositions. Do not infer
body membership from the encoded function's membership or silently assume
certificate totality. A suitable certificate's totality from ORIGINAL
typing and the bridge back to the actual model must also be proved.
Canonical coherence, a fixed rank case, or an NF-based relation alone
cannot discharge the conversion/fundamental theorem. First-order foundation
certification is independently still open.

HEAD remains 3454c9f; work uncommitted/unpushed. Prior work and user logs/
are preserved; the untracked .lia.cache is not part of the proof sources.
Next exact baseline command for continuing the joint proof:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CanonicalHereditary.vo ZFC_model/CanonicalApplication.vo ZFC_model/CanonicalContext.vo ZFC_model/MaterialSetTheory.vo ZFC_model/RealizationInduction.vo
```

## Canonical denotation coherence — verified; full soundness OPEN

TypedEqualityRenaming.v proves native context regularity and a structural
embedding theorem, mutually preserving wf, typing and equality. Insertions
carry actual native declaration typings; synchronous binder extension does
not assume endpoint regularity or preservation. Ordinary typing/equality
weakening follow. Isolated compile exits 1,1,0; source comparison, recursive
kernel check and integrated Dune build exited 0; six closed reports.
Raw logs are retained with the canonical-coherence verification below.

CanonicalTypeWitnesses.v now compiles (attempt 4, exit 0, ten closed
reports). It constructs beta-normal typing witnesses for every originally
typed lambda/application in a well-formed context, preserving the original
lambda domain. Its normal-form existence argument is constructive and uses
the original strong-normalization/preservation theorems.

CanonicalDenotation.v proves COHERENCE of an AUXILIARY denotation with
beta-normal implicit type witnesses. Original typing uniqueness and
confluence make the witnesses identical, enabling induction on denotation
without semantic conversion, valuation-validity, Choice or hierarchy
premises. It preserves all original lambda annotations and the exact model
operations. Same-value inclusion into original denotes and valuation
extensionality are proved too. Totality, beta/type-conversion preservation
and agreement with arbitrary original denotations are NOT established.
Substitution can create redexes in normal types: the missing semantic
normalization/substitution argument cannot be inferred from coherence.

Canonical compilation attempts exited 1,1,124,1,0. The 180-second timeout
is retained (empty raw log); replacing uncontrolled splitting of set-valued
goals by explicit conjunction steps allowed the next compiler diagnostics
to finish. A final destruct-bracket fix yields three closed reports, with
no theorem weakened. Integrated build, isolated fresh build, all seven
source comparisons, recursive kernel check and full local CI exited 0.
All 153 CI stages passed. Fresh build: 412 closed reports, including 19 new
reports (6 native weakening, 10 normal witnesses, 3 canonical denotation).
Kernel summary: existing functional_extensionality_dep only, no unsafe
settings. Exact commands, printed theorem types, failure/timeout/success
logs and CI results are retained in
verification/canonical-coherence-2026-10-14/COMMANDS.md.

No compiler error remains. The first open mathematical goal is STILL the
original typed semantic-conversion obligation displayed below. An auxiliary
canonical route now has coherence and syntactic witness existence, but
needs totality and beta/type-conversion preservation before it can justify
original typing soundness. First-order Ens/BZC certification is also open.

HEAD 3454c9f unchanged. Work uncommitted/unpushed; user logs/ untouched.
Next exact command for continuing the semantic proof:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CanonicalTypeWitnesses.vo ZFC_model/CanonicalDenotation.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo
```

## Bounded choice sequence, model-data bounds, native equality — soundness OPEN

BoundedChoiceSequence.v reconstructs the existing finite prefixes and
countable choice sequence by bounded recursion, proving exact agreement
and injection for all indices. CardinalClassification.bounded_cardinal_code
now actually uses this bounded injection, so downstream product coding no
longer selects the native sup-nat sequence graph on this path. It still
uses explicit classical logic, ordinary family_choice, cardinal comparison
and the powerset-gap principle; their first-order derivation is not done.

BoundedModelData.v retains an explicit Cartesian/powerset bound when choosing
a selector. It proves the decoder is a SUBSET of the supplied envelope
(hence an element of Power H), and bounds global selector/selection graphs
using powersets and products over H. It does NOT put global data inside H.
The same selector's witness values are preserved.

TypedEquality.v defines native mutual context, typing and equality
certificates over original Term nat n, retaining every lambda annotation.
No constructor assumes original typing or untyped conversion. Reflexivity
and projection to original typing (both equality endpoints) are proved.
The REVERSE completeness theorem and semantic interpretation of these
certificates remain OPEN. This auxiliary judgment is not a replacement
target, not a model axiom, and not a solution of semantic conversion.

Incremental model-data and integrated choice/classification builds exited
0. Isolated typed-equality compile/source comparison/kernel check exited 0.
Fresh combined build, four source comparisons, recursive kernel check and
full local CI exited 0; all 150 stages passed. The fresh build printed 393
closed reports, including 29 new reports (16 choice sequence, 8 model data,
5 native equality). The kernel summary lists only the existing
functional_extensionality_dep, no unsafe settings. No timeouts. Exact
commands and raw success/failure logs are retained in
verification/semantic-foundation-2026-10-14/COMMANDS.md.
Full soundness remains open. HEAD 3454c9f unchanged; work uncommitted and
unpushed, with all prior changes and user logs/ preserved.
Next proof target: native typed-equality completeness and a non-circular
semantic coherence argument; the exact original conversion goal is below.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/TypedEquality.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo
```

## Combined bounded decoder and selection — verified, soundness OPEN

Starting checkpoint 3454c9f is pushed; only user logs/ were untracked.
BoundedDecoder.v proves branch specifications for arbitrary inputs, so a
branch cannot accept another code tag. Its bounded formula combines the
three graphs. Totality, single-valuedness, evaluation and equality with the
existing all_decoding_graph are proved under the SAME supplied hierarchy
premises; no Choice or GCH premise is added. All singleton numeral inputs
are covered, not merely a finite test family. BoundedDecodedSelection.v
uses that graph and proves equality of its witness sets/source domain with
the existing global construction. It preserves the SAME selector s and its
values. Every rank-typed dependent product is in the source domain; ordinary
family_choice supplies a selector. Sixteen new closed reports in total.

Baseline command exited 0. Incremental combined-decoder exits 1,1,0,1,0;
fixed missing imports and a multi-goal tactic dispatch, without weakening
theorems. Decoded-selection incremental exits 0,0. Fresh isolated build,
both source comparisons, recursive kernel check and full local CI exited
0; all 147 stages passed. The fresh dependency build printed 364 closed
reports. Kernel summary lists only existing functional_extensionality_dep;
no unsafe settings or timeouts. Exact commands and raw logs are retained in
verification/combined-decoder-2026-10-14/COMMANDS.md.

The first remaining soundness goal is to DISCHARGE the explicit conversion
premise in RealizationInduction, not repackage it as a model assumption:

```coq
forall n (G : Ctx nat n) rho A B m k,
  @wf nat RankSorts n G -> valid_valuation H s G rho ->
  @typ nat RankSorts n G A (𝓤 m) ->
  @typ nat RankSorts n G B (𝓤 k) -> A =ᵝ B ->
  forall a b, denotes H s n G rho A a -> denotes H s n G rho B b ->
    EQ (decode a) (decode b).
```

Its realization/coherence/rank theorems depend on this premise, so using
them to prove it without a joint well-founded argument would be circular.
First-order Ens/BZC certification also remains open. Closed reports do not
discharge explicit premises. HEAD remains 3454c9f, synchronized with
origin/main at continuation start. Current edits are uncommitted/unpushed;
user logs/ remain untouched. Next command for continued conversion work:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo
```

## Exact universes and sort decoder — verified checkpoint, soundness OPEN

BoundedUniverses proves every omega numeral is an actual code and provides
a bounded membership test for the exact original U n. The bounded universe
graph evaluates numeral n to U n. BoundedSortDecoder recovers n from 3*n+2,
evaluates that graph, and proves agreement with the existing decode for
every sort code. All three decoder branches now have individual correctness
proofs. A combined graph with off-branch exclusion and full agreement is
still needed. Typed semantic conversion and first-order Ens/BZC proof-system
certification remain open; full soundness is NOT established.

Incremental exits: universe 1,1,0,1,1,1,1,0; sort decoder 0. Twelve new closed
reports. Fixed dependent transport simplification, explicit environments,
missing imports and folding the environment for rewriting; no weakened
statements. Fresh downstream build, both source comparisons, recursive
kernel check and full CI exited 0; all 145 stages passed. The fresh build
printed 353 closed reports. Kernel audit lists only the existing imported
functional_extensionality_dep, with no unsafe settings. No timeouts.
Exact commands, failures and successful logs are retained in
verification/sort-decoder-2026-10-14/COMMANDS.md.
The user explicitly authorized commit and push. HEAD before checkpoint is
33d05ab; origin/main is five commits behind, none ahead. User logs/ excluded.
This work is being committed as "ZFC model: certify bounded decoding and
conditional realization". It is a verified intermediate checkpoint, not
a completed soundness proof. The first remaining decoder goal is off-branch
exclusion followed by agreement of a combined graph with existing decode.
Next proof command after verification:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedSortDecoder.vo ZFC_model/BoundedInfiniteDecoder.vo ZFC_model/RealizationInduction.vo
```

## Infinite decoder branch — verified, soundness OPEN

BoundedInfiniteDecoder recovers n from the actual singleton-numeral tag
3*n+1 using the bounded tripling graph and evaluates bounded_carrier_graph.
Its bounded separation graph is proved to evaluate repr(infinite n) to
carrier n for every n and to agree with the existing decode at those codes.
The supplied hierarchy premises remain explicit. Four closed reports;
incremental exits 1,0 (one extra bracket in a destruct pattern corrected).
Fresh isolated build, source comparison, recursive kernel check and full
CI exited 0; all 143 stages passed. Fresh dependency build printed 153
closed reports. Kernel summary lists existing functional_extensionality_dep;
no unsafe settings or timeouts. Commands and raw logs are retained in
verification/infinite-decoder-2026-10-14/COMMANDS.md.

Remaining decoder work: construct the sort-universe graph, handle 3*n+2,
then combine branches and prove the full decoder graph agreement. Semantic
conversion and first-order Ens/BZC justification remain open independently.
HEAD 33d05ab unchanged; work uncommitted/unpushed; user edits preserved.
Next exact command when implementing the remaining sort branch:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedInfiniteDecoder.vo ZFC_model/BoundedCodeArithmetic.vo
```

## Uniform tag arithmetic and finite decoder — verified, soundness OPEN

BoundedRecursion generalizes least-closed iteration using finite bounded
separators, without collecting a native reference-family range. Its graph
definition depends on the supplied step graph, bound and initial value,
not on the reference family used to prove correctness.
BoundedCodeArithmetic instantiates it with three singleton successors to
construct the graph numeral n -> numeral(3*n). Composing its bounded
application predicate with finite_carrier_graph yields bounded_finite_decoder.
Evaluation at repr(finite n) equals finite_carrier n for EVERY n, including
zero. This is the finite branch only, not a complete decoder or soundness.

Incremental exits: recursion 0; arithmetic 0,0. Twelve new closed reports.
Fresh isolated build, both source comparisons, recursive kernel check and
full CI exited 0; all 142 stages passed. Fresh dependency build printed
149 closed reports. Kernel summary lists existing functional_extensionality_dep;
no unsafe settings or timeouts. Exact commands and logs are retained in
verification/code-arithmetic-2026-10-14/COMMANDS.md. Infinite and sort decoder branches,
semantic conversion and first-order Ens/BZC certification remain open.
HEAD 33d05ab unchanged; work uncommitted/unpushed; user changes preserved.
Next exact command when adding the remaining decoder branches:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedCodeArithmetic.vo ZFC_model/BoundedIteration.vo
```

## Bounded representation of actual global witness selection — soundness OPEN

BoundedCodeSelection specializes formula selection to codeWitnessF.
The admissible source set and selected graph are both bounded-formula
separations. Proved pointwise agreement with the SAME existing selector's
global_code_witnesses values, and function membership on the admissible
sources. Ordinary family_choice supplies such a selector. For ALL m,n,a,b
satisfying the model's rank conditions, the actual dependent function
space is an admissible source (using existing cardinal/hierarchy premises).
No PTS or semantic-operation definitions changed; this is a verified
bounded representation of their selection, not a replacement model.

Incremental exits 1,0,0,0; nine closed reports. First error was dependent
Fin elimination, corrected without statement changes. Fresh build, source
comparison, recursive kernel check and full CI exited 0; all 140 stages
passed. Fresh dependency build printed 219 closed reports. Kernel summary
lists existing functional_extensionality_dep, no unsafe settings. No
timeouts. Commands and raw logs: verification/code-selection-2026-10-14/COMMANDS.md.
Full decoder/Ens first-order justification and typed semantic
conversion remain open; no unconditional soundness claim follows.
HEAD 33d05ab unchanged; work uncommitted/unpushed; user edits preserved.
Next exact command for continued conversion/decoder development:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedCodeSelection.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo
```

## Bounded formula-selection graph — verified, soundness OPEN

BoundedFormulaSelection gives a bounded formula identifying the candidate
fiber and the value selected from it. Candidate sets are quantified inside
Power B; equality to apply_set uses its previously certified value bound.
formula_selection_graph is separated from Prod A B, not defined by native
graph. Proved graph typing/evaluation and bounded_formula_set_choice for
every total bounded-formula relation, with ordinary family_choice explicit.
Six closed assumption reports; incremental exits 0,0. Fresh build, source
comparison, recursive kernel check and full CI exited 0; all 139 stages
passed. Fresh dependency build printed 84 closed reports. Kernel summary
lists existing functional_extensionality_dep; no unsafe settings or timeouts.
Commands/logs: verification/formula-selection-2026-10-14/COMMANDS.md.
No new axioms or admissions.

This closes generic formula-based graph selection, not the separate task
of expressing arbitrary denotation predicates as bounded formulas. Native
generic relation choice remains for those predicates. Semantic conversion,
full soundness and the first-order Ens/BZC interpretation remain open.
HEAD 33d05ab unchanged; work uncommitted/unpushed; existing edits preserved.
Next exact command for continued conversion/foundation development:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFormulaSelection.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo
```

## Bounded selection without candidate-family collection — soundness OPEN

BoundedChoice.bounded_relation_choice now chooses once on nonempty subsets
of the fixed codomain B. The new bounded_relation_choice_from_selector
requires only a selector on those subsets. Candidate selection no longer
uses choose_extensional_family or collects family_range A candidates.
The ProductWitnesses import was removed. Downstream denotation and paired
choice use the unchanged theorem interface and compile incrementally.

Incremental exits 0,0; one new closed assumption report. Fresh downstream
build, source comparison, recursive kernel check and full CI exited 0;
all 138 stages passed. Fresh build printed 274 closed reports including
dependencies. Kernel summary lists existing functional_extensionality_dep;
no unsafe settings or timeouts. Exact commands and raw logs are retained
in verification/bounded-selector-2026-10-14/COMMANDS.md. This removes one
native family-range construction, not all arbitrary-predicate separation:
only formula-specialized candidate predicates have bounded certificates.
Native selected graph construction and first-order foundation justification
remain audit obligations, alongside semantic conversion/full soundness.
HEAD 33d05ab unchanged; work uncommitted/unpushed; user changes preserved.
Next exact command when continuing the open semantic-conversion proof:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo
```

## Remove infinite comparison from carrier correctness — soundness OPEN

carrier_iteration_certificate_correct now uses carrier_separator_laws,
not the native sup-indexed carrier_relation. Each separator is obtained
from the preceding one by a bounded slice-filter formula; the base filters
Prod omega_codes H. An induction proves closure and uniqueness at its
index. No set collecting all separators is defined or required. The old
native comparison lemmas are retained but no longer feed correctness.

Incremental exits 1,0: corrected elimination of the pinned library's empty
type F (not native False). Two new closed reports, ten total in the module.
Fresh isolated build, source comparison, recursive kernel validation and
full local CI exited 0; all 138 stages passed. Fresh dependency build
printed 137 closed reports. Kernel summary lists the existing imported
functional_extensionality_dep; no unsafe settings. No timeouts. Commands
and logs are retained in verification/finite-separators-2026-10-14/COMMANDS.md.
The earlier comparison-relation audit concern is superseded by this proof,
but first-order induction/Ens, decoding tags, sort universes and semantic
conversion remain open. HEAD 33d05ab unchanged; work uncommitted/unpushed.
Next exact command when continuing the open conversion/foundation work:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo
```

## Uniform bounded carrier graph — verified, soundness OPEN

BoundedIteration defines a least-closed-relation Formula, quantifying over
Power(Prod omega_codes H). The resulting bounded_carrier_graph is defined
by bounded_formula_graph (separation), not a native indexed sup. It is a
function omega_codes -> H and evaluates to carrier n for EVERY n. This
closes the uniform infinite-carrier indexing step at the Ens translation
level; decoding code tags and sort universes remains separate.

Important audit limitation: the correctness proof uses the native
carrier_relation sup as a comparison relation. This does not by itself
derive that comparison's existence or the proof in first-order BZC. No
claim of eliminating Replacement from the whole proof is made. Semantic
conversion and full soundness remain open.

Incremental exits 1,1,1,0,0. Eight closed reports; no new assumptions.
Fresh isolated module build, source comparison, recursive kernel check,
and full CI exited 0; all 138 stages passed. Fresh dependency build printed
135 closed reports. Kernel summary lists existing imported
functional_extensionality_dep; no unsafe settings. No timeouts. Commands
and raw logs are in verification/bounded-iteration-2026-10-14/COMMANDS.md.
HEAD 33d05ab unchanged; all work uncommitted/unpushed, earlier work and
user logs/ preserved. Full proof remains open: typed decoded conversion
(exact judgment below), code-tag/sort decoding, and first-order foundation
justification. Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedIteration.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo
```

## Bounded powerset graph — verified, soundness OPEN

BoundedPowersets certifies powerset equality by a bounded formula when its
ambient bound contains all subsets of the argument. Separation on Prod W W
constructs the powerset graph in a transitive powerset-closed W; its typing
and evaluation are proved. Existing supplied-envelope lemmas discharge
these closure premises for H, yielding the actual carrier i -> carrier(S i)
step uniformly. No replacement/choice premise is used by the new graph.
This is not yet a bounded definition of the full recursively indexed
decoder, a first-order BZC interpretation, or semantic conversion.

Incremental exits 1,0,1,0: corrected a missing Ens parameter annotation and
an explicit argument to envelope_power_closed. Seven closed reports.
Fresh isolated module build, source comparison, recursive kernel check
and full CI exited 0; all 137 stages passed. Fresh dependency build printed
127 closed reports. Kernel summary lists imported functional_extensionality_dep
and no unsafe settings. No timeouts. Exact commands and all logs are in
verification/bounded-powersets-2026-10-14/COMMANDS.md.
HEAD 33d05ab unchanged; work uncommitted/unpushed and user logs/ preserved.
The user's full soundness request remains open: prove typed decoded
conversion as stated below, without using the conditional realization
theorems circularly. Foundation work also still needs the uniform indexed
decoder and a first-order audit. Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo ZFC_model/BoundedPowersets.vo
```

## Typed denotation coherence and membership — CONDITIONAL, soundness OPEN

RealizationInduction now also proves typed_coherence_from_conversion,
typed_membership_from_conversion and typed_rank_from_conversion. Structural
term induction handles coherence, transporting application codomain typing
between convertible binder contexts. Membership follows by comparing an
arbitrary denotation with the realization witness; rank specializes this
to a sort. All three retain the SAME explicit, unproved typed decoded
conversion premise below. No new semantic hypotheses or axioms were added.
This does not discharge conversion or first-order BZC certification.

Incremental build exits 1,0: corrected decode_sort's explicit carrier
argument. Fresh isolated build, source comparison, recursive kernel check
and full local CI all exited 0; all 136 CI stages passed. The fresh build
printed 298 closed assumption reports including dependencies. Three new
conditional theorem reports are closed; their conversion premise remains
visible in the printed membership theorem type. Library-wide kernel
summary lists imported functional_extensionality_dep; no unsafe settings.
No timeouts. Commands and raw logs (including failure) are retained in
verification/semantic-regularity-2026-10-14/COMMANDS.md.
HEAD 33d05ab unchanged; work uncommitted/unpushed, prior changes and user
logs/ preserved. Exact remaining goal is the typed decoded conversion
judgment printed below. Next command when continuing its proof:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo
```

## Original-typing realization induction — CONDITIONAL, soundness OPEN

User refocused on finalizing soundness. RegularTyping now supplies a proved
equivalent syntactic induction certificate with redundant type-formation
subderivations. Renaming/substitution/regularity, original embedding and
erasure are checked; no PTS rule or semantic domain changed. Using this,
RealizationInduction proves realization for ALL original typings from one
explicit typed-decoded-conversion premise, in addition to the existing
set-construction premises. Separate semantic regularity/component
realization/rank assumptions are no longer needed in that induction.

THIS IS NOT FINAL SOUNDNESS. The first remaining semantic goal is:

```text
forall n G rho A B m k,
  wf G -> valid_valuation H s G rho ->
  typ G A (sort m) -> typ G B (sort k) -> A =beta B ->
  forall a b, denotes H s n G rho A a -> denotes H s n G rho B b ->
  EQ (decode a) (decode b).
```

It is quantified explicitly as conversion, not declared as an axiom or
proved constant. Do not pass it to the theorem and call the result
unconditional. A joint well-founded conversion/coherence argument remains
necessary; existing conditional beta lemmas do not discharge it by
themselves. First-order BZC foundation certification also remains open.

Before the refocus, BoundedFiniteCarriers was completed: bounded closure
formula and uniform graph, evaluated at every numeral, for finite_carrier.
Its finite-code 3*n tagging and other decoding branches remain open.
Incremental exits: finite carriers 0; regular typing 1,1,1,0;
realization induction 0. Seventeen new closed reports, including two
CONDITIONAL realization theorems. Commands, failures and final verification
are retained in verification/realization-induction-2026-10-14/COMMANDS.md.
Fresh isolated build, all three source comparisons, recursive kernel check
and full local CI exited 0. Fresh build printed 295 closed reports including
dependencies; all 136 CI stages passed. Library-wide kernel summary lists
imported functional_extensionality_dep and no unsafe settings. No timeouts.
HEAD 33d05ab unchanged; all work uncommitted/unpushed; prior edits and user
logs/ preserved. Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo
```

## Formula-defined bounded graphs — verified, full target OPEN

Added general formula renaming and its semantic correctness to
BoundedFormulaTransport. BoundedGraphs builds an edge certificate from
p(x,y) and constructs its graph by separation on Prod A B. Its exact
application law and agreement with graph A f for a bounded extensional
f are proved. Totality and unique values of p directly give function
membership and evaluation satisfying p, with no family_choice premise or
prior selected native function. Dune and CI include the new module.

Incremental exits 1,0,1,0,0; seven new closed assumption reports. Retained
errors about dependent constructor indices and proof-placeholder inference;
both corrected without weakening statements. Fresh isolated build, source
comparisons, recursive kernel check and full CI exited 0. Fresh build
printed 278 closed reports including dependencies; all 133 stages passed.
Library-wide kernel summary lists imported functional_extensionality_dep,
no unsafe settings. No timeouts. Commands and all raw logs are recorded in
verification/bounded-graph-2026-10-14/COMMANDS.md.

Next obligation remains a bounded formula defining the actual decoder
uniformly from supplied hierarchy data. The new graph theorem can then
construct its graph by separation; it does not supply that formula or
justify Ens/Prod in first-order BZC. General semantic conversion and the
fundamental soundness theorem remain open too. HEAD 33d05ab unchanged;
work uncommitted/unpushed; user logs/ and prior edits preserved.
Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedGraphs.vo ZFC_model/CodeHierarchyBounds.vo ZFC_model/RootBeta.vo
```

## Bounded application/decoding predicates — verified, full target OPEN

BoundedApplication.v certifies the separation predicate of value_fiber,
its union apply_set, and equality to that value via a syntactically bounded
Formula. Correctness holds for arbitrary graphs, including empty and
nonfunctional ones; value_bound supplies the graph-value bound. Added
CodeHierarchyBounds.decoding_value_certificate using the existing decoding
graph and Power(carrier i) as its value bound. This only certifies decoding
equality GIVEN the graph, not the graph's first-order construction. Added
the module to Dune and CI (06pa-bounded-application); did not weaken checks.

Incremental compiler exits 1,0,1,0: fixed an environment type annotation
and an explicit import; retained both failures. Six new closed assumption
reports. Fresh isolated build, both source comparisons, recursive kernel
check and full local CI exited 0. Fresh build printed 271 closed reports
including dependencies; all 132 CI stages passed. Library-wide kernel
summary lists imported functional_extensionality_dep, no unsafe settings.
No timeouts. Commands and complete raw logs are retained in
verification/bounded-application-2026-10-14/COMMANDS.md.

Next foundation obligation: give a bounded first-order construction of the
decoding graph from supplied hierarchy data, rather than relying on its
current sup-based definition. General semantic conversion/realization and
validity transport remain open in parallel; these predicate certificates
do not prove the fundamental theorem. The full Ens/BZC foundation audit and
hierarchy identification also remain open. HEAD 33d05ab unchanged; work
uncommitted/unpushed; all existing edits and user logs/ preserved.
Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedApplication.vo ZFC_model/CodeHierarchyBounds.vo ZFC_model/RootBeta.vo
```

## Lambda witnesses and realization transport — verified, soundness OPEN

Proved DenotationInversion.lambda_product_body from original typing alone:
every product witness for a lambda has domain convertible to its annotation
and codomain typing the body in the annotated binder context. Refined
RootBeta.realized_root_beta to derive its former PA/PB application-witness
conversion premises from typed domain-to-annotation conversion and body-type
conversion. Both fiber denotations transport into the annotated context.
CA/CB, constituent realization/coherence and semantic regularity still need
the general joint proof; no unconditional model soundness is claimed.

Also proved realizes_context_transport, realizes_context_conversion and
realizes_valuation_extensional. These retain the value and type code under
context morphisms or pointwise equal valuations. They do not establish
preservation of valuation validity when declaration terms change; that
requires the still-open semantic declaration conversion argument.

Incremental exits 1,0,1,1,1,0,0. All failures were corrected and raw logs
retained (missing symmetry instance import, quantified argument introduction,
EQ_tran binder name, ambiguous tactic witness selection). No timeouts.
First isolated build/kernel/CI passed (262 closed reports, 131 stages).
Final isolated rebuild, source comparisons, recursive kernel check and
final CI also exited 0, including the three later transport lemmas:
265 closed reports with dependencies and 131 passing stages. The kernel
library summary lists imported functional_extensionality_dep, no unsafe
settings. Commands, full types, and all failure/success logs are recorded in
verification/beta-witness-refinement-2026-10-14/COMMANDS.md.

Next goal: discharge CA/CB via a well-founded joint semantic conversion,
coherence and realization argument, including validity transport for
converted declarations. Syntactic common-head normalization alone does
not supply denotation preservation. First-order BZC bounded-denotation and
foundation certification also remain open. HEAD 33d05ab unchanged; work
uncommitted/unpushed; user logs/ preserved. Next exact build command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/ContextTransport.vo ZFC_model/TypeHeadNormalization.vo
```

## Arbitrary beta values via derived coherence — verified, soundness OPEN

Added RootBeta.realized_root_beta. It derives redex coherence by composing
lambda/application coherence from strict constituent coherence and local
conversion of actual typing witnesses. The shared ranked beta witness then
transports to any given redex denotation: the actual substituted reduct
denotes that same value, which belongs to a decoded result code in U k.
No redex-coherence premise or universal rank/membership premise is used.
Lambda coherence now only requires decoded domain equality, not code
equality. All other existing changes and user logs/ were preserved.

Incremental build, fresh isolated build, both source comparisons, recursive
kernel check and full local CI exited 0. One new closed Print Assumptions
report; fresh build prints 261 including dependencies; all 131 CI stages
passed. Kernel library-wide summary lists the existing imported
functional_extensionality_dep, with no unsafe settings. No failed runs or
timeouts. Exact commands, complete theorem type and raw logs are retained
in verification/beta-coherence-2026-10-14/COMMANDS.md.

Full soundness is NOT proved. First remaining goal: derive decoded semantic
conversion for well-typed beta-equivalent domain/codomain terms under valid
valuations, jointly with constituent realization/coherence and semantic
regularity. The local PA/PB/CB premises in realized_root_beta remain proof
obligations, not model axioms. No unconditional fundamental theorem exists
yet. First-order bounded denotation and BZC foundation certification also
remain open; closed Rocq assumption reports do not settle them.
HEAD 33d05ab unchanged; work uncommitted and unpushed. Next exact check:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/DenotationCongruence.vo ZFC_model/TypeHeadNormalization.vo
```

## Shared typed beta value from realizations — verified, soundness OPEN

Previous turn made verified progress on ranked rule witnesses. Added
DenotationBeta.realized_beta. From domain/argument realizations and
body/type realizations in valid binder valuations, plus decoded domain/
codomain coherence, it chooses ranked witnesses and constructs one value
denoted by both redex and actual substituted reduct. It also gives the
denotation of the substituted result type, membership of the common value
in its decoding, and membership of that result code in U k. No universal
rank premise on arbitrary denotations or assumed redex-coherence premise
is used. DenotationBeta now imports the already checked paired-selection
and ranked-realization machinery.

Incremental build exited 0; one new closed Print Assumptions report.
Fresh isolated build, source cmp, recursive kernel check and full local
CI exited 0. Fresh build printed 260 closed reports with dependencies;
all 131 CI stages passed. Kernel library-wide summary lists imported
functional_extensionality_dep, no unsafe settings. No failed builds or
timeouts. Exact commands, full printed theorem type and raw logs:
verification/realized-beta-2026-10-14/COMMANDS.md.

The full proof is NOT finished. Next compare arbitrary redex denotations
with this constructed value using the lambda/application coherence steps,
deriving that comparison from local constituent facts rather than assuming
redex coherence. The general joint realization/semantic-regularity/
conversion argument remains open, as does the first-order BZC foundation
audit. A shared existential beta value alone is not arbitrary-denotation
preservation. HEAD 33d05ab unchanged; newer work uncommitted/unpushed;
user logs/ preserved. Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationBeta.vo ZFC_model/RootBeta.vo ZFC_model/DenotationInversion.vo
```

## Ranked rule witnesses from realizations — verified, soundness OPEN

Previous turn made verified progress on root beta. The existing syntactic
rank uniqueness/descent results in NormalizationComplexity/RedexRanks.v
already cover typing-witness independence, so no duplicate was introduced.
Instead added ranked_realization_witness to DenotationChoice.v: choose
the already ranked code from the type's realization and transport the
body's membership using decoded type coherence. LambdaRealization now
derives its ranked-witness premise from body/type realizations plus that
coherence. ApplicationRealization now selects a ranked domain/fiber family
from type realizations, constructs its product witness, and transports the
function/argument membership. The new application rule no longer needs a
universal rank bound on all denotations. Product coherence was generalized
to decoded component equality, which suffices for product congruence.

Incremental exits 0,0. Three new closed assumption reports. Fresh isolated
build, source comparisons, recursive kernel check and final full local CI
exited 0. Fresh build printed 259 closed reports including dependencies;
all 131 stages passed. Kernel summary lists imported
functional_extensionality_dep, no unsafe settings. No failures/timeouts.
Exact commands, printed types and raw logs:
verification/ranked-realization-2026-10-14/COMMANDS.md.

Full proof still OPEN: these rule lemmas require semantic realization of
types and decoded coherence; neither follows merely from the constructors.
The joint fundamental argument must include semantic regularity (the
required domain/codomain type realizations) and conversion, not assume it
as an extra model axiom. The arbitrary-denotation root-beta theorem retains
its stronger local rank/membership obligations. First-order bounded
denotation and the BZC hierarchy/cardinal audit remain open afterward.
HEAD 33d05ab unchanged; newer work uncommitted/unpushed; user logs/ untouched.
Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo
```

## Root-beta constructor — arbitrary witnesses extracted, soundness OPEN

Previous turn made verified progress on unconditional type-head
normalization. RootBeta.v now proves denotes_root_beta for an arbitrary
redex denotation, extracting application/lambda witnesses. It derives the
syntactic product-type equalities, well-typed domains/codomains, and the
argument typing from original typing alone. Original context conversion
transports the application codomain's typing and denotation into the
lambda context. The existing cross-product beta/substitution theorem then
proves the reduct has the same value.

IMPORTANT: the remaining local semantic premises are still explicit:
typed domain/codomain conversion, domain/codomain rank bounds, body
membership and argument membership. They are not proved general facts.
The result is a constructor step for the joint fundamental proof, not a
global beta-preservation or full soundness theorem. Initial versions were
refined to avoid requiring conversion for untyped terms or across different
contexts. No model contract assumes the final result.

Incremental exits 0,0,0. One new closed assumption report. Fresh isolated
build, source cmp, recursive kernel check and full local CI exited 0.
Fresh build printed 256 closed reports with dependencies; all 131 CI stages
passed. Kernel library-wide summary lists imported functional_extensionality_dep,
no unsafe settings. No failed builds/timeouts. Exact commands, printed
theorem type and raw logs: verification/root-beta-2026-10-14/COMMANDS.md.

Next goal remains the joint typed semantic conversion/rank/membership
invariant, using common-head classification and these constructor steps.
Do not assume that invariant, full beta preservation or final typing
soundness to close the proof. After it, complete the first-order bounded
denotation and BZC hierarchy/cardinal audit. HEAD 33d05ab unchanged; newer
work uncommitted/unpushed; user logs/ intact. Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo
```

## Common typed head — unconditional syntactic theorem checked

Previous turn made verified progress on application coherence. Added
TypeHeadNormalization.v: original strong normalization gives a head form;
typing inversion excludes sort/product-headed applications and lambdas at
sort types. Every well-typed type reduces to a sort, product or
variable-headed spine. Convertible well-typed types reduce to a common
such head and have equal sort ranks. These theorems have no semantic
premises. They preserve original syntax/annotations/rules. Head
classification does not assert full normality or semantic preservation.

Incremental exits 0,1,0: fixed an uninferred context-length parameter in
sort injectivity. Five module Print Assumptions reports closed. Initial
local CI passed, but isolated build failed (exit 1): the SortBounds import
needed an explicit PTSrk.NormalizationComplexity theory dependency. Initial
kernel check failed (exit 1) because the new proof object was missing.
Fixed the dune declaration. Isolated rebuild, final full CI and recursive
kernel check exited 0; all 130 CI stages passed. Rebuild printed 254 closed
reports with dependencies. Kernel summary lists imported
functional_extensionality_dep, no unsafe settings. Source cmp exited 0;
cmp of the non-copied dune manifest exited 2. No timeouts. All commands,
including failed runs, are retained in verification/type-head-2026-10-14.

Full model soundness remains OPEN. Next use the common-head classification
in the joint semantic conversion/ranked-membership argument. Still prove
denotation preservation along the two reduction paths; do not assume this
as a global contract or confuse syntactic rank equality with semantic
membership. First-order bounded denotation and BZC hierarchy/cardinal
justification remain open. HEAD 33d05ab unchanged; subsequent proof work
is uncommitted/unpushed; user logs/ untouched. Next exact command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationInversion.vo ZFC_model/BetaWitnessTransport.vo ZFC_model/ApplicationRealization.vo
```

## Application coherence step — verified, full proof still OPEN

Previous turn made verified progress on lambda coherence. Added
typed_product_domain and denotes_application_coherence to
DenotationInversion.v. Original type correctness proves well-typedness of
the product-witness domains. Original typing uniqueness and product
injectivity compare the two products, and the proved binder-context
conversion aligns fiber denotations. Semantic application congruence then
reduces the constructor to function/argument coherence and decoded
conversion of the actual domains/fibers. Those semantic premises remain
open; this is not a global soundness theorem or an axiom supplying one.

Incremental build exited 0; two new Print Assumptions reports closed.
Fresh isolated build exited 0 with 250 closed reports including dependencies.
Source cmp, recursive kernel check and full local CI exited 0; all 129
stages passed. Library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. No failed builds or
timeouts. Exact commands/logs retained in
verification/application-coherence-2026-10-14/COMMANDS.md.

Next concrete obligation: for beta-equivalent well-typed types T,T' in a
well-formed context and a valid valuation, prove equality of decoded values
of their denotations, together with ranked membership. In schematic form:
wf G; valid_valuation H s G rho; G |- T : sort i; G |- T' : sort j;
T =beta T'; denotes H s G rho T a; denotes H s G rho T' a'
must imply EQ (decode a) (decode a'). No such theorem is currently proved.
It must be established jointly with the typing/rank invariant needed by
root beta, without assuming final soundness or a global conversion contract.
The bounded first-order denotation and BZC hierarchy/cardinal audit also
remain open. HEAD 33d05ab unchanged; lambda/application steps uncommitted
and unpushed; user logs/ preserved. Next exact baseline command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo ZFC_model/BetaWitnessTransport.vo ZFC_model/ApplicationRealization.vo ZFC_model/DenotationCongruence.vo
```

## Lambda coherence step — verified, full proof still OPEN

Previous turn made verified progress and committed it as 33d05ab. Added
denotes_lambda_coherence to DenotationInversion.v. It derives beta
equivalence of the two body-result types by original uniqueness_of_typing,
then uses semantic lambda congruence. Domain/body coherence and decoded
conversion of those result types remain explicit local premises. Product
coherence now restricts its binder premise to actual denoted-domain
members, as required for a valid-context induction.

Incremental builds exited 0,0. The new theorem's Print Assumptions is
closed. Fresh build exited 0 (248 closed reports including dependencies);
refresh after the product-premise refinement exited 0 (13 reports). Source
cmp, recursive kernel check and final full local CI exited 0; all 129
stages passed. Kernel library-wide summary lists imported
functional_extensionality_dep, no unsafe settings. No failures/timeouts.
Exact commands and raw logs:
verification/lambda-coherence-2026-10-14/COMMANDS.md.

The full proof is NOT finished: establish decoded conversion/coherence and
ranked semantic membership from original typing, not as assumptions of the
final theorem. Lambda's result-type conversion is the next concrete
obligation, followed by arbitrary root-beta and the full fundamental
typing theorem. First-order bounded denotation and BZC hierarchy/cardinal
justifications remain open afterward. HEAD 33d05ab unchanged; this step is
uncommitted/unpushed. User logs/ preserved. Next exact baseline command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo ZFC_model/BetaWitnessTransport.vo ZFC_model/ApplicationRealization.vo ZFC_model/DenotationCongruence.vo
```

## Beta witness transport — checked commit checkpoint, soundness OPEN

BetaWitnessTransport.v proves beta_argument_typing using only original
redex typing and original inversion/conversion. semantic_beta_across_products
permits different application/lambda product witnesses with equal decoded
domains/fibers. denotes_beta_across_products uses this and original-syntax
substitution to reach the actual reduct. Semantic equality, rank bounds,
body membership and argument membership remain explicit premises; no claim
that every typed redex supplies them has been proved.

Incremental builds exited 0,0; three new Print Assumptions reports closed.
Fresh isolated build exited 0, printing 247 closed reports with dependencies.
Source cmp, recursive kernel check and full local CI exited 0. All 129 CI
stages passed. Library-wide kernel summary lists imported
functional_extensionality_dep, no unsafe settings. No timeouts. Commands,
the printed theorem type and raw logs are retained under
verification/beta-transport-2026-10-14/COMMANDS.md.

This checkpoint commits the accumulated global-selection, typed-denotation,
choice, context/congruence and beta-transport work on parent 4364c80 at the
user's request. It does NOT finish model soundness. No push requested or
performed; user logs/ excluded and preserved. Earlier entries below are
historical snapshots of the formerly uncommitted work.

First remaining goal: establish general denotation coherence and ranked
semantic membership from original typing in valid contexts, including
conversion, so arbitrary root-beta witnesses satisfy the transport lemma.
Then assemble reduction/conversion and full typing soundness. The native
denotation still needs a bounded first-order certificate, and hierarchy/
cardinal premises need justification in BZC + GCH + V_{omega+omega}.
Next exact baseline command (using the environment in COMMANDS.md):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BetaWitnessTransport.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo
```

## Six compatible reduction cases — verified, soundness open

Previous turn was verified progress on context conversion. Extended
DenotationInversion.v with lambda/application inversion through EQ closure.
DenotationCongruence.v proves lifting of denotation preservation through
the six compound-term reduction cases: product domain/codomain, lambda
annotation/body, application function/argument. Changed binder contexts use
the proved original context reduction; changed typing witnesses use original
subject reduction. The premises concern the reduced immediate subterm.
No root-beta theorem, global coherence or model soundness is assumed.

Two compiler runs were deliberately stopped with TERM while dependent
inversion expanded large semantic operations (driver exits 1,1). Replacing
broad splits alone did not fix the slowdown. Local Opaque declarations for
the three semantic operations prevent tactic unfolding; kernel checking,
guard/universe checking and the underlying definitions remain unchanged.
Run 3 exited 0, with eight additional closed assumption reports (two
inversions and six congruence lemmas). Run 4 (exit 0) restricts binder-body
hypotheses to actual domain extensions, making them usable with valid-context
induction. Fresh build exited 0 (244 closed reports including dependencies);
the isolated tree was then refreshed for that refinement (exit 0, six reports)
and source equality checked with cmp. Recursive kernel check and final full
CI exited 0; all 128 stages passed. Library-wide kernel summary lists imported
functional_extensionality_dep, no unsafe settings. Stopped runs were deliberate
terminations, not timeouts. All commands/logs retained under
verification/congruence-2026-10-14/COMMANDS.md.

Full soundness remains OPEN. The root beta case for arbitrary denotations
still needs semantic typing/rank validity and coherence of product witnesses;
denotes_matched_beta does not supply that case. Existence, conversion and
first-order BZC certification remain open. HEAD 4364c80 unchanged, newer
work uncommitted/unpushed, user logs/ intact. Next goal: prove the arbitrary
root-beta case together with required typing/coherence facts, then assemble
original reduction/conversion preservation. Next exact baseline command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo
```

## Context conversion transport — verified, model soundness open

Previous turn was verified progress on product inversion/application. Added
ContextTransport.v. A context_typing_morphism requires only the original
variable typings; original typing and denotation transport follow by the
proved simultaneous substitution theorem with the identity substitution.
Original context reduction supplies such a morphism. For structurally
beta-equivalent context declarations, well-formedness of the source proves
the morphism by induction, using original typ_conv and weakening. Thus
denotation is equivalent in two well-formed convertible contexts, with a
specialized binder-declaration corollary. No semantic conversion/coherence
premise is used for this result and no PTS rules were changed.

Incremental exits 0,1,1,0,0. Missing symmetry-instance import and an index
renamed by dependent elimination were fixed. Seven assumption reports
closed. Fresh isolated build, recursive kernel check and full local CI
exited 0. All 127 stages passed; fresh build printed 236 closed reports
including dependencies. Library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. No timeouts. Logs
and exact commands retained under
verification/context-transport-2026-10-14/COMMANDS.md.

Full soundness remains OPEN. Context conversion is not term conversion:
denotation existence, general term/type coherence, rank validity and beta
conversion soundness still need proof. Native denotation still needs its
first-order bounded certificate; hierarchy/cardinal foundations remain
unproved in BZC. HEAD 4364c80 unchanged, newer work uncommitted/unpushed,
user logs/ preserved. Next goal: use binder context transport in the semantic
term-conversion proof and establish coherence/rank validity without assuming
them in the final theorem. Next exact baseline command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ContextTransport.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo
```

## Product inversion and application witness reuse — verified, soundness open

Previous turn was verified progress on paired lambda witnesses. Added
DenotationInversion.v: product inversion through EQ closure, variable-value
uniqueness, and product coherence from domain/codomain subterm coherence.
ApplicationRealization.v reuses the product witness obtained from the
function's denotation and transports argument membership using domain
coherence. Its remaining premises are explicitly local domain coherence
and rank validity of domain/codomain denotations, not a model-soundness axiom.

Incremental exits for runs 1–8: 1,1,0,1,1,0,1,0. Failures: excessive split
unfolding, a wrongly applied specialized induction hypothesis, a missing
CodeUniverses import, a projection before supplying its function argument,
and a missing source after an atomic patch mismatch. All were repaired;
no theorem weakening. Four new assumption reports closed. Fresh isolated
build, recursive kernel check and full local CI exited 0. All 126 stages
passed; fresh build printed 229 closed reports including dependencies.
Library-wide kernel summary lists imported functional_extensionality_dep,
no unsafe settings. No timeouts. All logs and exact commands retained under
verification/inversion-2026-10-14/COMMANDS.md.

Full soundness remains OPEN. Next prove general denotation coherence and
rank validity (including conversion), rather than assume these in the final
typing theorem. The native rule-composition lemmas are not that final
theorem. First-order bounded denotation, hierarchy identification and
cardinal-premise derivations still need BZC justification. HEAD remains
4364c80, newer work uncommitted/unpushed; user logs/ untouched.
Next exact baseline command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo
```

## Joint type/body selection for lambda — verified, soundness open

Previous turn was verified progress (bounded selection and product induction).
Added PairedChoice.v: select pairs from Prod B C, then use proved Cartesian
projections to obtain two extensional families preserving a joint predicate.
Added LambdaRealization.v: select each body value with its own type code in
U k, bounding body values in carrier k by decoding_subset_bound. Lambda
realization in valid contexts no longer assumes a preselected codomain
family. It still explicitly requires pointwise ranked body witnesses; that
stronger induction invariant is not yet proved for all original typings.

Both incremental builds exited 0; four new assumption reports closed.
Fresh isolated build, recursive kernel check and full local CI exited 0.
All 124 stages passed; the fresh build printed 225 closed reports including
dependencies. Library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. No timeouts or failed
compiles this milestone. Logs and exact commands are retained in
verification/paired-choice-2026-10-14/COMMANDS.md.

Completion audit remains negative: no full typing/conversion theorem, no
first-order BZC interpretation certificate. Next prove uniform ranked body
realization and application compatibility, and general conversion coherence.
The pairing construction does not solve these by assuming model soundness.
Native denotation candidate separation still lacks a bounded-formula
certificate; hierarchy identification/cardinal-premise derivations remain.
HEAD 4364c80 unchanged; newer work uncommitted/not pushed, user logs/ intact.
Next exact baseline command in the documented local opam environment:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo
```

## Bounded witness selection and product induction case — verified, soundness open

Previous turn was verified progress on structural contexts/rule composition.
Added BoundedFormulaTransport.v, BoundedChoice.v and DenotationChoice.v.
All bounded formulas respect EQ-related environments. Set-indexed choice
selects extensional witnesses from relational candidates in a supplied set.
The formula instance certifies its candidate predicate as bounded; the
native denotation instance does NOT yet have that first-order certificate.

Proved sort-denotation inversion, extraction of universe-bounded witnesses,
uniform denotation family selection and lambda body selection in carrier k.
product_realization_in_context discharges product formation from the two
semantic induction hypotheses in valid contexts. Lambda body selection
still requires a compatible codomain family; application and conversion
coherence remain open. No final soundness theorem or BZC model is claimed.

Incremental exits 1,0,0,1,0,0. The two errors were omitted explicit choice
and denotation-context arguments; fixed by supplying them, not weakening
statements. Fresh isolated build, recursive kernel check and full local CI
exited 0; all 122 stages passed. Ten new module assumption reports closed;
fresh build printed 221 closed reports including dependencies. Library-wide
kernel summary lists imported functional_extensionality_dep, no unsafe
settings. No timeouts. All logs (including failures) and exact commands are
retained in verification/bounded-choice-2026-10-14/COMMANDS.md.

HEAD remains 4364c80; newer work uncommitted and not pushed, user logs/
untouched. Next goal: coherence for denotations of codomain types, so the
lambda/application induction hypotheses provide compatible witnesses, then
conversion and full original typing soundness. Native Comp of denotation,
bounded recursion, hierarchy identification and cardinal principles still
need first-order BZC justification, not just closed Rocq assumption reports.
Next exact baseline command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationChoice.vo ZFC_model/DenotationBeta.vo
```

## Structural contexts and original-rule realization — verified, soundness open

The previous turn was verified progress (original-syntax substitution and
matched beta), not a blocked/no-progress turn. Added InterpretedContexts.v:
valid_valuation recursively interprets only context declarations, not all
typing judgments. It is extensional in valuations and supports a proved
lookup theorem, yielding variable realization. Sort realization is also
proved. RuleRealization.v composes explicit witnesses for products, lambdas
and applications; application uses denotes_subst for the actual B ◁ u result
type. Set-equality type transport is proved, but is NOT syntactic conversion.

Incremental commands building InterpretedContexts.vo twice and then
RuleRealization.vo exited 1,0,0. The first failure was an unnamed index after
dependent elimination; naming its successor branch fixed it. Eight new
assumption reports are closed. Fresh isolated build, recursive kernel check
and full local CI each exited 0. All 119 stages passed; fresh build printed
211 closed reports including dependencies. Library-wide kernel audit lists
imported functional_extensionality_dep and no unsafe settings. Exact commands
and all logs (including the failure) are retained in
verification/contexts-2026-10-14/COMMANDS.md.

Still OPEN: existence and coherence of denotations/fiber families for every
typing, semantic equality from syntactic conversion, and consequently the
full typing induction. In particular, do not replace those obligations by a
model record assuming the rule-realization premises. First-order bounded
construction of syntax/valuation/denotation, hierarchy identification and
derivation of cardinal/choice principles remain foundation obligations.
No BZC soundness theorem follows merely from these native Ens proofs.

HEAD remains 4364c80, with all newer work uncommitted; no push. User logs/
preserved. Next goal: prove denotation coherence and construct extensional
bounded fiber witnesses from the induction hypotheses; then close conversion
and typing induction. Next exact baseline command:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RuleRealization.vo ZFC_model/DenotationBeta.vo
```

## Original-syntax denotation, substitution and matched beta — not full soundness

Added SyntaxRenaming.v, SyntaxSubstitution.v, Denotation.v and DenotationBeta.v.
The relation uses original Term nat n and Typing.typ; no calculus changes.
It does not assume semantic membership. Proved valuation extensionality,
renaming, simultaneous and single-variable substitution. Original typing
witnesses transport using independently proved original-typing lemmas.
denotes_matched_beta gives the same value to a redex and its substituted
body under matching witnesses and explicit semantic typing/bound premises.
It is not general conversion soundness or denotation coherence.

Incremental build exits for runs 1–9: 0,0,0,1,0,0,1,0,0. Failures were
variable-constructor inference (fixed with explicit typ_var arguments) and
the unapplied polymorphic var constructor (fixed with explicit parameters).
Fresh isolated build, independent recursive kernel check and full local CI
all exited 0. All 117 CI stages passed. Seven new module assumption reports
are closed; the fresh build prints 203 closed reports including dependencies.
The library-wide kernel summary lists imported functional_extensionality_dep
and no unsafe settings. Logs (including failures) and exact commands are
retained under verification/denotation-2026-10-14/COMMANDS.md.

Full model soundness remains OPEN. The three next obligations are:
1. Denotation existence, including extensional families, for well-typed
   original terms in well-interpreted contexts.
2. Coherence across different typing witnesses and conversion; use the
   proved substitution theorem, but do not equate matched beta with arbitrary
   conversion preservation.
3. Original Typing.typ membership soundness, then the first-order BZC+GCH
   and supplied-hierarchy justification (including cardinal premises and
   V_{omega+omega} identification). Closed Rocq assumptions do not prove BZC.

HEAD remains 4364c80, not pushed. All global-choice/operations and new
denotation changes remain uncommitted. User logs/ are preserved untouched.
Next exact build command (repository root, documented local opam environment):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationBeta.vo
```

## Rank-independent typed operations verified; completion audit fails

Previous turn was verified progress on global selection. GlobalOperations.v
now defines semantic_product, semantic_lambda and semantic_application using
the global selector. It proves their typing, beta and congruence for equal
semantic domains, fibers, bodies and arguments. The selector contract is
proved obtainable from family_choice; no model/soundness axiom was added.

Incremental exits 1,0,0: the first elaboration failed to infer the lambda
fiber family. Explicit theorem arguments fixed it without statement changes.
The later build adds application congruence. Large global definitions made
elaboration slow, but no run timed out. Local Opaque declarations control
elaboration only; kernel/guard/universe checking remain enabled. Fresh build,
recursive kernel check and full CI exited 0. Eight module reports closed;
fresh build printed 195 closed reports including dependencies. Library-wide
kernel summary lists imported functional_extensionality_dep, no unsafe
settings. All 113 stages passed. Commands/raw logs including failure retained
under verification/global-operations-2026-10-14/COMMANDS.md.

Completion audit: no original-syntax interpretation or theorem preserving
Typing.typ is present. Syntax.app has no type annotation; the paper's inverse
coding operation requires the product type. A typed interpretation must
therefore supply this information and prove conversion/derivation coherence.
Inversions.uniqueness_of_typing proves only syntactic beta-equivalence and
does not discharge semantic coherence. No annotation-erasing bridge or new
calculus was introduced. Substitution, conversion and typing soundness are
still unproved, as are first-order BZC derivations of the construction and
cardinal principles and the hierarchy identification. Full completion cannot
be claimed from the current semantic algebra or closed assumption reports.

HEAD remains 4364c80, not pushed. GlobalCodeChoice/GlobalOperations and their
build/docs/evidence changes are uncommitted. User logs/ remain untouched.
Next goal: implement a typed denotation for the original syntax with explicit
semantic product data, then prove substitution and conversion coherence;
do not silently choose a product type from a cardinal code alone.
Next exact command:

```sh
sed -n '1,115p' theories/Typing.v
sed -n '1,125p' theories/Inversions.v
sed -n '1,200p' ZFC_model/GlobalOperations.v
```

## Rank-independent selection in the supplied hierarchy verified

On request, committed the preceding verified witness/projection/congruence
work as 4364c80 (`ZFC model: construct selected codes and prove semantic
congruence`), not pushed. The new GlobalCodeChoice.v work is uncommitted;
user logs/ preserved.

GlobalCodeChoice defines a single candidate set from a semantic source A,
all codes and one decoding graph. All coding graphs are bounded by
Power(Prod H H). rank_independent_code_choice supplies one selector for all
ranks, assuming explicit transitive W, omega_codes subset W, tower_envelope
W H, classical logic, cardinal comparability/gap and family choice.
bounded_code_admissible proves the chosen code belongs to every justified
universe, using strict carrier growth. Global code/bijection projections are
typed and extensional in A, with no rank argument. No new global axioms.

Incremental build exits 1,1,1,0,0: explicit hierarchy base, Cartesian factors
and rank parameters resolved inference failures. Fresh build and recursive
kernel check exited 0. Full local CI passed 112 stages, exit 0. Six module
assumption reports are closed; fresh build printed 187 closed reports with
dependencies. Library-wide kernel summary lists imported
functional_extensionality_dep, no unsafe settings. Commands and raw logs
including failures: verification/global-code-choice-2026-10-14/COMMANDS.md.

Full model soundness remains unproved. Next goal: use the rank-independent
code/bijection operations to define syntax interpretation and prove
substitution, conversion and typing soundness. First-order bounded existence
of the global code/decoding graphs, cardinal/choice-principle derivations,
bounded recursion and hierarchy identification remain foundation obligations.
This uses the supplied hierarchy as a bound; it does not prove its existence
or identify it with V_{omega+omega}. Preserve model-first ordering.
Next exact inspection command:

```sh
sed -n '1,220p' theories/Syntax.v
sed -n '1,200p' theories/Typing.v
sed -n '1,220p' ZFC_model/GlobalCodeChoice.v
```

## Selected-code projections, beta and fixed-rank congruence checked

Previous turn made verified progress on code-preserving witnesses.
SelectedCodes.v now defines selected_code and selected_bijection using
Cartesian graph projections, proves their typing, and specializes coded_beta
to the selected bijection. ProductExtensionality.v proves equality of
dependent products from equal domains and pointwise-equal extensional fibers.
selected_codes_congruence propagates that equality to both selected outputs
at fixed ranks, with the same selection operation. No PTS rules changed.

SelectedCodes incremental builds exited 0,0. ProductExtensionality builds
exited 1,0 (explicit binders needed for constant-family extensionality).
Fresh build and recursive kernel check exited 0. Full CI passed all 111
stages, exit 0. Five SelectedCodes and two ProductExtensionality reports are
closed; fresh build printed 181 closed reports including dependencies.
Library-wide kernel summary lists imported functional_extensionality_dep,
no unsafe settings. Commands/raw logs, including failure, retained under
verification/selected-codes-2026-10-14/COMMANDS.md.

HEAD remains 62f7381, not pushed. This and the preceding product/code witness
source/build/docs/evidence changes are uncommitted; user logs/ untouched.
Full model soundness remains unfinished. Next goal: construct a single
rank-independent selection using the supplied hierarchy (or prove the
needed coherence), then define the syntax interpretation and prove its
substitution/typing soundness. Generic cardinal principles and bounded
recursion/existence still require first-order BZC+GCH justification. Do not
identify fixed-rank congruence with the syntax substitution theorem.
Next exact command:

```sh
sed -n '1,180p' ZFC_model/SuppliedHierarchy.v
sed -n '1,220p' ZFC_model/SelectedCodes.v
```

## Code-preserving witnesses and fixed-rank uniform selection verified

Previous turn made verified progress on product witnesses. CodeWitnesses.v
now certifies a bounded predicate retaining (code, bijection), proves its
nonemptiness and rank bound, extracts the actual bijection to decode c, and
proves uniform_product_code_choice: for every fixed m,n there exists one
set-coded operation s selecting such witnesses for every typed product.
Its premises remain classical logic, cardinal_comparability,
infinite_powerset_gap and family_choice. These are not new global axioms,
nor proved consequences of a first-order BZC+GCH calculus.

Incremental build exits: 1,1,1,0,1,0 (environment type inference, rank-bound
arguments, unfolded carrier inference, then a destruct-pattern bracket).
All fixed without weakening statements. Fresh build and recursive kernel
check exited 0; full local CI passed 109 stages, exit 0. Six new theorem
reports are closed; fresh compilation printed 168 closed reports including
dependencies. Library-wide kernel audit lists imported
functional_extensionality_dep, no unsafe settings. Exact commands/raw logs
including failures: verification/code-witnesses-2026-10-14/COMMANDS.md.

HEAD remains 62f7381, not pushed. ProductWitnesses and CodeWitnesses plus
their source/build/docs/evidence changes are uncommitted. User logs/ preserved.
Full model soundness is NOT complete. Next goal: define code and bijection
projections from selected pairs, prove extensionality under equality of the
product data and establish rank-independent/coherent selection needed for
substitution. First-order bounded recursion, cardinal-premise derivations,
hierarchy identification and the original PTS soundness induction remain
open. Model-first ordering unchanged. Next exact inspection command:

```sh
sed -n '1,200p' ZFC_model/CodeWitnesses.v
sed -n '1,180p' ZFC_model/CodedFunctions.v
```

## Product-witness nonemptiness and hierarchy bound verified

The prior dichotomy/all-product coding checkpoint was committed on request
as 62f7381 (`ZFC model: prove countable dichotomy and all-product coding`),
not pushed. This continuation adds ProductWitnesses.v, currently uncommitted.
User logs/ remain untouched.

product_witnesses_nonempty follows from decoded_product_code, with classical
logic, cardinal_comparability, infinite_powerset_gap and family_choice all
explicit. product_witnesses_rank_bound places the eligible set in
carrier(13 + max(m+1,n)) without those premises. coding_targets_bounded
identifies the target family with the existing bounded decoding range.
choose_extensional_family constructs a graph for an extensional set-indexed
family from ordinary family_choice. No new global axiom or PTS rule change.

Incremental builds exited 0,1,0: the failed target-range equality omitted the
decoding graph beta law, fixed using that law. Fresh build, recursive kernel
check and full CI exited 0. Four module reports are closed; fresh build
printed 162 closed reports with dependencies. Library-wide kernel summary
lists imported functional_extensionality_dep and no unsafe settings. All
108 CI stages passed. Commands and raw logs, including failure, retained
under verification/product-witnesses-2026-10-14/COMMANDS.md.

Next goal: extend eligible witnesses to retain the universe code, not only
its decoded carrier, and construct a coherent set-indexed choice of coding
bijections. Arbitrary carrier/bijection choice is not yet a term-level code
constructor. BZC derivation of the cardinal principles, bounded recursion,
hierarchy identification and the original PTS soundness induction remain
open. Preserve model-first ordering. Next exact inspection command:

```sh
sed -n '1,180p' ZFC_model/ProductWitnesses.v
sed -n '1,160p' ZFC_model/CodedFunctions.v
```

## Finite/countable dichotomy and all-product code theorem checked

Previous turn was verified progress, committed as 8eecf29 (not pushed).
CountableDichotomy.v constructs a countable graph by choosing outside finite
prefixes, or exhibits a finite bijection when a prefix covers the set.
Choice is supplied on nonempty subsets of X, obtained from the explicit
generic family_choice principle. The theorem does not assume the dichotomy.

CardinalClassification.v now proves:

    decoded_product_code :
      (forall P : Prop, P \/ ~ P) -> cardinal_comparability ->
      infinite_powerset_gap -> family_choice -> forall m n a b,
      IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
      exists c, IN c (U (Nat.max (S m) n)) /\
        equinumerous (dependent_product (decode a) (fun x => decode (b x)))
          (decode c).

No countable-injection side condition remains. This is still conditional on
independent cardinal/choice principles, NOT a full BZC+GCH model proof.
Native recursion and sup nat used for the sequence must be replaced or
justified by bounded first-order constructions. Coherent selection and the
original PTS soundness induction remain open.

Incremental builds exited 1,0,1,0: missing Prop annotation, then explicit
finite decode parameters, fixed without weakening statements. Fresh build,
recursive kernel check and full local CI exited 0. Five dichotomy and two
additional classification assumption reports are closed; fresh build printed
138 closed reports including dependencies. Library-wide kernel audit lists
imported functional_extensionality_dep, no unsafe settings. All 107 stages
passed. Exact commands/raw logs including failures retained in
verification/countable-dichotomy-2026-10-14/COMMANDS.md.

Current source/build/docs/evidence changes are uncommitted atop 8eecf29;
user logs/ untouched. Next goal: connect decoded_product_code to the bounded
eligible-witness sets and prove their nonemptiness, then choose coherent
coding bijections from a set-indexed family. In parallel to that mathematical
work, generic comparison/gap principles and sequence construction still need
derivation in the precise BZC+GCH theory. Model-first ordering is unchanged.
Next exact command:

```sh
sed -n '75,240p' ZFC_model/BoundedBijections.v
sed -n '1,210p' ZFC_model/CodedFunctions.v
```

## Finite-embedding classification verified

Previous turn made verified progress and committed e9862f3 (not pushed).
FiniteClassification.v now proves:

    finite_embedding_classification :
      (forall P : Prop, P \/ ~ P) -> forall n X,
      embeds X (finite_carrier n) ->
      exists m, m <= n /\ equinumerous X (finite_carrier m).

The proof constructs the actual enumeration graph and an injection's range
bijection. Five module assumption reports are closed. The explicit classical
premise is not erased by these reports. Both incremental builds, fresh build,
recursive kernel check and full CI exited 0. Fresh build printed 42 closed
reports including dependencies. Kernel summary has no axioms or unsafe
settings. All 106 local CI stages passed. Commands/raw logs retained under
verification/finite-classification-2026-10-14/COMMANDS.md.

Prepare this source/build/docs/evidence checkpoint from parent e9862f3;
user logs/ preserved, no push. Full model proof is not finished.
Next goal is the finite/countable dichotomy: obtain a finite embedding or a
countable injection for arbitrary relevant sets from explicit bounded choice.
Do not add the dichotomy as a hidden product-coding assumption. Also audit the
new image separation/finite graph; comparability/gap derivation, coherent
selection, hierarchy identification and original PTS soundness remain open.
Next exact command:

```sh
sed -n '1,240p' ZFC_model/BoundedBijections.v
sed -n '1,210p' ZFC_model/FiniteClassification.v
```

## Conditional infinite classification checked; full model still open

Previous turn was progress on bounded comparison. CardinalClassification.v
now proves infinite_bounded_classification, infinite_bounded_code and
infinite_decoded_product_code under explicit classical logic, generic
cardinal comparability and the infinite-powerset-gap principle. No new global
axioms are introduced. Those principles are NOT yet derived in BZC+GCH.
The product theorem also requires an injection of omega_codes into the
product; it therefore does not cover finite products. Index uniqueness is
proved without the three principles. This is not final model soundness.

Two incremental builds, fresh isolated compilation, recursive kernel check
and complete local CI all exited 0. Four new assumption reports are closed;
the fresh build printed 126 closed reports including dependencies. The
library-wide kernel summary lists imported functional_extensionality_dep,
no unsafe settings. All 105 stages passed, including pristine upstream.
Exact commands and logs: verification/cardinal-classification-2026-10-14/.

Prepare the user-requested commit from parent
506fe328ee59dda401f038d36031755748d0ac84, including this proof and the prior
bounded-gluing checkpoint, docs, build wiring and evidence. User logs/ remain
excluded. No push requested in the latest message.

Next goal: prove the finite/countable dichotomy and finite classification,
then discharge the generic comparison/gap principles in the stated theory.
Do not assume the missing product-coding theorem. Coherent bounded witness
selection, hierarchy identification, first-order BZC derivability and PTS
soundness remain open, with the model-first ordering unchanged.
Next exact inspection command:

```sh
sed -n '110,190p' ZFC_model/CodeUniverses.v
sed -n '110,165p' ZFC_model/CountableCodes.v
```

## Comparison separation audit completed for its three local predicates

The previous turn was verified progress: commits 5e08a2c and 506fe32 were
pushed. HEAD is 506fe328ee59dda401f038d36031755748d0ac84. This continuation
extends BoundedComparison.v, with source/docs/evidence uncommitted and user
logs/ preserved.

New proofs: graph_bounded_separation, successor_bounded_separation, and

    bounded_comparison_bijection :
      (forall P : Prop, P \/ ~ P) -> forall A B f g : Ens,
      injection A B f -> injection B A g ->
      bijection A B (graph_by_formula A B f g).

All three Comp predicates local to CantorBernstein.v now have bounded syntax
certificates and equality proofs. The final theorem retains explicit excluded
middle. Imported constructions, first-order BZC derivability and the original
PTS soundness theorem are NOT thereby proved.

Both incremental builds, a fresh isolated build, recursive kernel check and
full local CI exited 0. Seven module assumption reports (three new) are closed;
fresh build has 43 closed reports including dependencies. Library-wide kernel
audit lists imported functional_extensionality_dep and no unsafe settings.
All 104 CI stages passed. Commands and raw logs are retained in
verification/bounded-gluing-2026-10-14/COMMANDS.md.

Next goal: formulate independent GCH/cardinal-comparison principles and prove
the exact cardinal-code classification needed for eligible-witness
nonemptiness, rather than assuming product coding. Coherent choice,
hierarchy identification and original PTS soundness remain open. Model-first
ordering remains in force. Next exact inspection command:

```sh
sed -n '1,240p' ZFC_model/BoundedBijections.v
sed -n '1,220p' ZFC_model/CardinalHierarchy.v
```

## Bounded comparison region verified; previous checkpoint pushed

Commit 5e08a2c (`ZFC model: prove product bounds and Schroeder-Bernstein`)
was created and pushed to origin/main successfully. No index lock existed;
no lock removal was necessary. Historical permission failures below are resolved.

BoundedComparison.v now gives scoped bounded formulas for the base, closed
subsets, and least comparison region, and proves that separation with the
region formula is extensionally equal to the region in CantorBernstein.v.
Its four Print Assumptions reports are closed. The comparison theorem itself
still takes excluded middle explicitly. These certificates do not establish
first-order BZC derivability or full model soundness.

Incremental builds exited 1,1,0,1,0 (syntax, binder inference, then an iff
direction error, all fixed without weakening statements). Fresh isolated build
and recursive kernel check exited 0. Fresh build printed 40 closed reports
including dependencies; library-wide kernel audit lists imported
functional_extensionality_dep, with no unsafe settings. Local CI passed all
104 stages, including pristine upstream, exit 0. Exact commands and raw logs:
verification/bounded-comparison-2026-10-14/COMMANDS.md.

Current checkpoint adds only the bounded-comparison source, build/CI wiring,
documentation and verification evidence; user logs/ remain untouched. Commit
message: `ZFC model: certify bounded separation for the comparison region`.

Next foundation goal: bounded certificates for the successor subset and
glued comparison graph. Next mathematical goal: exact cardinal-code
classification under independently stated GCH/choice principles, hence
eligible-witness nonemptiness. Coherent selection, hierarchy identification,
BZC derivability and original PTS typing soundness remain open. Preserve the
model-first ordering from FOUNDATIONS.md.
Next exact check after extending the certificates:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedComparison.vo
```

## Commit retry and comparison audit correction

The previous turn was progress: it completed the interrupted CI run (103
stages). Current permissions allow retrying the already requested commit.
Audit correction: the earlier record claimed a CantorBernstein kernel check
without a retained log or observed command. Ran that check now against the
isolated compiled module: exit 0, no axioms or unsafe settings. Excluded middle
remains an explicit theorem parameter, despite the closed global assumptions.
The exact command and log are appended to the comparison verification record.
Prepare `ZFC model: prove product bounds and Schroeder-Bernstein` from parent
34b85debaf46290aedc12632245db26717112b26. User logs/ are excluded.

## Cardinal comparison checkpoint verified; commit environment blocked

CantorBernstein.v constructs Schroeder--Bernstein from two set-graph
injections, with excluded middle an explicit theorem premise. CartesianMaps
and PowersetSquares supply the all-rank upper bound described below. Targeted
build/kernel checks passed. A complete rerun of local CI passed all 103
stages (result retained under verification/cantor-bernstein-2026-10-14/).

The requested commit could not be created: Git failed to create
.git/index.lock with `Operation not permitted`; `.git/index.lock` does not
exist, so this is repository permission state rather than a stale lock. Source
and documentation changes remain in the worktree. Do not claim a commit until
the index becomes writable.

Next proof goal: use the comparison theorem with the all-rank embedding bound
to formulate exact GCH/cardinal-code assumptions and prove eligible-witness
nonemptiness. The theorem currently exposes classical logic explicitly; its
bounded-formula translation remains outstanding. Original PTS interpretation
and soundness are still not proved.

## All-rank decoded dependent-product upper bound checked

Previous turn made progress on countable pairing and its exponent bound.
CartesianMaps.v now builds actual Cartesian graph injections; PowersetSquares.v
uses disjoint tags to propagate square absorption through every powerset
carrier. The resulting model-specific theorem is:

    decoded_dependent_product_bound : forall m n a b,
      IN a (U m) ->
      (forall x, IN x (decode a) -> IN (b x) (U n)) ->
      embeds (dependent_product (decode a) (fun x => decode (b x)))
        (carrier (Nat.max (S m) n)).

This proves the actual upper bound uniformly, without GCH, choice, or supplied
fiber injections. Two CartesianMaps and nine PowersetSquares reports are
closed. The theorem does not identify the product with an available code;
GCH/cardinal classification and coherent bijection selection remain unproved.
Hierarchy identification/BZC derivability and original PTS typing soundness
also remain unproved. The goal stays active with model-first ordering.

CartesianMaps incremental build exited 0. PowersetSquares iterations exited
1,0,0,0: the failure was a tactic branch count in tagged_pair, fixed with
explicit branches without changing statements. Fresh build exited 0 and
printed 118 closed reports including dependencies. Recursive kernel check
exited 0 with imported functional_extensionality_dep in its library-wide
summary, no unsafe settings. Full local CI including pristine upstream passed
all 102 stages, exit 0. Commands/raw logs including failure retained under
verification/powerset-squares-2026-10-14/COMMANDS.md.

HEAD remains 34b85debaf46290aedc12632245db26717112b26. The prior exponent
lemmas and this turn's code/docs/logs are uncommitted. User logs/ preserved;
no new commit or push performed.

Next proof goal: obtain exact available cardinal codes from the upper bound.
Fix a precise GCH statement independently of the PTS target, derive the
classification of sets embeddable into each finite powerset carrier, and
prove eligible-witness nonemptiness. This still requires cardinal comparison
and a finite/countable base classification; do not insert the result as a
model assumption. Next inspection command:
`rg -n 'GCH|choice|cardinal|well.order|Schroeder|Bernstein' ZFC_model vendor/zfc docs/direct-r-handoff`.
Next build command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/PowersetSquares.vo`.

## Witness/pairing checkpoint committed; countable exponent bound proved

Committed accumulated work as 34b85debaf46290aedc12632245db26717112b26,
`ZFC model: construct bounded witnesses and countable pairing`. No push
requested/performed; user logs/ excluded and preserved.

Continued afterward with three theorems in CountablePairing.v. Any K that
absorbs its Cartesian square also absorbs the subset-valued function space
K -> P(K) into P(K). Instantiating the new pairing gives:

    countable_subset_exponent :
      embeds (dependent_product omega_codes (fun _ => Power omega_codes))
        (Power omega_codes).

The dependent version accepts explicitly supplied fiber injections. It does
not assume or construct those injections globally. All three new reports are
closed. Incremental build and rebuild in the isolated directory exited 0;
recursive kernel check exited 0, reporting no axioms or unsafe settings.
The seven module reports are closed; additional dependency reports appear in
the rebuild log. Exact commands/raw logs appended to the pairing checkpoint.
Full 100-stage CI covers the committed checkpoint; the later exponent lemmas
received targeted rebuild/kernel checks. Current source/doc/log changes since
the commit are uncommitted.

Next proof: propagate Cartesian-square absorption through powersets by
encoding two subsets with disjoint tags, then derive all-rank Cartesian and
subset-exponent bounds. GCH classification/nonemptiness, coherent choice,
hierarchy identification, and original PTS soundness remain open. Next command
(README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CountablePairing.vo`.

## Countable Cartesian square bijection checked; commit requested

The previous turn constructed bounded eligible-witness sets. This turn adds
CountablePairing.v and proves an actual set-graph bijection:

    countable_pairing_bijection :
      bijection (Prod omega_codes omega_codes) omega_codes pairing_graph.

Four new reports closed. Incremental and fresh builds exited 0; fresh build
printed 51 closed reports including dependencies. Recursive kernel check
exited 0, reporting no axioms or unsafe settings. Full local CI including
pristine upstream passed all 100 stages, exit 0. Commands and raw logs:
verification/countable-pairing-2026-10-14/COMMANDS.md.

User requests commit, then further proof. Prepare accumulated witness and
pairing work as `ZFC model: construct bounded witnesses and countable pairing`.
Parent HEAD 5f88ec1c1c5048b6049fa5f5a1ef3c3ee0f8a0c8. User logs/ preserved
and excluded. Next proof combines this pairing with subset_function_embeds
and powerset_embeds to bound the countable subset-valued function space.
All-rank cardinal estimates, GCH classification/nonemptiness, coherent
selection, hierarchy identification, and original PTS soundness remain open.
Next command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CountablePairing.vo`.

## Bounded eligible-bijection set constructed and checked

Previous turn was progress: committed hierarchy infrastructure and proved
coding witness bounds. This turn adds BoundedBijections.v: bounded formulas
equivalent to graph bijection, and an eligible-witness set with exact membership
specification, completeness of the graph bound, and rank bound P^8(W).
Six new theorem reports are closed. No choice, GCH, cardinal classification,
or model soundness is assumed or proved by this construction.

Incremental builds exited 0,1,0,1,0. Failures were missing imports for the rank
definitions and an uninferred domain parameter, repaired explicitly. Fresh
build exited 0 with 108 closed reports including dependencies. Recursive
kernel check exited 0; its library-wide summary lists imported functional
extensionality, with no unsafe settings. Full CI including pristine upstream
passed all 99 stages, exit 0. Commands/raw logs including failures are in
verification/bounded-bijections-2026-10-14/COMMANDS.md.

HEAD remains 5f88ec1c1c5048b6049fa5f5a1ef3c3ee0f8a0c8. New certificates,
post-commit witness lemmas and handoff/log updates are uncommitted; user logs/
preserved. No additional commit/push requested or performed in this turn.

Next goal: prove the cardinal bound and classification that make eligible
sets nonempty for the intended targets. Start with Cartesian-product estimates
for the concrete countable/powerset carriers; then the exponent bound and
GCH classification, before coherent set choice. This is still only one part
of full original PTS soundness; supplied hierarchy identification and the
typing interpretation remain open. Next inspection command:
`cat ZFC_model/SubsetFunctions.v; cat ZFC_model/CardinalHierarchy.v; rg -n 'pair|inject|cancel' /Users/akuklev/.local/share/pts-rk-ci/opam/pts-rk-ci/lib/coq/user-contrib/Stdlib/Arith/Cantor.v`.
Next verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedBijections.vo`.

## Checkpoint committed; coding witness bounds proved afterward

Committed accumulated work as 5f88ec1c1c5048b6049fa5f5a1ef3c3ee0f8a0c8,
`ZFC model: bound constructions in a supplied hierarchy`. No push requested
or performed. User logs/ excluded and preserved.

Continued with coding_bijection_rank_bound and coding_witness_rank_bound in
SuppliedHierarchy.v: if W is transitive and A,K are subsets of W, every
bijection f : A -> K lies in P^4(W), and Couple K f lies in P^7(W). This
provides an explicit ambient bound for eligible witnesses; their existence
and coherent selection still need proof. Both new assumption reports are
closed. Incremental build and rebuild in the isolated previous fresh directory
passed, as did recursive kernel checking. All ten reports in the rebuilt
module are closed; library-wide check still lists imported functional
extensionality. Raw logs and commands appended to the same verification
directory. Full 98-stage CI covers the committed checkpoint, not these two
subsequent lemmas; these received targeted rebuild/kernel checks.

Current diff after the commit contains these witness lemmas and handoff/log
updates. Next goal: formalize the bounded eligible-witness predicate and its
set; then prove cardinal classification/nonemptiness using the intended GCH
hypothesis before choosing witnesses. Full original PTS soundness remains
unproved. Next command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SuppliedHierarchy.vo`.

## Supplied hierarchy closure checked; checkpoint commit requested

SuppliedHierarchy.v characterizes a supplied H by membership in some finite
powerset iterate of a base W. No hierarchy existence axiom or sup-indexed
collection is introduced. From this characterization and the stated base
conditions, it proves transitivity, powerset closure, and membership of
carriers, code universes, decoded carriers, decoding graphs and dependent
products in H. Identification of W with V_omega and H with V_{omega+omega}
remains unproved. Cardinal coding and original PTS typing soundness remain
unproved; the goal is active, with the corrected model-first ordering.

Incremental build, fresh build and recursive kernel check exited 0. Eight
new reports are closed; fresh dependencies printed 96 closed reports. The
kernel library-wide summary lists imported functional_extensionality_dep;
no unsafe settings were reported. Full local CI passed all 98 stages,
including newly added CodeHierarchyBounds and SuppliedHierarchy stages.
The preceding code-hierarchy checkpoint actually had 96 stages and nine new
reports; its inaccurate documentation has been corrected against raw logs.
Exact commands and logs: verification/supplied-hierarchy-2026-10-14/COMMANDS.md.

User requests committing and then continuing proof. Prepare accumulated ZFC
model work under `ZFC model: bound constructions in a supplied hierarchy`.
Parent HEAD is 5872c848ea9d92339107685f3fd9396010d72218; user logs/ excluded.
Next proof: bound the set of eligible coding bijections inside H so ordinary
set choice has a concrete witness bound. Cardinal classification/nonemptiness
must still be proved; a bound does not assert eligible bijections exist.
Next command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SuppliedHierarchy.vo`.

## Concrete decoding graph bounds checked

Previous turn proved bounded dependent-product equivalence. This turn adds
CodeHierarchyBounds.v. It proves omega_codes transitive, U_i subset of the
base carrier, decoded members of U_i subset of carrier i, and:

    decoding_graph_rank_bound : forall i,
      IN (decoding_graph i) (carrier (5 + i)).

The decoding graph is typed into the existing dependent product and its beta
law is checked. All nine new theorem reports are closed. This supplies an
actual rank bound for the model-specific graph, but not a first-order BZC
existence proof, coherent cardinal coding, GCH classification, or PTS
typing/soundness theorem.

Build evidence: incremental CodeHierarchyBounds builds exited 1,1,1,0; the
failures were argument inference and a level rewrite, all repaired without
weakening statements. Fresh build exited 0 with 88 closed reports including
dependencies. Recursive rocq check exited 0; its summary lists imported
functional_extensionality_dep but no unsafe fixpoints/type-in-type/assumed
positivity. Full local CI including pristine upstream passed all 96 stages,
exit 0. Logs and exact commands are in
verification/code-hierarchy-2026-10-14/COMMANDS.md.
Correction: that CI run did not yet include a separate CodeHierarchyBounds
stage; its fresh build and kernel check did cover it. The supplied-hierarchy
checkpoint adds the missing CI stage.
HEAD remains 5872c848ea9d92339107685f3fd9396010d72218; all work remains
uncommitted and user logs/ are preserved.

Next goal: formulate the supplied V_{omega+omega} hierarchy explicitly and
prove that the finite-rank code and graph bounds fit inside it; then audit the
remaining cardinal/GCH coding and finally the original PTS typing soundness.
Do not claim model soundness from these bounds. Next inspection command:
`rg -n 'Code|El|carrier|decode|Generator|sound' ZFC_model theories`.

## Bounded dependent function spaces checked

Previous turn made progress on family ranges. BoundedProducts.v now gives
a five-variable bounded formula for totality, fiber membership and uniqueness,
and proves equality of the resulting space with the original construction:

    bounded_product_equivalence : forall A W f,
      IN f (dependent_product A (fun _ => Power W)) ->
      EQ (bounded_product A W f) (dependent_product A (apply_set f)).

bounded_product separates Power (Prod A W) by the explicit formula, with no
indexed family_range or unrestricted function_laws in its definition. All
four new theorem assumption reports are closed. The input family graph is
supplied, not postulated as part of an allegedly completed model.

Both incremental builds exited 0. Fresh build exited 0 with 20 closed reports
including dependencies. Recursive rocq check exited 0, with imported
functional_extensionality_dep in its library-wide summary but closed reports
for the new theorems. No unsafe fixpoints, type-in-type or assumed positivity.
Full local CI including pristine upstream passed all 96 stages, exit 0.
Exact commands/raw logs: verification/bounded-products-2026-10-14/COMMANDS.md.
HEAD remains 5872c848ea9d92339107685f3fd9396010d72218; new and preceding
work remain uncommitted. User logs/ preserved; no commit or push performed.

Next goal: connect bounded constructions to the actual code/carrier hierarchy.
First establish concrete bounds for the code universes and decoding-family
graphs in a supplied V_{omega+omega} hierarchy, without assuming those graphs
exist or treating Ens.sup as a BZC certificate. Cardinal product classification,
coherent coding, and original PTS typing soundness still remain. Only after
that supplied-hierarchy model is sound pursue removing hierarchy existence.
Next inspection command:
`sed -n '1,220p' ZFC_model/CodeUniverses.v; cat ZFC_model/CardinalHierarchy.v; cat ZFC_model/HierarchyBounds.v`.
Next verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedProducts.vo ZFC_model/CardinalHierarchy.vo`.

## Bounded family-range reconstruction checked

Previous turn made progress by proving hierarchy rank bounds. This turn adds
BoundedFamilies.v: explicit bounded Formula 3, separation-based range of a
set-coded family, equivalence to the old indexed range, and range/union bounds.

    bounded_family_range_equivalence : forall W A f,
      IN f (dependent_product A (fun _ => Power W)) ->
      EQ (bounded_family_range W A f) (family_range A (apply_set f)).

The new definition has no indexed sup. Five new assumption reports are closed.
The premise types an input family graph; it does not construct the graphs
needed by model soundness or certify function_laws as a bounded predicate.
The supplied-hierarchy model remains the immediate goal; full soundness and
the later interpretation without hierarchy existence are both unfinished.

Incremental builds exited 1,0: missing Ens annotation in range_env was fixed
without changing any theorem. Fresh build exited 0, printing 21 closed reports
including dependencies. Recursive rocq check exited 0; its library-wide summary
lists imported functional_extensionality_dep, while the theorem reports are
closed. No unsafe fixpoints, type-in-type or assumed positivity reported.
Full local CI including pristine upstream passed all 95 stages (exit 0).
Exact commands and raw logs, including failure, are retained in
verification/bounded-families-2026-10-14/COMMANDS.md.

HEAD remains 5872c848ea9d92339107685f3fd9396010d72218. Prior dirty work and
user logs/ are preserved. No commit/push performed.
Next proof goal: replace function_laws for a set-coded family by totality,
fiber membership and uniqueness quantified only over supplied domain/value
bounds, then certify it in Bounded.Formula. Ambient Power (Prod A W) supplies
the graph-element bound; the family graph supplies fiber lookup. Prove
equivalence before replacing the existing dependent_product construction.
Next inspection command:
`sed -n '1,170p' ZFC_model/SetFunctions.v; sed -n '1,150p' ZFC_model/BoundedFamilies.v`.
Next verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFamilies.vo`.

## Hierarchy rank bounds checked; bounded reconstruction next

Previous turn was progress: it corrected the foundation ordering and retained
the bounded-formula build evidence. This turn adds HierarchyBounds.v with
actual rank bounds for pairs, products, family ranges, graph abstraction and
dependent function spaces. Uniform theorem:

    dependent_product_level_bound : forall W n A B,
      transitive_set W -> INC A (iterated_power W n) ->
      (forall x, IN x A -> INC (B x) (iterated_power W n)) ->
      IN (dependent_product A B) (iterated_power W (5 + n)).

The domain/fiber bounds are ordinary input bounds, not assumed PTS model
closure. All eight new Print Assumptions reports are closed. This does NOT
yet replace arbitrary Ens-indexed families by first-order bounded definitions,
establish the V_{omega+omega} hierarchy, or prove typing soundness.

Incremental builds both exited 0. Fresh build exited 0 with 42 closed reports
including dependencies; recursive rocq check exited 0, reporting no axioms or
unsafe settings. Full local CI, including pristine upstream, passed all 94
stages, exit 0. Exact commands and raw logs are retained under
verification/hierarchy-bounds-2026-10-14/COMMANDS.md.
Fresh command: `opam exec --switch=pts-rk-ci -- timeout 180 dune build
--build-dir /tmp/pts-rk-hierarchy-fresh.DtcwD8 --display=short --no-buffer
ZFC_model/HierarchyBounds.vo`.

HEAD remains 5872c848ea9d92339107685f3fd9396010d72218; all previous dirty
work and user logs/ are preserved. No commit or push performed.
Next goal: use these bounds to reconstruct family ranges and dependent
function spaces from set-coded families using bounded formulas. In particular,
function_laws still has unrestricted x/y/z quantifiers and B : Ens -> Ens;
do not claim it is a BZC predicate until those are replaced/relativized.
Then connect the constructions to the explicitly supplied hierarchy and
complete cardinal coding and original PTS soundness. Removing hierarchy
existence remains deferred until after soundness.
Next inspection command:
`sed -n '1,180p' ZFC_model/BoundedFormulas.v; sed -n '1,170p' ZFC_model/SetFunctions.v`.
Next build command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/HierarchyBounds.vo ZFC_model/BoundedInverse.vo`.

## Current priority: hierarchy-bounded model and soundness first

The latest user correction supersedes the goal-registration wording below.
First reformulate the existing model in BZC + GCH + existence of
V_{omega+omega} and finish soundness for the original PTS. Use the hierarchy
to bound constructions, replace separation by explicit existence constructions
where possible, and certify boundedness of any remaining separation. Do not
assume hierarchy existence supplies arbitrary subset comprehension. Only
after this model and soundness are finished pursue an interpretation in
BZC + GCH without the hierarchy-existence assumption. FOUNDATIONS.md and
DECISIONS.md record this ordering. Neither milestone is proved.

BoundedFormulas.v and BoundedInverse.v now provide scoped bounded syntax,
correctness for the library's ordered pairs and graph application, and a
bounded separation formula equal to the existing inverse graph. Nine new
Print Assumptions reports are closed. These are Ens semantic equivalences,
not a first-order BZC derivation or completed model soundness.

Verification: incremental builds exited 1,1,0,1,0 (all failures retained).
A fresh build of BoundedInverse.vo and dependencies exited 0, printing 29
closed assumption reports. Recursive rocq check exited 0; its library-wide
summary lists Stdlib functional_extensionality_dep imported through the
syntax dependencies, unlike the closed theorem-specific reports. No unsafe
fixpoints, assumed positivity, or type-in-type were reported. Full local CI
including pristine upstream passed all 93 stages, exit 0. Exact commands and
raw logs are in verification/bounded-formulas-2026-10-14/COMMANDS.md.

HEAD remains 5872c848ea9d92339107685f3fd9396010d72218. This checkpoint,
the prior powerset/subset-function work, and foundation documents remain
uncommitted. Existing user logs/ are preserved; no commit or push performed.

Next goal: specify the supplied V_{omega+omega} hierarchy and show explicit
rank bounds for the existing code/carrier/graph constructions; audit sup/Comp
against those bounds. Do not divert into removing hierarchy existence before
soundness. Product cardinal classification, coherent coding and original PTS
typing interpretation remain required, not assumed model laws.
Next exact inspection command:
`rg -n 'sup|Comp|family_range|iterated_power|Definition U|Definition El' ZFC_model vendor/zfc`.
Next verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedInverse.vo`.

## New active goal: weaker-foundation interpretation, if possible

Historical registration; ordering superseded by the current priority above.

User requests an interpretation in BZC + GCH, rather than full ZFC + GCH,
and a set-sized model in BZC + GCH + existence of V_{omega+omega}.
“GHZ” is provisionally read as GCH. Goal registered as active; neither
target is proved. Exact obligations and the initial foundation audit are
recorded in ZFC_model/FOUNDATIONS.md. Existing soundness work remains required.

This update changes documentation only; no proof/build result is claimed.
Last verified proof baseline remains the 91-stage run below (79 closed
model assumption reports). Those reports do not certify BZC strength.
Existing uncommitted powerset/subset-function work and user logs/ are preserved.
No commit or push requested for this goal-registration turn.

Next task: fix the precise BZC/GCH presentation and audit sup/Comp, hierarchy
uniformity, witness-selection bounds, and the difference between definable
interpretation and set-sized realization. In particular, do not assume that
finite powerset iterations can be collected into a set in the weaker theory.
Next exact source-inspection command:
`rg -n 'sup|Comp|family_range|iterated_power|exists x y' ZFC_model vendor/zfc`.

## Powerset embeddings and subset-function exponent step checked

Committed the previous CountableCodes/CardinalGrowth/CardinalHierarchy
checkpoint as 5872c848ea9d92339107685f3fd9396010d72218,
`ZFC model: prove cardinal growth and uniform decoding bounds`, as requested.
No push requested/performed. New PowersetEmbedding.v and SubsetFunctions.v
work is uncommitted. User-owned logs/ is untouched.

Direct images give an actual injection P(A) -> P(B) from any supplied
injection A -> B. Membership-pair relations inject functions A -> P(B)
into P(A x B). Fiber recovery proves this map injective. Combining with
the previously constructed fiberwise map proves:

    dependent_subset_product_bound : forall A K B enc,
      (forall x, IN x A -> injection (B x) (Power K) (apply_set enc x)) ->
      embeds (dependent_product A B) (Power (Prod A K)).

This constructs the product injection; it does not assume the product
bound. Fiber injections are explicit supplied data, not yet selected for
the cardinal hierarchy. All twelve new Print Assumptions reports are closed.

Incremental builds exited 0,1,0. The failure was uninferred A/B arguments in
flatten_injective, repaired explicitly without changing statements. The
final combined theorem was checked in the fresh build: exit 0, all 79
model reports closed:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir
/tmp/pts-rk-zfc-powerset-fresh.vQKhh9 --display=short --no-buffer
ZFC_model/PowersetEmbedding.vo ZFC_model/SubsetFunctions.vo
ZFC_model/CardinalHierarchy.vo ZFC_model/CodedFunctions.vo`.
Recursive kernel check exited 0, no axioms:
`opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o
-Q /tmp/pts-rk-zfc-powerset-fresh.vQKhh9/default/vendor/zfc ZFC
-Q /tmp/pts-rk-zfc-powerset-fresh.vQKhh9/default/ZFC_model PTSrkModel
PTSrkModel.PowersetEmbedding PTSrkModel.SubsetFunctions
PTSrkModel.CardinalHierarchy PTSrkModel.CodedFunctions`.
Full local CI, including pristine upstream, exited 0 with all 91 stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-powerset-final"
bash tools/check-local-ci.sh`. Exact commands/logs, including the failed
iteration, are in verification/powerset-embedding-2026-10-14/.

Full PTS soundness is still NOT finalized. Next cardinal step: prove the
Cartesian-product estimates for the countable/powerset carriers and use
the new subset-function encoding to obtain the rank-indexed exponent bound.
Stdlib.Arith.Cantor is installed locally and can supply natural pairing for
the countable base (not yet imported or used). Exact GCH classification,
coherent selection of cardinal-coding bijections and original PTS typing
interpretation remain unproved; none is asserted as an axiom or model field.
Next exact verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer ZFC_model/PowersetEmbedding.vo ZFC_model/SubsetFunctions.vo
ZFC_model/CardinalHierarchy.vo ZFC_model/CodedFunctions.vo`.

## Concrete growing carriers and all-rank decoding bound checked

Parent HEAD is 91156df3c7fb387f300a83993b4710fd45c81a35. The user subsequently
requested committing this work; prepared as `ZFC model: prove cardinal growth
and uniform decoding bounds`, including CountableCodes, CardinalGrowth and
CardinalHierarchy. No push requested.
User-owned logs/ is untouched.

CardinalGrowth.v proves Cantor non-surjectivity and no injection Power A -> A,
constructs singleton injections, and proves strict growth of all finite
powerset iterates. CardinalHierarchy.v now instantiates the previously
arbitrary infinite carriers as carrier i = iterated_power omega_codes i.
The decoding bound is proved uniformly for all ranks, not by finite tests:

    decoding_bound : forall i a, IN a (U i) -> embeds (decode a) (carrier i).
    carrier_strict : forall i j, i < j -> ~ embeds (carrier j) (carrier i).
    concrete_sort_axiom : forall i,
      IN (repr (sort i)) (decode (repr (sort 0))).

All fourteen new Print Assumptions reports are closed. No choice, excluded
middle, GCH, assumed carrier bounds or PTS model laws were added as axioms.
These are concrete powerset representatives, NOT yet proved to be alephs.
Exact cardinal codes for products and the GCH argument are still missing;
the hierarchy alone is not asserted to form a complete PTS model.

Both incremental builds exited 0. Fresh dependency build exited 0; all 67
model assumption reports are closed:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir
/tmp/pts-rk-zfc-growth-fresh.9Nx7jR --display=short --no-buffer
ZFC_model/CardinalHierarchy.vo ZFC_model/CodedFunctions.vo`.
Recursive kernel check exited 0, no axioms:
`opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o
-Q /tmp/pts-rk-zfc-growth-fresh.9Nx7jR/default/vendor/zfc ZFC
-Q /tmp/pts-rk-zfc-growth-fresh.9Nx7jR/default/ZFC_model PTSrkModel
PTSrkModel.CardinalHierarchy PTSrkModel.CodedFunctions`.
Full local CI, including pristine upstream, exited 0 with all 89 stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-growth-final"
bash tools/check-local-ci.sh`. Commands and exact logs are retained in
verification/cardinal-growth-2026-10-14/. Raw compiler logs have trailing
whitespace and are preserved verbatim; source/document checks are separate.

The requested final PTS soundness theorem remains unproved. Next major
obligations: the GCH cardinal classification and exponent bound that ensure
each dependent product has an exact represented cardinal, coherent selection
of its coding bijection, and original PTS context/term interpretation with
substitution, beta compatibility and typing soundness. Do not replace this
by a record of assumed model laws or silently drop the GCH/product obligations.
Next exact verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer ZFC_model/CardinalHierarchy.vo ZFC_model/CodedFunctions.vo`.

## Actual counting bijections and rank-zero decoding bound checked

Committed prior product-embedding work as
91156df3c7fb387f300a83993b4710fd45c81a35, `ZFC model: prove dependent product
embedding`, as requested. No push requested/performed. New CountableCodes.v
work below is uncommitted. User-owned untracked logs/ remains untouched.

CountableCodes.v constructs a concrete graph bijection from each U_i to the
set omega_codes of singleton numerals. The explicit numbering is bijective
on permitted codes, unlike the previous possibly repeating enumeration.
Forward evaluation and inverse round trip are proved. Finite carriers also
inject into omega_codes. Fixing the rank-zero infinite carrier to this set
proves the decoding bound for ALL members of U_0, with arbitrary higher
carriers. This is not an assertion that those higher carriers are alephs.

Exact principal types:

    counting_bijection : forall i,
      bijection (U i) omega_codes (counting_graph i).
    rank_zero_decoding_bound : forall higher a,
      IN a (U 0) -> embeds (El (countable_zero higher) a) omega_codes.

Ten new Print Assumptions reports are closed; no axiom, assumed PTS model
law, choice premise or unsafe checking change was introduced. No kernel
rules changed. omega_codes is a countably infinite representative, not a
formal von Neumann initial ordinal construction.

Both incremental builds exited 0. Fresh dependency build exited 0, with all
53 assumption reports closed:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir
/tmp/pts-rk-zfc-countable-fresh.yqh2JU --display=short --no-buffer
ZFC_model/CountableCodes.vo ZFC_model/CodedFunctions.vo`.
Recursive kernel check exited 0, no axioms:
`opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o
-Q /tmp/pts-rk-zfc-countable-fresh.yqh2JU/default/vendor/zfc ZFC
-Q /tmp/pts-rk-zfc-countable-fresh.yqh2JU/default/ZFC_model PTSrkModel
PTSrkModel.CountableCodes PTSrkModel.CodedFunctions`.
Full local CI, including pristine upstream, exited 0, all 87 stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-countable-final"
bash tools/check-local-ci.sh`. Exact commands and logs are retained in
verification/countable-codes-2026-10-14/.

The requested finalized PTS model soundness proof remains unproved. Next
major construction: actual uncountable finite-index aleph carriers, their
cardinal comparison theory, precise GCH and the product exponent bound.
Coherent choice of cardinal-coding bijections and the original PTS context/
term interpretation with substitution and beta compatibility still follow.
No local counting/base-rank result substitutes for those obligations.
Next exact verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer ZFC_model/CountableCodes.vo ZFC_model/CodedFunctions.vo`.

## Product-cardinality first step checked; full soundness NOT finalized

Committed the prior checkpoint as 5c8476ed81316b5ba3cb259ffd4c4d170170705f,
`ZFC model: prove bijection inverses and coded beta`, as requested. No push
was requested or performed. Continued ProductEmbedding.v work below is
prepared for the subsequently requested commit
`ZFC model: prove dependent product embedding`. No push requested.
User-owned untracked logs/ remains untouched.

New result: actual fiber injections into K induce an explicitly constructed
set injection from the dependent product into the function set A -> K.
Neither that injection nor the resulting bound is a hypothesis. The graph
family variant derives its extensionality from concrete set application.

Exact theorem type:

    dependent_product_injection_from_graph : forall A K B enc,
      (forall x, IN x A -> injection (B x) K (apply_set enc x)) ->
      injection (dependent_product A B) (dependent_product A (fun _ => K))
        (product_injection A B (apply_set enc)).

All seven new Print Assumptions reports are closed. No new axiom, assumed
model law, choice premise or kernel rule change. The supplied fiber
injections still need to be constructed/selected in the cardinal proof.

First incremental build exited 0. Fresh build including the graph-family
variant and all six model modules exited 0; 43 closed reports:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir
/tmp/pts-rk-zfc-product-fresh.leuaTw --display=short --no-buffer
ZFC_model/ProductEmbedding.vo ZFC_model/CodedFunctions.vo
ZFC_model/CodeUniverses.vo`.
Recursive kernel check exited 0, no axioms:
`opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o
-Q /tmp/pts-rk-zfc-product-fresh.leuaTw/default/vendor/zfc ZFC
-Q /tmp/pts-rk-zfc-product-fresh.leuaTw/default/ZFC_model PTSrkModel
PTSrkModel.ProductEmbedding PTSrkModel.CodedFunctions PTSrkModel.CodeUniverses`.
Full local CI, including pristine upstream, exited 0 with all 86 stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-product-final"
bash tools/check-local-ci.sh`. Commands and exact logs retained in
verification/product-embedding-2026-10-14/.

The user's requested final soundness theorem is still unproved. The actual
finite-index aleph hierarchy, precise GCH and exponent bound, coherent
selection of coding bijections, context/term interpretation, substitution
and beta compatibility, and original Typing.typ/RankSorts soundness remain.
The vendored three-file set library supplies none of the missing cardinal
machinery. Do not equate the checked local coded-beta theorem or today's
product injection with completion of that model proof.
Next exact verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer ZFC_model/ProductEmbedding.vo ZFC_model/CodedFunctions.vo
ZFC_model/CodeUniverses.vo`.

## Concrete bijections and coded beta checked

Committed the previous code-universe checkpoint as
072c6d96c31557ae3c36563d8466c53a1c54f6f4, `ZFC model: construct countable code
universes`, as requested. Did not push. Continued proof work below is
prepared for the subsequently requested commit
`ZFC model: prove bijection inverses and coded beta`; user-owned untracked
logs/ remains untouched. No push requested.

SetBijections.v constructs inverse graphs by separation, with inverse typing,
bijectivity and both evaluation round trips. Concrete identity/composition
graphs prove equinumerosity reflexive/symmetric/transitive. These are set
constructions, not choice postulates. CodedFunctions.v proves typed encoding,
decoding, application, extensionality, coded beta and empty-fiber transport
for a supplied bijection from a dependent function set to a carrier K.
There are 15 new closed Print Assumptions reports (9+6).

Exact principal theorem types:

    coded_beta : forall A B K f body x,
      bijection (dependent_product A B) K f ->
      family_extensional body ->
      (forall y, IN y A -> IN (body y) (B y)) -> IN x A ->
      EQ (coded_application A B K f (encode_function f A body) x) (body x).
    empty_fiber_forces_empty_code : forall A B K f x,
      bijection (dependent_product A B) K f ->
      IN x A -> EQ (B x) Vide -> EQ K Vide.

No existence or coherent selection of coding bijections is claimed. These
are local lemmas about ordinary bijections, not a PTS soundness statement
with missing model obligations hidden in its hypotheses. No new axioms,
unsafe checking changes, choice premise or PTS rule changes.

Baseline targeted build exited 0. Incremental builds 1,2,3,4 exited 0,1,1,0;
the failures were inference of the graph body in the composition proof,
fixed by explicit arguments, without weakening statements. Fresh dependency
build exited 0, all 36 model-module assumption reports closed:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir
/tmp/pts-rk-zfc-bijections-fresh.c1GfHf --display=short --no-buffer
ZFC_model/CodedFunctions.vo ZFC_model/CodeUniverses.vo`.
Recursive kernel check exited 0, with no axioms:
`opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o
-Q /tmp/pts-rk-zfc-bijections-fresh.c1GfHf/default/vendor/zfc ZFC
-Q /tmp/pts-rk-zfc-bijections-fresh.c1GfHf/default/ZFC_model PTSrkModel
PTSrkModel.CodedFunctions PTSrkModel.CodeUniverses`.
Final full local CI, including pristine upstream, exited 0, all 85 stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-bijections-final"
bash tools/check-local-ci.sh`. All commands and logs, including both failed
iterations, are retained in verification/set-bijections-2026-10-14/.

Remaining goal: actual finite-index aleph carriers, precise GCH and the
dependent-product cardinal bound, then existence and coherent selection of
coding bijections. Context/term semantics, substitution/beta compatibility
and soundness for original Typing.typ/RankSorts remain unproved.
Next exact verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer ZFC_model/CodedFunctions.vo ZFC_model/CodeUniverses.vo`.

## Code universes and extensional decoding now constructed

Committed and normally pushed the preceding application milestone as
15f587a98055982615af5cb270ea67f0ec5a440d, `ZFC model: prove concrete graph
application`; origin/main matched HEAD after push. The user subsequently
requested committing this code-universe checkpoint, followed by further
proof work; prepared as `ZFC model: construct countable code universes`.
No push requested for this checkpoint. User-owned logs/ remains untouched.

New ZFC_model/CodeUniverses.v constructs distinct finite/infinite/sort codes,
the actual sets U_i, exact membership, monotonicity and strict growth, and
an explicit enumeration by nat. Extensional decoding El is a concrete
union of matching code values, not an assumed model field. Finite carriers
and sort decoding are constructed. Infinite carriers remain an explicit
arbitrary parameter nat -> Ens, with no cardinality assumptions or claims.
The paper's aleph hierarchy is NOT yet constructed by this module.

Exact checked public theorem types (K : nat -> Ens):

    universe_enumeration : forall i,
      EQ (U i) (sup nat (enumerate_universe i)).
    decode_repr : forall K c, EQ (El K (repr c)) (code_value K c).
    sort_axiom : forall K i, IN (repr (sort i)) (El K (repr (sort 0))).
    decoded_sort_product_empty : forall K j g,
      ~ IN g (dependent_product (El K (repr (sort j))) (El K)).

The last theorem concerns ordinary decoded function graphs, not yet the
denotation of the original PTS Bottom term. All ten new Print Assumptions
reports are closed under the global context. No new axioms, assumed model
laws, unsafe checking changes or PTS rule changes.

Incremental CodeUniverses.vo builds 1/2/3 exited 1 (missing le_dec import,
ZFC/Stdlib exist-name collision, elimination into the library's Set-valued
empty type); build 4 exited 0. Statements were not weakened. Fresh build
including strict-growth proof and all three local model modules exited 0:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir
/tmp/pts-rk-zfc-codes-fresh.Pj0oAh --display=short --no-buffer
ZFC_model/CodeUniverses.vo ZFC_model/SetApplication.vo`.
Log /tmp/pts-rk-zfc-codes-fresh.log has 21 closed reports (5+6+10).
Recursive kernel check exited 0 with no axioms:
`opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o
-Q /tmp/pts-rk-zfc-codes-fresh.Pj0oAh/default/vendor/zfc ZFC
-Q /tmp/pts-rk-zfc-codes-fresh.Pj0oAh/default/ZFC_model PTSrkModel
PTSrkModel.CodeUniverses PTSrkModel.SetApplication`.
Final full local CI, including pristine upstream, exited 0 with 83 stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-codes-final"
bash tools/check-local-ci.sh`. Exact commands and all logs, including the
three failed iterations, are in verification/code-universes-2026-10-14/.

Next proof obligation: construct the finite-index aleph hierarchy and a
precise GCH proposition, prove the dependent-product cardinal bound, then
construct coherent coding bijections. No bound properties of K have been
assumed. Context/term interpretation, substitution/beta semantics and
original-typing soundness remain unfinished. Next exact verification command
(README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer ZFC_model/CodeUniverses.vo ZFC_model/SetApplication.vo`.

## Set-model continuation: functional application checked; soundness unfinished

Parent HEAD: 3345146540c54a05c4c1187bcc603d509742586d. User requests finishing
set-model soundness, explicitly placing that work in scope. Initial worktree
had only user-owned untracked logs/, which remains untouched. The user
subsequently requested commit and push; this checkpoint is prepared for
`ZFC model: prove concrete graph application` on main, then normal push.

Inspection: ZFC_model previously contained only SetFunctions.v and README,
not a term interpretation or soundness theorem awaiting a final proof.
The paper's model is specifically in ZF+GCH. The pinned ZFC subset has no
finite-aleph/GCH infrastructure. No missing model laws have been postulated.

Implemented SetApplication.v, now included in dune and a new full-CI stage.
Its concrete total application is Union of a separated value fiber bounded
by three unions of the graph (the library has a non-Kuratowski pair encoding).
Checked public results, with EQ/IN from the original ZFC library:

- apply_set_extensional: EQ g h -> EQ x x' -> EQ (apply_set g x) (apply_set h x').
- apply_set_beta: family_extensional f -> IN x A ->
  EQ (apply_set (graph A f) x) (f x).
- apply_set_typed: IN g (dependent_product A B) -> IN x A ->
  IN (apply_set g x) (B x).
- apply_set_spec: same premises -> application g x (apply_set g x).
- apply_set_eta: IN g (dependent_product A B) -> EQ (graph A (apply_set g)) g.
- dependent_product_extensionality: g,h in dependent_product A B and
  pointwise EQ of their applications on A imply EQ g h.

Both incremental builds exited 0. Fresh dependency build exited 0 with all
11 Print Assumptions reports closed (five old, six new):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir
/tmp/pts-rk-zfc-fresh.glVoYd --display=short --no-buffer
ZFC_model/SetApplication.vo`; /tmp/pts-rk-zfc-fresh.log.
Recursive kernel check exited 0:
`opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o
-Q /tmp/pts-rk-zfc-fresh.glVoYd/default/vendor/zfc ZFC
-Q /tmp/pts-rk-zfc-fresh.glVoYd/default/ZFC_model PTSrkModel
PTSrkModel.SetApplication`; /tmp/pts-rk-zfc-kernel.log.
Baseline full local CI, including pristine upstream, exited 0;
/tmp/pts-rk-zfc-baseline.log. No new axioms or PTS rule changes.
Final full local CI exited 0 with all 82 stages passing:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-application-final"
bash tools/check-local-ci.sh`; /tmp/pts-rk-zfc-ci.log. Exact commands, both
incremental builds, baseline, fresh build, kernel check, final CI and stage
summaries are retained in verification/set-application-2026-10-14/.

First remaining construction: actual countable cardinal/sort-code universes
U_i and extensional decoding, then finite-aleph/GCH cardinal bounds and
coherent coding bijections. The new operation evaluates ordinary graphs,
not the cardinal elements used as function codes in the paper. Context/term
interpretation, substitution and beta semantics, original-typing soundness,
and the interpreted Bottom corollary remain unproved. Do not call these
graph results a finalized PTS soundness proof or an unconditional ZFC model.
Next exact verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer ZFC_model/SetApplication.vo`.

## Completeness update: STLC reduction checked, external hardness outstanding

Current parent HEAD: b61eef6 (updated manuscript merge). This task adds
STLCEmbedding.v, its dune entry and eight Audit.v checks; updates README,
DECISIONS and this state. No kernel changes, admits or new axioms. User-owned
logs/ is untouched. The user subsequently requested commit and push; this
snapshot is prepared for `Normalization complexity: prove Church STLC reduction`
on main, to be pushed normally to origin/main.

Exact new public statement, ChurchSTLC.church_stlc_reduction:

    forall (t u : Term nat 1) (A : ChurchSTLC.Ty),
      has_type emptyEnv fzero t A -> has_type emptyEnv fzero u A ->
      typ empty (close t) (Pi (U 0) (code A fzero)) /\
      typ empty (close u) (Pi (U 0) (code A fzero)) /\
      (convertible t u <-> def_equiv nat 0 (close t) (close u)) /\
      encodingSize (close t) + encodingSize (close u) =
        encodingSize t + encodingSize u + 4.

Source has_type and beta are independent Church STLC relations, not PTS
premises renamed as STLC. The single ground type is closed by lambda o:U0;
annotations are preserved. Reflection is proved using normal type codes,
shape preservation, and original confluence. No finite-example argument.

Fresh dependency build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir
/tmp/pts-rk-stlc-fresh.ybfesA --display=short --no-buffer
theories/NormalizationComplexity/Audit.vo`.
Log /tmp/pts-rk-stlc-fresh.log contains 96 closed assumption reports
(95 audit results, one upstream report). All eight new results are closed.
Rebuild after comment/format cleanup: /tmp/pts-rk-stlc-final-audit.log, exit 0.
Recursive `rocq check -silent -o -Q
/tmp/pts-rk-stlc-fresh.ybfesA/default/theories PTSrk
PTSrk.NormalizationComplexity.Audit` exited 0; /tmp/pts-rk-stlc-kernel.log.
Repeated after final cleanup: /tmp/pts-rk-stlc-final-kernel.log, exit 0.
The global loaded-library extensionality entry is unchanged from upstream;
it is not an assumption of any audited theorem. Baseline full local CI also
exited 0 (/tmp/pts-rk-tower-hardness-baseline.log).
Final full local CI exited 0, all 81 stages pass:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/tower-hardness-final"
bash tools/check-local-ci.sh`; /tmp/pts-rk-stlc-ci.log. Exact commands,
all five incremental compiler results (including failures), final builds,
kernel check and CI summaries are retained under
docs/direct-r-handoff/verification/tower-hardness-2026-10-14/.

Remaining goal: formalize the machine/encoding complexity framework and
Nguyen's STLC TOWER-hardness theorem, then compose with the checked reduction.
There is no unconditional machine-level TOWER-completeness theorem in Rocq
yet. The README identifies the external mathematical input and separates it
from kernel evidence. No hardness premise has been hidden in the goal.
Next exact verification command (README environment exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/NormalizationComplexity/Audit.vo`.

The following normalization-completion milestone is historical; its scope
is the operation-cost upper bound, not the new lower-bound claim.

## Normalization complexity COMPLETE in the documented operation-cost model

Parent HEAD is 95450d34bffd4c4d54ddd73d79f0d0d830837276. All earlier proof
work is preserved; user-owned logs/ is untouched. The user subsequently
requested commit and push. This snapshot is prepared for the commit
`Normalization complexity: prove TOWER and fixed-rank normalization` on main,
to be pushed normally to origin/main. Original kernel unchanged.

Final public statements (all use original Term/typ/RankSorts and beta steps):

1. `fixed_rank_normalization`: wf G -> typ G t T -> RedexBound G t d ->
   exists u, fst (normalizeCosted d t) = Some u /\ t ->* u /\ beta_normal u /\
   typ G u T /\ cost <= tower (2*d+1) (nodes t+5*d+2).
2. `rank_bound_in_linear_time`: for closed typ empty t T, the executable
   conservativeRankCosted returns a semantic redex bound <= 2*s+1 at cost
   <= 7*s, with s = encodingSize t.
3. `normalization_in_TOWER`: for closed typ empty t T, automaticNormalizer
   returns Some u, with t ->* u, beta_normal u, typ empty u T, and TOTAL cost
   <= tower (4*s+3) (18*s+8), including computation of the rank bound.

No semantic estimator, descent, success or termination contract is a premise
of these results. The fixed-rank theorem naturally takes the paper's semantic
d-bounded-input premise, not an assumption that a supplied fuel succeeds.
The cost model is explicit constructor/callback and rank-word operations;
labels/indices use the documented unary encoding. Counters are ghost accounting,
not a machine/extraction runtime certificate for Gallina unary counters.

Proof chain: Morphisms -> Safety (including residual substitution/context
transport) -> Descent -> BoundedNormalization; SortBounds -> AutomaticBound ->
Normalization connects the conservative bound to the executable reducer.
Audit.v has 87 Print Assumptions checks, all closed under the global context.

Important mathematical repair: the manuscript/previous handoff's claimed
`RedexBound empty t (S (estimateRank t))` for closed typed t is FALSE.
EstimatorChecks proves the counterexample described in the milestone below.
Keep the original Agda translation unchanged. The final automatic normalizer
uses `conservativeRank t = 1 + maxRankLiteral t + nodes t` instead. This has a
proved linear computation cost and yields the requested classification without
changing head rank, typing rules or the input domain. The sharper Agda-budget
success theorem is neither proved nor needed; no such claim is made.

Build evidence: targeted Audit.vo command (README environment exports first),
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/NormalizationComplexity/Audit.vo`, exited 0; log
/tmp/pts-rk-nc-finalize-30.log prints exact public types and all 87 checks.
Fresh full dependency build (exit 0): same command with
`--build-dir /tmp/pts-rk-nc-final-fresh.Bm7eZT`; /tmp/pts-rk-nc-final-fresh.log.
It contains 88 closed reports: 87 audit checks plus one upstream report.
Final full CI (exit 0):
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-finalize-final"
bash tools/check-local-ci.sh`; /tmp/pts-rk-nc-finalize-final-ci.log. All 81
stages pass, including pristine upstream and the normalization audit.

Independent recursive kernel check (exit 0, no admitted dependency flags):
`opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o
-Q /tmp/pts-rk-nc-final-fresh.Bm7eZT/default/theories PTSrk
PTSrk.NormalizationComplexity.Normalization
PTSrk.NormalizationComplexity.BoundedNormalization
PTSrk.NormalizationComplexity.EstimatorChecks`.
Log /tmp/pts-rk-nc-final-kernel-check.log. Its global loaded-library summary
lists Stdlib functional_extensionality_dep, separately from theorem dependency
audits: all 87 local theorem Print Assumptions reports are closed. No new axiom
was introduced. No unsafe fixpoints, type-in-type or assumed positivity.

After a comment/import cleanup, another empty build directory was allocated:
/tmp/pts-rk-nc-verified.xg8gFn; command as above with this --build-dir,
log /tmp/pts-rk-nc-verified.log, exit 0, all 87 local audits closed. Final
recursive `rocq check -silent -o -Q .../default/theories PTSrk
PTSrk.NormalizationComplexity.Audit` also exited 0; log
/tmp/pts-rk-nc-verified-kernel-check.log. Checking PTSrk.Ranks alone produces
a byte-identical loaded-library context summary (`cmp` exit 0), confirming
the listed Stdlib axiom was already in the upstream library context.
Final cleaned-tree CI rerun, exit 0, all 81 stages PASS:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-verified-final"
bash tools/check-local-ci.sh`; /tmp/pts-rk-nc-verified-ci.log.

All 30 incremental logs (failures included), baseline, both fresh builds,
final CI outputs/stage tables and kernel-check outputs are archived under
verification/normalization-final-2026-10-14/. COMMANDS.md records exact commands,
per-attempt statuses and toolchain. Source/documentation whitespace checks pass.
Raw compiler logs are kept verbatim; their compiler-emitted trailing whitespace
is reported by a whole-worktree diff check, including earlier continuation logs.

No required normalization proof goal remains in this model. Optional future
work: analyze the sharper original Agda budget, or formalize a concrete machine/
binary-encoding cost refinement. Those are not hidden premises of the results.
Next exact verification command (README exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/NormalizationComplexity/Audit.vo`.

The following entries are chronological earlier milestones, superseded by
this completed status and retained for provenance.

## 2026-10-14 — fixed-rank normalization proved; estimator bridge refuted

In-progress continuation at unchanged HEAD 95450d3; all earlier work preserved.
Baseline local CI (including pristine upstream) exited 0; log
/tmp/pts-rk-nc-finalize-baseline.log. Added Morphisms, Safety, Descent,
BoundedNormalization and EstimatorChecks. Targeted Audit.vo build exited 0,
/tmp/pts-rk-nc-finalize-16.log. Original kernel/rules unchanged.

New checked results: typed simultaneous substitutions and context transport;
substitution residual bounds; greedy_strict_descent; bounded_rounds_normal;
fixed_rank_normalization, which guarantees successful normalization, original
typing preservation and cost <= tower (2*d+1) (nodes t+5*d+2) for d-bounded
well-typed terms. No semantic descent hypothesis is assumed.

IMPORTANT: the previous remaining estimator-to-head-rank goal is FALSE.
EstimatorChecks defines B = Pi _:U0.U0, A = Pi _:B.U0, and the closed type
Pi x:A. Pi y:B. ((lambda z:U0.x) U0) y. It is typed at U3, estimateRank is 0,
and the displayed lambda head has rank 2. All three facts and failure of
RedexBound empty witness (S (estimateRank witness)) compile. This refutes the
paper's claimed bridge, NOT TOWER normalization or even the success of its
particular estimator-budget attempt. Do not attempt to prove the false goal.

Repair in progress: retain the faithful Agda estimator and counterexample;
prove the conservative semantic bound 1 + maxRankLiteral t + nodes t for
closed typed terms. SortBounds.v is the current new proof layer; no final
automatic TOWER theorem yet. Next command (README opam exports first):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/NormalizationComplexity/SortBounds.vo`.
Development logs /tmp/pts-rk-nc-finalize-{1..17}.log retain failed attempts.

## Normalization continuation: cost bounds and semantic rank lemmas checked

Current HEAD is 95450d34bffd4c4d54ddd73d79f0d0d830837276 after the completed
history reorganization. This continuation is uncommitted. User-owned untracked
logs/ is untouched. The full normalization complexity proof remains OPEN.

Baseline: `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-continuation-baseline"
bash tools/check-local-ci.sh` exited 0, including pristine upstream.
Added Literals.v, Runtime.v and RedexRanks.v under theories/NormalizationComplexity;
updated Audit.v, dune and README. No original kernel/rules/annotations changed.

Checked milestones:
- Literal maxima cannot increase through original beta reduction.
- Costed renaming, substitution (including binder shifts), greedy passes,
  iteration and normal checking project to the original operations.
- A k-pass bounded attempt costs at most tower (2*k+1) (nodes t+5*k+2).
  With the estimator budget, its cost is at most
  tower (4*encodingSize t+3) (11*encodingSize t+7). These are bounded attempts,
  NOT yet guaranteed successful normalization at those budgets. Counters are
  ghost accounting in an explicit constructor/callback operation model.
- Original-typing semantic redex ranks are positive; rank-zero typed terms
  in well-formed contexts are normal. Type ranks are unique, stable under
  conversion, and preserved by typed substitution and reduction.
- Argument rank is strictly below function rank; application result rank
  is at most function rank. Newly exposed lambdas are bounded by original
  spine redexes. greedy_contracted_head_bound bounds the heads contracted
  by the bottom-up application clause, including newly exposed heads.

Targeted build commands used the dedicated opam exports documented in the
normalization README, then `opam exec --switch=pts-rk-ci -- timeout 180 dune build
--display=short --no-buffer theories/NormalizationComplexity/RedexRanks.vo`.
Latest target build: /tmp/pts-rk-nc-cont-25.log, exit 0.
Earlier continuation logs 1--17 cover Literals/Runtime and zero-rank proofs;
18--25 cover semantic rank comparisons and head exposure. Failures are retained,
not counted as successes: 18 implicit sort-inversion scope; 19 suppressed
notation; 21 context inference; 23 dependent boolean case equation. Corrected
builds 20, 22, 24 and 25 each exited 0.

Fresh audit command (exit 0):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build
--build-dir /tmp/pts-rk-nc-resume-fresh.LVufMY --display=short --no-buffer
theories/NormalizationComplexity/Audit.vo`.
Log /tmp/pts-rk-nc-resume-fresh.log contains all 54 local Print Assumptions
reports closed under the global context (plus one upstream report), and exact
types of cost bounds, zero_bound_normal, exposed_lambda_rank and
greedy_contracted_head_bound. No added axioms or admitted proofs.

First remaining local goal: a typed substitution residual bound, including
all binder/annotation positions. For well-formed G, typed u:U and body t:T in
G&U, TypeRank G u a and bounds d on both u and t should imply
`RedexBound G (subst t u) (Nat.max d a)`.
Generalize over binder depth/typed substitutions for its induction. Then
transport bounds under reduction of context declarations, and combine with
the checked contracted-head and strict argument-rank lemmas to prove strict
greedy descent. Estimator semantic soundness is independently still open:
closed typed t must have RedexBound empty t (S (estimateRank t)). Neither
missing theorem is postulated, and qualitative SN does not establish either.

Next exact command after implementing the residual lemma:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/NormalizationComplexity/RedexRanks.vo`.
Use the README's OPAMROOT/PATH exports first. See continuation verification
logs for failures and the final full-CI result recorded below.

Final full local CI (exit 0):
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-continuation-final"
bash tools/check-local-ci.sh`.
All requested stages passed, including pristine upstream and normalization.
Durable logs: verification/normalization-continuation/ contains the baseline,
all 25 targeted development logs (failures included), both fresh audits,
final CI output, final-stages.tsv and the pristine upstream commit identifier.
`git diff --check` passed; no forbidden proof escape was found in the
normalization sources. Changes remain uncommitted; no push performed.

## NormalizationComplexity: checked groundwork, full classification OPEN

Latest task: translate rank.agda and formalize the paper's TOWER / fixed-rank
ELEMENTARY normalization claims. Starting HEAD d60de9cf84dd5921a809b4a63b1590b21a000397;
only user-owned untracked logs/ existed. Those logs remain untouched. No commit
or push was requested for this task; changes remain in the worktree.

Baseline command (exit 0):
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-complexity-baseline"
bash tools/check-local-ci.sh`; outer log /tmp/pts-rk-normalization-baseline.log.
This includes the separate pristine upstream build.

Added theories/NormalizationComplexity/{Rank,Greedy,Bounds,Audit}.v, dune,
and README.md. Original syntax, rules, annotations and beta relation unchanged.
The Agda estimator variants are translated; optimization equalities checked.
Greedy passes/iterates are beta sound. A bounded successful result is normal.
Proved node-size substitution/product and greedy exponential/iterated-tower
bounds, linear numeric estimator magnitude, and linear abstract word-model
traversal cost (NOT a claim about unary-nat machine execution).

Successful targeted build (exit 0):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/NormalizationComplexity/Audit.vo`.
Log /tmp/pts-rk-normalization-15.log: all 15 Print Assumptions reports closed.
The regular CI driver now has an additional normalization audit stage.

Fresh build (exit 0) used a newly allocated absolute build directory:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build
--build-dir /tmp/pts-rk-normalization-fresh.OFEjeT --display=short --no-buffer
theories/NormalizationComplexity/Audit.vo`.
Retained report: verification/normalization-complexity-2026-10-13.log,
including fresh compilation and 15 closed assumption reports.
Final complete local CI command (exit 0):
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-complexity-final"
bash tools/check-local-ci.sh`.
All stages pass, including pristine upstream and the new normalization audit.
Stage table: verification/normalization-complexity-ci-2026-10-13.tsv.
Development logs, including failures and final CI output, are copied into
verification/normalization-complexity-development/ for durable continuity.

Earlier failing compiler invocations are retained at
/tmp/pts-rk-normalization-rank-{1,2,3}.log and
/tmp/pts-rk-normalization-{4,5,6,7,8,9,10,11,12,13,14}.log.
Failures were missing Dune modules and proof-script elaboration/arithmetic;
each was repaired without changing kernel rules or adding assumptions.
An attempted fresh build using --build-dir _build/normalization-fresh failed
before compilation (Dune requires an absolute or immediate-child build dir);
its diagnostic is /tmp/pts-rk-normalization-fresh.log.

The full requested classification is NOT COMPLETE. First next mathematical
goal: define semantic contextual redex-rank bounds at original RankSorts and
prove the estimator bounds abstraction-domain ranks under typing/conversion.
Then prove strict greedy rank descent and consequently
`normalb (rounds (S (RankEstimate.estimateRank t)) t) = true` for closed typed t.
Finally cost the actual substitution/greedy implementation: output-size bounds
alone are not time bounds. See the new README for precise model qualifications.
No pending obligation is added as an axiom or hypothesis of a completed target.

Next exact incremental command (after environment exports in the README):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/NormalizationComplexity/Audit.vo`.

## Completed Theorem 7; separate ZFC development relocated

Request: move the set-model development into ZFC_model, finalize Theorem 7,
commit and push. Starting HEAD 5551117; prior uncommitted equality/deduction
proofs and verification logs are preserved. User logs/ untouched.
Baseline local CI including pristine upstream exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/theorem7-baseline"
bash tools/check-local-ci.sh`; /tmp/pts-rk-theorem7-baseline.log.

Moved models/{SetFunctions.v,dune,README.md} to ZFC_model, preserving the
PTSrkModel namespace and unchanged proofs. Updated the CI target and live docs.
The pinned third-party dependency remains vendor/zfc. The set model and its
typing soundness remain INCOMPLETE, independent of both R interpretations.

New checked results:
- FunctionalCountermodel.soundness and order_reflexivity_underivable: the
  shared source arithmetic countermodel extended to ALL functional source
  deduction rules, using stable negative semantics without a classical axiom.
- Theorem7.order_reflexivity_realized and nonfaithfulness: original PTS proof
  of the translated sentence that the independent source system cannot derive.
- Theorem7.theorem7: all functional source axioms, deduction preservation,
  ground truth/internal refutation, and nonfaithfulness, unconditionally.
- DerivationCertificates.derive_sound/derive_complete: a finite certificate
  interpreter for EXACTLY original Typing.typ at RankSorts. Conversion uses
  explicit full beta traces (including annotations), justified by existing
  confluence; no new PTS rules or alternate typing relation.
- WitnessSearch.witness: forall A, Core.Realizes A ->
  {p : Term nat 0 | @typ nat RankSorts 0 ε p A}. Exhaustive finite enumeration
  plus Stdlib's CONSTRUCTIVE natural-number search proves termination from
  inhabitance, without any choice or typing-decidability assumption. Deliberately
  inefficient; not a replacement for the fast native checker on concrete terms.
- Theorem7.theorem5_target : Kernel.Theorem5Target, no arguments/assumptions.
- Theorem7.effective_axiom a : {p | @typ nat RankSorts 0 ε p (axiom_type a)}.
- Theorem7.effective_deduction : forall A : FirstOrder.formula 0,
  FunctionalSyntax.derives [] A ->
  {p : Term nat 0 | @typ nat RankSorts 0 ε p (FirstOrder.sentence_translation A)}.
  Effective source-axiom and true/false ground-atom interfaces also constructed.
These settle the previous Prop-to-Type witness gap using independently proved
all-index realization/preservation. They do not assert the old bounded optional
generator's particular totality contracts; those are not used by the theorem.

Commands (documented OPAMROOT/PATH), each with timeout 180 and flags
`--display=short --no-buffer` after `opam exec --switch=pts-rk-ci -- timeout 180 dune build`:
- FunctionalCountermodel.vo and ZFC_model/SetFunctions.vo: exit 0 on first build;
  /tmp/pts-rk-theorem7-countermodel-1.log.
- Interpretation_of_R/DirectRDerivationCertificates.vo: logs
  /tmp/pts-rk-theorem7-certificates-{1,2,3,4,5}.log, exits 1,1,1,1,0.
  Fixed dependent map membership, then explicit existential arguments in
  nth_error_In and conversion_sound; no mathematical weakening.
- Interpretation_of_R/DirectRWitnessSearch.vo: exit 0 on first build;
  /tmp/pts-rk-theorem7-search-1.log.
- Interpretation_of_R/functional/DirectRTheorem7.vo: logs
  /tmp/pts-rk-theorem7-package-{1,2}.log, exits 1,0 (extra closing parenthesis).
- Interpretation_of_R/functional/DirectRFunctionalAudit.vo and DirectR.vo:
  exit 0; /tmp/pts-rk-theorem7-audit.log; 493 closed assumption reports, including
  all 45 new queries. Final theorem and effective interface types are printed.
No Axioms report and no timeout. Final local CI exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/theorem7-final"
bash tools/check-local-ci.sh`. This includes pristine upstream, the relocated
ZFC target and all four new stages without weakening checks or timeouts.
Contribution stages were incremental. A separate fresh FULL build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-theorem7-full.LaNXNB --display=short --no-buffer`.
Its 601 assumption reports are all closed, with no Axioms report or timeout.
Exact transcript: verification/theorem7-full-2026-10-13.log, byte-identical to
/tmp/pts-rk-theorem7-full.log. The final theorem, effective target and effective
deduction all appear in the fresh audit output with their unconditional types.
Exact byte-compared transcripts are retained as
verification/theorem7-{baseline,countermodel-1,certificates-1,certificates-2,
certificates-3,certificates-4,certificates-5,search-1,package-1,package-2,audit,ci}
-2026-10-13.log (each brace entry is one joined filename).
Source/docs diff checks and shell syntax check passed. Original theories/ and
vendor/ are unchanged against HEAD; relocated SetFunctions.v and dune are
byte-identical to their previous versions. Raw compiler logs intentionally
retain whitespace and failed attempts. No remote CI result is claimed.
Theorem 7 (thm:direct-R) is COMPLETE, including effective Type-valued interfaces
and the original Kernel.Theorem5Target. No remaining Theorem 7 proof obligation.
External PTS Bottom nontriviality and the separate ZFC model's soundness were
not part of this theorem and remain distinct; no such result is claimed.
The old bounded optional generator contracts remain separate legacy goals.

Commit handoff: all checked proof work since parent 5551117, the ZFC relocation,
docs and exact logs are to be committed together as "Complete functional R
interpretation and isolate ZFC model", then ordinarily pushed as explicitly
authorized. This entry records the checked pre-commit tree; the containing
commit's hash is available from Git history. User logs/ remain unstaged.
Next exact command for a new session is verification, not a missing proof:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/theorem7-recheck"
bash tools/check-local-ci.sh`.

## Current continuation: equality and deduction preservation

At the user's request, committed the preceding checked milestones as
555111701490728c9ed594b646465dcbd96620c4, "Realize functional R axioms and
establish deduction infrastructure", then pushed origin/main successfully.
User logs/ are untouched. New proof work below is not in that commit.
Baseline `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-equality-baseline"
bash tools/check-local-ci.sh` exited 0, including pristine upstream.
Log: /tmp/pts-rk-functional-equality-baseline.log.

DirectRFunctionalEquality now compiles: scoped symmetry, term congruence,
atomic equality transport, typed/admitted/equal environment extension,
transport for EVERY formula, and equality_replacement for arbitrary source
substitution. Observation premises are derived from Good, not dropped.
The transportable helper is a proved property, not a new domain/source axiom.
Primitive conjunction/disjunction/existential reuse their definitionally equal
negative translations without changing the source syntax or PTS annotations.
Command (documented OPAMROOT/PATH): `opam exec --switch=pts-rk-ci -- timeout 180
dune build --display=short --no-buffer
Interpretation_of_R/functional/DirectRFunctionalEquality.vo`.
Logs /tmp/pts-rk-functional-equality-{1,2,3,4,5}.log: exits 1,1,1,1,0.
Failures: pointwise environment weakening (1/2), an unsolved observation premise
in replacement (3), and an incorrectly targeted tactic edit (4); all fixed.
DirectRFunctionalDeduction now compiles, including every constructor of the
independent FunctionalSyntax.derives: conjunction/disjunction/existential
introduction and elimination, guarded universal rules, classical elimination,
equality reflexivity and arbitrary-formula replacement. New unconditional type:
`forall A : FirstOrder.formula 0, FunctionalSyntax.derives [] A ->
 exists p, @typ nat RankSorts 0 ε p (FirstOrder.sentence_translation A)`.
General preservation quantifies over original PTS contexts, typed Good-admitted
environments, and inhabitants of translated source hypotheses. These are the
ordinary context premises, not assumptions of deduction preservation itself.
Exact command:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalDeduction.vo`.
Logs /tmp/pts-rk-functional-preservation-{1,2,3,4,5}.log: exits 1,1,1,1,0.
Failures: implicit conjunction argument (1); existential-elimination context
placeholder (2), environment matching (3), and rewriting the context as well
as the conclusion before newest (4). Explicit context/environment normalization
and rewriting a separate newest witness fixed them. No timeout.
Twenty new assumption queries and both module CI stages are registered.

Theorem 7 is NOT yet packaged/complete. Next goal is a functional source
countermodel proving order-reflexivity underivable, alongside the internal
order-reflexivity inhabitant. Reuse the shared DirectRCountermodel source
arithmetic structure (NOT a set model of PTS) and adapt the relational source
soundness proof without importing the relational interpretation. The functional
primitive connectives require stable negative source semantics to avoid adding
native classical axioms. Then package axioms, sentence preservation, ground
correctness and nonfaithfulness, keeping Type-valued effective witness selection
and legacy generator/Kernel.Theorem5Target contracts explicit rather than
claiming that Prop existence constructs those interfaces.
Next exact command after adding/registering the source countermodel module:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalCountermodel.vo`.
New proofs are uncommitted after the authorized push; user logs/ untouched.
Functional audit exited 0: 448 closed assumption reports, including all 20 new
lemma queries, with no Axioms report. Command (same OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalAudit.vo`.
Final local CI exited 0, including pristine upstream and both new stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-preservation-final"
bash tools/check-local-ci.sh`. Its contribution stages were incremental.
The separate fresh full build exited 0 with 556 closed assumption reports and
no Axioms report. Exact command (same OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-functional-preservation-full.lcC1g2 --display=short --no-buffer`.
Durable transcript: verification/functional-preservation-full-2026-10-13.log,
byte-identical to /tmp/pts-rk-functional-preservation-full.log. No timeout.
Source/docs `git diff --check` and
`bash -n tools/ci-check-direct-r.sh` passed. No remote CI result is claimed.
Exact compiler transcripts are retained under verification/functional-
equality-{1,2,3,4,5,baseline}-2026-10-13.log and functional-preservation-
{1,2,3,4,5,audit,ci}-2026-10-13.log (joined filenames without line breaks).
They match the /tmp originals byte-for-byte, preserving compiler whitespace
and failed attempts. No Admitted, axioms or disabled checks were added.

## Current continuation: independent functional deduction infrastructure

Request: proceed proving Theorem 7. Existing uncommitted proof work and index
state are preserved; user logs/ untouched. HEAD remains 7b6bdab. No commit/push.
Baseline local CI including pristine upstream exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-deduction-baseline"
bash tools/check-local-ci.sh`; /tmp/pts-rk-functional-deduction-baseline.log.

New checked modules:
- DirectRFunctionalSyntax: source renaming/substitution, the five functional R
  schemes, independent classical natural deduction with primitive conjunction,
  disjunction/existential, equality replacement, weakening and ex falso.
- DirectRFunctionalTranslation: environment extensionality, source and target
  renaming/substitution, and instantiate_translation for arbitrary formulas.
- DirectRFunctionalFormulaLogic: formation and stability of every translated
  formula, plus guarded universal introduction/instantiation. All constructions
  use the original annotated PTS terms and typing judgment.
- DirectRFunctionalSourceAxioms: source_axiom_realized bridges each independent
  source scheme to the existing all-index PTS witnesses, in arbitrary contexts.
  The harmonized paper's functional R4 is implication, not relational iff.

Exact per-module build command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalSyntax.vo`, and
similarly DirectRFunctionalTranslation.vo, DirectRFunctionalFormulaLogic.vo,
DirectRFunctionalSourceAxioms.vo.
Compiler logs /tmp/pts-rk-functional-syntax-{1,2}.log: exit 1 (tactic branch
count), then 0. Translation-1: exit 0. Formula-logic-{1,2,3}: exits 1,1,0
(implicit lifted sort, then unspecified domain of double_negation_map; fixed
by explicit domain formation and source formula). Source-axioms-1: exit 0.
No timeout. New lemmas are registered for Print Assumptions, and CI retains
its unchanged checks/timeouts with four additional explicit module stages.

Theorem 7 remains INCOMPLETE. First remaining goal is congruence/equality
replacement for arbitrary translated formulas, then induction on the independent
FunctionalSyntax.derives (including all logical and eigenvariable rules).
Target preservation: typed Good-admitted environments and inhabited translated
hypotheses imply an inhabitant of the translated conclusion, in original typ.
For equality transport, reuse the scoped successor_congruence in
FunctionalBounded, addition_congruence/equality_transitivity in
FunctionalAddition, and multiplication_congruence in FunctionalMultiplication.
Unlike the unary equality API, these require GAt premises; obtain them from
FunctionalTerms.term_observed on the Good-admitted environments. Do not discard
those premises when adapting the relational proof. Symmetry also needs a scoped
wrapper around Foundations.Law_eq_sym_typed (FunctionalTerms' wrapper is closed).
Also retain the final theorem's nonfaithfulness witness and effective witness
packaging obligations; no Type-valued Theorem5Target or generator totality claim.
Next exact command after adding the equality module and its Dune registration:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalEquality.vo`.
The functional audit exited 0, with 428 closed assumption reports (32 new
queries) and no Axioms report. Exact command (same environment):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalAudit.vo`.
Final local CI exited 0 including pristine upstream and the four new stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-deduction-final"
bash tools/check-local-ci.sh`. Contribution stages were incremental. The separate
fresh full build exited 0, with 536 closed assumption reports and no Axioms:
`opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-functional-deduction-full.uFR5gh --display=short --no-buffer`.
Exact durable logs: verification/functional-deduction-full-2026-10-13.log and
verification/functional-deduction-ci-2026-10-13.log. Both match their /tmp originals
byte-for-byte. No remote CI result is claimed. No timeout occurred.
All new proof work remains uncommitted, HEAD 7b6bdab, and no push was performed.
Source/docs diff checks and shell syntax check
exited 0. Exact compiler transcripts, including all three failures, are retained
under verification/functional-{syntax-1,syntax-2,translation-1,formula-logic-1,
formula-logic-2,formula-logic-3,source-axioms-1,deduction-baseline,deduction-audit}
-2026-10-13.log (each brace entry denotes one filename, with no line break).
These retained transcripts have been compared byte-for-byte to the /tmp logs;
compiler whitespace is intentional and excluded from source diff checks.

## Current continuation: Good instantiation and bounded cases

Request: proceed proving Theorem 7. All uncommitted multiplication work, index
state and user logs/ are preserved. HEAD remains 7b6bdab; no commit or push.
Baseline local CI including pristine upstream exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/good-invariant-baseline"
bash tools/check-local-ci.sh`; /tmp/pts-rk-good-invariant-baseline.log.

New module DirectRFunctionalCases: a fixed checked specialization exposes the
ORIGINAL Good eliminator for arbitrary scoped d and rank-10 family Q. Its
first build exited 0. Generic closure-family formation and beta conversion to
the existing invariant-closure types are being checked. Build 2 exited 1 for
an implicit scope parameter in step_motive_beta's change command; explicit
scope annotations are now supplied in both motive beta lemmas.
Command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalCases.vo`.
Logs: /tmp/pts-rk-good-invariant-1.log through -3.log.
Build 3 exited 1 because lifting an indexed invariant is not definitionally
its scoped instance; proved renaming equalities normalize that plumbing.
Build 4 reached motive_zero and exited 1 for the same implicit-scope issue;
build 5 exited 0 after an explicit renaming equality. Build 6 exited 0:
good_invariant_realized and bounded_case_realized now give closed original
typ witnesses uniformly in cutoff, for arbitrary Good-admitted elements.
They instantiate the existing Good motive at rank 10 and apply the four
constructor-closure witnesses; no host induction over expression trees is used.

DirectRFunctionalAxioms compiled on its first build (exit 0): use the bounded case
to derive original R4 by internal no_back refutation of its large branch, and
R5 by transporting each finite equality or composing the large lower bound.
Command is the same as above with DirectRFunctionalAxioms.vo; first log is
/tmp/pts-rk-functional-axioms-1.log. Independent functional deduction
preservation remains; Theorem 7 is not complete.
The new unconditional results are `forall n, Realizes (R4 n)`,
`forall n, Realizes (R5 n)`, and
`forall a, Realizes (axiom_type a)`, with the original Codes definitions.
Core.Realizes means `exists p, @typ nat RankSorts 0 ε p ...`.
The old generated-witness totality contracts and Type-valued Theorem5Target
record are not asserted to be constructed by this Prop-valued existence theorem.
31 new lemma assumption queries, public type checks and both modules have been
registered in the functional audit and unchanged-timeout CI driver.
The functional audit exited 0 with 396 closed assumption reports, including
all 31 new lemma queries. Exact audit command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalAudit.vo`.
Log: /tmp/pts-rk-functional-axioms-audit.log.
The new bounded_case_type is exactly
`Π Domain (Arrow (GoodAt V0) (CaseAt n V0))`; its theorem is unconditional
`forall n, Realizes (bounded_case_type n)`.
Final local CI exited 0, including pristine upstream and both new stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-axioms-final"
bash tools/check-local-ci.sh`. Its contribution stages were incremental.
The fresh FULL build exited 0 with 504 closed assumption reports and no Axioms
report. Exact command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-functional-axioms-full.qDviqx --display=short --no-buffer`.
Durable full transcript: verification/functional-axioms-full-2026-10-13.log.
No timeout occurred. Source/documentation `git diff --check` and
`bash -n tools/ci-check-direct-r.sh` exited 0; raw logs retain compiler whitespace.
All new work is uncommitted, prior multiplication changes and index state are
preserved, user logs/ are untouched, and HEAD remains 7b6bdab. No push was
requested or performed and no remote CI success is claimed.
Durable final audit/CI transcripts:
verification/functional-axioms-audit-2026-10-13.log and
verification/functional-axioms-ci-2026-10-13.log.
Baseline and incremental transcripts are retained in verification/ as
good-invariant-baseline, good-invariant-1 through -6, and functional-axioms-1
(all suffixed -2026-10-13.log). Failed scope/renaming attempts remain visible.

First remaining proof obligation: DirectRFirstOrder currently defines terms,
formulas and translation but no source substitution or derives relation.
Define independent scoped classical deduction over that functional syntax,
then prove translation/substitution, formula stability and equality replacement
for admitted arguments, and deduction preservation. Bridge its source axiom
formulas to these Codes scheme witnesses; do not define derivability as target
inhabitation or replace the functional carrier by the relational one.
Next exact command after implementing the independent functional deduction
system/translation preservation (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer @Interpretation_of_R/functional/audit`.

## Previous continuation: multiplication invariant, after 7b6bdab

User requested commit/push, then further Theorem 7 proofs. Committed the
reorganization and accumulated checked milestones as 7b6bdab74d1518bf8e830d717c0025de4df485db;
`git push origin main` exited 0. User logs/ remain untracked and untouched.
The commit retains exact compiler logs, including trailing whitespace emitted
by rocqdep; the pre-commit diff check reported that log whitespace (not a proof
failure). Earlier diff checks had not inspected these then-untracked logs.

Baseline local CI (including pristine upstream) exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/multiplication-baseline"
bash tools/check-local-ci.sh`; /tmp/pts-rk-multiplication-baseline.log.
New DirectRFunctionalMultiplication proves scoped constructor formation,
observation closure, congruence, and both order bounds with their explicit
positive-factor premises, plus finite/finite and positive large-factor cases.
The first and second incremental builds exited 0, including both zero-factor
laws, equality-to-zero transport, finite/large and large/finite cases, and the
large/large branch. The third build exited 1 for a missing rename_order lemma
in the combined case proof; that structural equality has now been proved.
The fourth run exited 0 for the module and functional assumption audit:
365 closed assumption reports, including all 22 new multiplication lemmas.
The unconditional public result is
`forall n, Realizes (multiplication_invariant_type n)`, where the type is
`Π Domain (Π (lift_closed Domain)
  (Arrow (InvariantAt n (shift V0)) (Arrow (InvariantAt n V0)
    (InvariantAt n (multiplication_at (shift V0) V0)))))`.
Here multiplication_at x y is the original doubly applied multiplication
constructor. The scoped theorem also accepts arbitrary typed x,y and their
two invariant witnesses. It never assumes the output invariant.
No PTS rule or proof assumption is changed.
Command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/functional/DirectRFunctionalMultiplication.vo`.
Logs: /tmp/pts-rk-multiplication-1.log through -4.log. The combined negative
cases and positive invariant closure now compile; both G witnesses remain
separate. The fresh full build exited 0, with 473 closed assumption reports
and no Axioms report. Exact command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-multiplication-full.bL0el8 --display=short --no-buffer`.
Durable log: verification/multiplication-full-2026-10-13.log.
No timeout occurred. The first final-CI
attempt exited 1 at 02-kernel because its build overlapped the still-finishing
audit in the same Dune directory; rerunning after the audit exited is recorded
as /tmp/pts-rk-multiplication-ci-2.log and exited 0. Exact successful command:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/multiplication-final-2"
bash tools/check-local-ci.sh`. It includes pristine upstream and the new
multiplication stage; contribution stages reuse the completed audit output.
No proof or resource limit was weakened.
Durable logs: verification/multiplication-baseline-2026-10-13.log,
multiplication-1/-2/-3/-4-2026-10-13.log, multiplication-ci-2026-10-13.log
(the Dune-lock failure), and multiplication-ci-final-2026-10-13.log.
Theorem 7 remains incomplete. Next goal: instantiate Good at invariant_motive,
then project CaseAt, derive R4/R5, and prove functional deduction preservation.
Next exact command after that edit (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer @Interpretation_of_R/functional/audit`.
This new multiplication work is not yet committed. Source/documentation
`git diff --check` and `bash -n tools/ci-check-direct-r.sh` exited 0. Raw logs
retain compiler whitespace. HEAD and origin/main remain 7b6bdab; the user
logs/ directory is untouched. No remote CI result is claimed for this work.

## Previous continuation: separate relational and functional libraries

Request: isolate the interpretations in Interpretation_of_R, with relational/
and functional/ subdirectories. Existing uncommitted proof changes and user
logs are preserved; no commit or push requested or performed.
Baseline: `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/layout-baseline"
bash tools/check-local-ci.sh` exited 0, including pristine upstream.
Transcript: /tmp/pts-rk-layout-baseline.log.

The source relocation is implemented. The original kernel remains in theories/.
Shared builders, structural logic, tables, iteration and selector certificates
are in Interpretation_of_R; interpretation-specific definitions/proofs are in
its relational/ and functional/ libraries. Theorem 4 remains the completed
target; Theorem 7 remains incomplete (multiplication invariant closure first).
First validation command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer Interpretation_of_R/relational/DirectRRelationalAudit.vo`.
The first build exited 1: Unary still needed the generic nJ2..nJ9/nj9
exact-rank encodings. Moving those to CommonCodes fixed it. The second
relational audit exited 0 (34 closed assumption reports).
The first functional attempt exited 1 because Dune was already running in
the same build directory; the second exited 0 (343 closed reports).
The first fresh full build and first post-refactor CI exited 1 at the old
UnaryAudit: its qualified certificate names still referred to Separation.
Updating those to FiniteCertificates also required an explicit import there;
the intermediate unary-audit attempt exited 1 for that missing import.
The second clean full build encountered the same missing import before the
fix was copied into its build tree. All failures remain in the layout logs.
Final verification:
- Fresh isolated relational command (documented OPAMROOT/PATH) exited 0:
  `opam exec --switch=pts-rk-ci -- timeout 180 dune build
  --build-dir /tmp/pts-rk-relational-isolated.Wq3dhB --display=short --no-buffer
  @Interpretation_of_R/relational/audit`. Both relational and unary audits ran:
  94 closed assumption reports; no functional module was compiled.
- Fresh FULL build exited 0:
  `opam exec --switch=pts-rk-ci -- timeout 600 dune build
  --build-dir /tmp/pts-rk-layout-final.kTXJEG --display=short --no-buffer`.
  451 closed assumption reports, matching the pre-refactor total; no Axioms
  report. Log: verification/layout-final-full-2026-10-13.log.
- Both new aliases passed (exit 0, incremental after the fresh full build):
  `opam exec --switch=pts-rk-ci -- timeout 180 dune build
  --build-dir /tmp/pts-rk-layout-final.kTXJEG --display=short --no-buffer
  @Interpretation_of_R/relational/audit @Interpretation_of_R/functional/audit`.
- Final local CI exited 0, including actionlint, pristine upstream and all
  relocated stages: `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/layout-verified"
  bash tools/check-local-ci.sh`.
  Log: verification/layout-final-ci-2026-10-13.log. Contribution stages mix
  fresh and cached output; the separate successful clean build above is the
  complete fresh assumption audit. `git diff --check` and
  `bash -n tools/ci-check-direct-r.sh tools/check-direct-r.sh` also exited 0.

Failures and earlier successful checks are retained under verification/ as
layout-baseline, layout-relational-1/-2, layout-functional-1/-2, layout-full,
layout-ci, layout-unary-audit-1, layout-full-second-failed, and
layout-relational-isolated (all suffixed -2026-10-13.log). No timeout occurred.
There are no cross-interpretation imports, nor parent imports of either child
library. The kernel .v files and models/ are unchanged. All 1547 distinct named
declarations from the pre-move development remain present; extraction moved
some of them into shared modules. Existing working-tree proof edits and logs/
are preserved at their relocated paths. HEAD remains a63636c; no staging,
commit, push or remote CI claim is made.

Next mathematical goal remains functional multiplication invariant closure,
then Good instantiation, bounded cases, R4/R5 and functional deduction
preservation. Next exact command after editing, with documented OPAMROOT/PATH:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer @Interpretation_of_R/functional/audit`.

## Previous continuation: functional addition closure, following a63636c

Request: proceed proving. All previous uncommitted changes, their index state
and untracked user logs/ are preserved. No commit or push performed.
Baseline local CI including pristine upstream exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-addition-baseline"
bash tools/check-local-ci.sh`; functional-addition-baseline.log.

New checked module DirectRFunctionalAddition:
- Scoped addition typing, G closure, congruence and both operand-to-sum order
  bounds apply original closed guarded laws through weakening/substitution.
- case_of_numeral_equality handles any numeral index: use a finite branch below
  the cutoff or transport a true ground comparison to the global large branch.
- addition_finite_case combines congruence with the existing ground_add_typed
  and equality transitivity. addition_large_left/right use the corresponding
  sum bound and order transitivity. These are uniform proofs, not finite tests.
- case_eliminate is a derived negative elimination rule with a stable target
  and callbacks under actual Positive.extension contexts. addition_case uses
  it twice for the finite/finite branch and once for either large branch.
- extension_trans composes actual context extensions without extensionality.
  invariant_eliminate_pair eliminates BOTH positive invariants at the SAME
  rank-8 answer type, retaining both G proofs separately from negative cases.
- addition_invariant now proves closure for arbitrary scoped x,y:
  `Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
   inhabited Γ (InvariantAt n x) -> inhabited Γ (InvariantAt n y) ->
   inhabited Γ (InvariantAt n (addition_at x y))`.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAddition.vo`.
Logs under _build/local-ci-logs: functional-addition-1 exited 1 (missing closing
parenthesis in a scoped law type); functional-addition-2 exited 0.
functional-addition-case-1 and functional-addition-invariant-1 exited 0.
functional-addition-closed-1.log exited 1 (formation proof inference for the
second domain binder); supplying the explicit lifted domain-formation proof
fixed it. The following audit command exited 0:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`, functional-addition-audit-1.log.
All 23 new lemma assumption queries are closed under the global context.
The unconditional closed witness theorem now checked is:
`forall n, Realizes (addition_invariant_type n)`, where that type is exactly
`Π Domain (Π (lift_closed Domain)
  (Arrow (InvariantAt n (shift V0)) (Arrow (InvariantAt n V0)
    (InvariantAt n (addition_at (shift V0) V0)))))`.
No timeout occurred and no rule, assumption or CI limit was changed.
The module is registered in Dune, local CI and the functional assumption audit.
Fresh full build and final local CI both exited 0.
Outputs: _build/local-ci-logs/functional-addition-full.log and functional-addition-ci.log.
Exact fresh command: `opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-functional-addition.0LiTMb --display=short --no-buffer`.
Final CI command: `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-addition-final"
bash tools/check-local-ci.sh` (documented PATH).
Durable transcripts: verification/functional-addition-full-2026-10-13.log and
verification/functional-addition-ci-2026-10-13.log. The fresh build has 451
closed assumption reports, with no Axioms report. The final local CI uses
incremental contribution stages; the separate clean build provides the fresh
audit. No remote CI success is claimed.
`git diff --check` and `bash -n tools/ci-check-direct-r.sh` exited 0.
New changes this turn: DirectRFunctionalAddition, Dune/CI/audit registration,
STATE/DECISIONS and these two verification logs. Earlier changes and user logs/
remain untouched; HEAD is still a63636c and the work is uncommitted.

Theorem 7 is NOT complete. The first remaining mathematical obligation is
multiplication invariant closure, including BOTH zero-factor laws and the
positive-factor premise of each multiplication order bound. Reuse the generic
case_eliminate and invariant_eliminate_pair machinery for the binary proof.
Then instantiate Good at invariant_motive and project CaseAt, derive R4/R5,
and prove independent functional first-order deduction preservation.
Next exact command after implementing multiplication closure:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

## Historical continuation: functional invariant zero/successor, following a63636c

Request: proceed proving. Preserved all earlier uncommitted proof/log changes,
their index state, and untracked user logs/. No commit or push performed.
Baseline local CI including pristine upstream exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-bounded-baseline"
bash tools/check-local-ci.sh` (documented PATH); functional-bounded-baseline.log.

New module DirectRFunctionalBounded, using the original Codes definitions:
- CaseAt has exact rank 8 and InvariantAt exact rank 10, in every context and
  uniformly in cutoff. Scoped equality/order/G formation and guarded law
  application lemmas support these results.
- invariant_intro, invariant_apply, invariant_case, and invariant_eliminate
  construct original typ inhabitants. The last uses Positive.extension to
  expose BOTH positive G evidence and negative cases under actual binders.
  It eliminates the positive invariant at a rank-8 answer type; it does not
  extract G from a negative disjunction.
- zero_case and zero_invariant are uniform in the cutoff.
- successor_finite_case advances an index below the cutoff; equality at the
  cutoff gives the global large branch. successor_large_case uses guarded
  order propagation and transitivity. successor_case eliminates CaseAt only
  into the stable negative CaseAt target.
- successor_invariant opens the parent's rank-8 answer type/continuation,
  eliminates the child at that same answer type, constructs parent G and
  Case separately, then feeds the parent continuation. The public closed
  successor_invariant_realized inhabits
  `Π Domain (Arrow (InvariantAt n V0) (InvariantAt n (successor_at V0)))`.
- invariant_motive_typed checks the closed `lam Domain (InvariantAt n V0)` at
  `Arrow Domain (𝓤 10)`; invariant_motive_beta proves its application equation.
  replace_case/replace_invariant and renaming identities retain annotations.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalBounded.vo`.
Logs under _build/local-ci-logs:
- functional-bounded-1/-2 exited 1 (map-membership inference; wrong certificate
  name); functional-bounded-3 exited 0.
- functional-successor-1 exited 0; -2 exited 1 (rewrite under a mapped list);
  functional-successor-3 exited 0.
- functional-invariant-successor-1 exited 1 because rewriting a continuation
  hypothesis also rewrote its context. -2 exited 0 after proving a separate
  equality for the hypothesis TYPE, leaving the actual context untouched.
- functional-invariant-motive-1 exited 0. No timeout or added axiom.

The audit now prints the new public types and checks all 45 new lemmas.
Audit command: `opam exec --switch=pts-rk-ci -- timeout 180 dune build
--display=short --no-buffer theories/DirectRFunctionalAudit.vo`;
_build/local-ci-logs/functional-bounded-audit.log, exit 0 (320 closed reports).
Fresh full command: `opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-functional-bounded.54mRFW --display=short --no-buffer`;
_build/local-ci-logs/functional-bounded-full.log, exit 0 (428 closed reports).
The module is registered in Dune and the unchanged-timeout CI driver.
Final local CI also exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-bounded-final"
bash tools/check-local-ci.sh`; _build/local-ci-logs/functional-bounded-ci.log.
Its contribution stages are incremental; the separate fresh full build provides
the freshly executed audit, with no Axioms report. No remote CI result is claimed.
Durable transcripts: verification/functional-bounded-full-2026-10-13.log and
verification/functional-bounded-ci-2026-10-13.log.
`git diff --check` and `bash -n tools/ci-check-direct-r.sh` exited 0.
New diff this turn: DirectRFunctionalBounded, Dune/CI/audit registration,
STATE/DECISIONS and the two verification transcripts. All pre-existing changes
and user logs/ are preserved. HEAD remains a63636c; work is uncommitted.

Theorem 7 remains INCOMPLETE. First remaining goal: addition closure of the
positive invariant for arbitrary scoped x,y with their two InvariantAt proofs,
NOT just external expression trees. Then multiplication closure (retain both
zero laws and positive-factor conditions), instantiate Good at invariant_motive,
and project CaseAt. R4/R5 and independent functional deduction preservation
remain after that. Internal separation, R3 and negative ground faithfulness
were completed at the previous milestone and must not be redone.
Next exact command after adding binary closure:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

## Historical continuation: original functional no_back, following a63636c

Request: proceed proving Theorem 7. Preserved the prior uncommitted atomic-suffix
proofs and verification logs, including their index state, and user logs/.
Baseline local CI including pristine upstream exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/leat-bridge-baseline"
bash tools/check-local-ci.sh` (documented PATH); leat-bridge-baseline.log.

New milestone: DirectRFunctionalSeparation.no_back_realized proves, uniformly,
`forall n, Realizes (Neg (LeAt (numeral (S n)) (numeral n)))` for the ORIGINAL
functional relation. order_body extracts the literal existing Order body;
order_reduction proves two beta steps. order_instance_observation identifies
the entire annotated body with the constructed observation telescope.
order_observation_formation follows by original subject reduction from the
existing Order typing theorem, not by a new formation assumption.

Command (documented OPAMROOT/PATH): `opam exec --switch=pts-rk-ci -- timeout 120
dune build --display=short --no-buffer theories/DirectRFunctionalSeparation.vo`.
Logs under _build/local-ci-logs: leat-bridge-1 through -5 exited 1 (substitution
normalization); leat-bridge-6 exited 0. functional-no-back-1 exited 1 (closed
lifting rewrite); functional-no-back-2 exited 0. No admissions or added axioms.
Normalization keeps the outer 31 binders intact and solves only suffix renaming
goals, explicitly reducing assembler eq_rect transports. Whole-goal rewriting
was slower and did not solve the substitution identity.

Further checked milestones in the same module:
- numeral_order_refuted: j < i -> Realizes (Neg (LeAt (numeral i) (numeral j))).
- ground_order_false: value u < value t -> Realizes (Neg (sentence_translation
  (less_equal t u))), for every closed functional source term t,u.
- ground_equality_false: value t <> value u -> Realizes (Neg
  (sentence_translation (equal t u))).
- R3_realized: forall m n, m <> n -> Realizes (R3 m n).
These are unconditional apart from the displayed numerical side conditions;
they do not assume a target inhabitant, formation contract, or model.
Existing ground_equality_true/ground_order_true complete both directions of
ground atom proof/refutation construction. External Bottom nontriviality is
not used or newly proved here.

functional-refutation-1.log and functional-ground-negative-1.log exited 0,
using the module command above (180 seconds for the latter).
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo` exited 0;
_build/local-ci-logs/functional-separation-audit.log. All 19 new Print Assumptions
queries are closed under the global context. The audit prints the five public
theorem types. Added the new module to Dune and the unchanged-timeout CI driver.

Fresh full verification exited 0 with
`opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-functional-separation.TuasNl --display=short --no-buffer`,
output _build/local-ci-logs/functional-separation-full.log.
Final local CI exited 0 with
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/functional-separation-final"
bash tools/check-local-ci.sh`, output functional-separation-ci.log.
Durable transcripts: verification/functional-separation-full-2026-10-13.log
and verification/functional-separation-ci-2026-10-13.log. The fresh build reports
383 closed assumption checks and no Axioms report. The final local CI uses
incremental contribution stages; the separate fresh full build supplies the
newly executed assumption audit. No remote CI result is claimed.
`git diff --check` and `bash -n tools/ci-check-direct-r.sh` exited 0.
Final additions this turn: DirectRFunctionalSeparation, its Dune/CI/audit
registration, the handoff updates and these two verification transcripts.
All earlier uncommitted changes and the user's untracked logs/ are preserved.

Theorem 7 is NOT complete. First remaining goal: uniformly construct the four
constructor closures of `InvariantAt n d`, then realize
`Π Domain (Arrow (GoodAt V0) (CaseAt n V0))` for every n by instantiating Good.
Do not weaken this to induction over external expression trees. Derive R4/R5
from that result, then preserve an independently defined functional deduction
system. No equality-table bridge is needed for the ground refutations now proved.
Next exact command after implementing the bounded-invariant layer:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
HEAD remains a63636c; no commit or push performed in this proof-only request.

## Historical continuation: atomic order suffix, following a63636c

Request: proceed proving. Starting HEAD a63636c; only untracked user logs/.
Those logs remain untouched. No commit or push performed this turn.
Theorem 7 remains INCOMPLETE; no original LeAt refutation is claimed.

Baseline complete local CI (including pristine upstream) exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/atomic-bridge-baseline"
bash tools/check-local-ci.sh`, with the documented local PATH.
Output: _build/local-ci-logs/atomic-bridge-baseline.log.

New checked milestones:
- TelescopeArguments.telescope_inclusion embeds the original variables through
  a dependent telescope. arguments_preserve_prefix and arguments_replace_prefix
  prove that an actual typed argument spine retains their substitution.
- FiniteSpecialization.contextual_data_observation eliminates all 23 law
  arguments and returns the eight-data substitution of any suffix that only
  uses those data. It constructs the law arguments; it does not assume them.
- data_fold_specialized and order_suffix_specialized compute the actual
  five-argument functional fold at the finite data. order_numeral_suffix
  computes its negative Boolean order entry uniformly in cutoff and indices.
- no_back_suffix uses cutoff S n (table size S (S n)), NOT cutoff n: the latter
  collapses n and S n. Its conclusion is beta equivalence to Neg Top.
- no_back_observation_elimination works in every original PTS context and
  constructs an inhabitant of Bottom from an inhabitant of the expanded
  backwards-order observation. This is an elimination lemma, not external
  Bottom nontriviality and not yet Realizes (Neg (LeAt ...)).

Incremental commands, with documented OPAMROOT/PATH:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRTelescopeArguments.vo`, exit 0, atomic-prefix-1.log.
Same command targeting DirectRFiniteSpecialization.vo, exit 0, atomic-prefix-2.log.
Suffix attempts atomic-suffix-1/-2 exited 1 (missing equivalence-instance import,
then an uninferred intermediate beta application); atomic-suffix-3 exited 0.
Elimination attempts atomic-elimination-1 through -5 exited 1 (wrong module
qualification, empty-Fin/scoping inference, and an over-unfolded rewrite);
atomic-elimination-6 exited 0. All logs are in _build/local-ci-logs.
No timeout occurred, and no kernel rule or assumption was changed.

Fresh full build and final local CI both exited 0.
Full build directory: /tmp/pts-rk-atomic-suffix.W8f3Xu.
Commands: `opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-atomic-suffix.W8f3Xu --display=short --no-buffer` and
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/atomic-suffix-final"
bash tools/check-local-ci.sh`.
Outputs: _build/local-ci-logs/atomic-suffix-full.log and atomic-suffix-ci.log.
Durable transcripts: verification/atomic-suffix-full-2026-10-13.log and
verification/atomic-suffix-ci-2026-10-13.log. The fresh full build contains 364
closed assumption reports, including all eight newly audited lemmas; no Axioms
report appears. Local CI contains 257 closed reports (including the additional
Print command). No remote CI result is claimed. `git diff --check` exited 0.
Final diff: the telescope/specialization modules, functional audit, STATE,
DECISIONS and two verification logs. HEAD remains a63636c; changes are uncommitted.
Untracked user logs/ remains excluded and unchanged.

First remaining goal: prove beta conversion from the ORIGINAL
`LeAt (numeral (S n)) (numeral n)` to
`data_observation_type (order_suffix (numeral (S n)) (numeral n))`, including
the formation needed for conversion. Then apply no_back_observation_elimination
under the original LeAt binder and abstract to obtain the internal refutation.
The equality analogue, negative ground faithfulness, four-constructor bounded
invariant, R3/R4/R5 and independent functional deduction preservation remain.
Next exact command after implementing the bridge:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

## Historical continuation: contextual observation and folds, following 947f08e

Request: proceed proving, then commit and push. Starting HEAD 947f08e, with
only untracked user logs/, which remains untouched. Theorem 7 is NOT complete.

Baseline complete local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/context-observation-baseline"
bash tools/check-local-ci.sh` (documented local PATH).
Output: _build/local-ci-logs/context-observation-baseline.log.

New checked generic lemmas in DirectRTelescopeArguments:
- closed_arguments_lift transports a closed dependent argument spine into
  any original PTS context. The terminal substitutions agree pointwise.
- closed_arguments_application applies that spine and returns the exact
  lifted substituted suffix. No functional extensionality is used.

DirectRFiniteSpecialization.contextual_observation supplies the same chosen
23 closed law terms uniformly in every context, following the eight data terms.
contextual_source_observation connects this application theorem to the actual
assemble(nAllObs body) source with its exact suffix assembly and substitution.

DirectRFunctionalEvaluation proves beta fold equations for Codes.zero,
Codes.successor, Codes.addition and Codes.multiplication at arbitrary scoped
arguments. numeral_evaluation and finite_numeral_evaluation apply to the
original five-argument presentation domain. Only the generic iteration helper
is reused from UnaryEvaluation; no unary carrier/relation replaces the target.

Incremental commands (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRTelescopeArguments.vo`, exit 0, context-arguments-1.log;
the DirectRFiniteSpecialization.vo target with timeout 180, exit 0,
context-specialization-1.log; and DirectRFunctionalEvaluation.vo with timeout 90,
exit 0, functional-evaluation-1.log. All logs are in _build/local-ci-logs.
Each compiled on its first attempt.

Fresh isolated full build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-context-observation.xCVh5g --display=short --no-buffer`.
All 356 assumption reports are closed under the global context; no Axioms
report appears. Exact output: verification/context-observation-full-2026-10-13.log.
Updated complete local CI exited 0, including pristine upstream and all original
stages, using `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/context-observation-final"
bash tools/check-local-ci.sh`. Its functional audit has 248 closed reports.
Exact output: verification/context-observation-ci-2026-10-13.log.
`git diff --check` and `bash -n tools/ci-check-direct-r.sh` exited 0.
No new remote CI result is claimed.

Commit checkpoint: `Lift finite observations into contexts and prove functional folds`,
parent 947f08e, commit 747362729e626ac122b5866d2a726f757dd2f71d. Includes the
generic transport lemmas, two new modules, audit, module/CI registration,
handoff and verification logs. `GIT_TERMINAL_PROMPT=0 timeout 45 git push origin main`
exited 0 and reported `947f08e..7473627 main -> main`. After the proof commit,
only untracked user logs/ remained; it is excluded and untouched. This delivery
note is a documentation-only follow-up with no proof changes after validation.

First remaining goal: relate the original EqAt/LeAt bodies on closed numerals
by beta conversion to observation_type with the corresponding fold suffix.
Use contextual_source_observation plus finite_numeral_evaluation and the false
order-table entry at cutoff n to construct a closed inhabitant of
`Neg (LeAt (numeral (S n)) (numeral n))` uniformly in n. Then derive negative
ground faithfulness. The four-constructor bounded invariant, R3/R4/R5 and
independent functional deduction preservation remain open.
Next exact command after implementing that bridge/separation:
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

## Historical continuation: complete finite observation arguments, following aa443af

Request: finish theorem 7, commit and push. Starting HEAD aa443af, with only
untracked user logs/. Theorem 7 is NOT complete. User logs/ is untouched.

Baseline complete local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/binary-congruence-prefix-baseline"
bash tools/check-local-ci.sh` (documented local PATH).
Output: _build/local-ci-logs/binary-congruence-prefix-baseline.log.

New binary-congruence application certificates and the exact original first
17/18-field source matches compiled, uniformly for q>0. Command:
`opam exec --switch=pts-rk-ci -- timeout 120 dune build --display=short
--no-buffer theories/DirectRFiniteDomainPrefix.vo`, exit 0;
_build/local-ci-logs/binary-congruence-prefix-1.log.

Source-prefix normalization initially was expensive. Local attempts
order-prefix-1, -5 and -7 reached 180-second timeouts (124). Failed attempts
-2/-3/-4 exposed reduction/rewrite mismatches. Attempt -6 was stopped (130)
to profile. Timed profiles -1/-2 were deliberately terminated (143).
All logs are in _build/local-ci-logs. Timed profile -3 was also terminated (143).
The existing CI stage budget is 1200 seconds and has not been changed.

The final source-matching proof uses assemble_prefix_congr by direct application,
not whole-goal rewriting or destructing the full prefix. This solved the
performance issue: order-prefix-8 exited 0 under the unchanged local 180-second
limit. No typing rule, annotation or theorem statement was weakened.

All ten arithmetic laws now compile in their actual source positions, including
the two multiplication order implications with their positivity premises.
arithmetic-prefix-1 failed on a second unsolved conversion subgoal; -2 exited 0.
The dependent application chain reaches all 31 arguments.

Public checked results:
- full_observation_specialization connects that chain to assemble(nAllObs body)
  for any named suffix, retaining its exact substitution by all 31 terms.
- observation_certificates constructs all 23 closed law proofs, uniformly for
  q>0, WITHOUT any assumed typed observation term.
- observation_arguments packages those proofs as an actual dependent
  TelescopeArguments.arguments spine over law_telescope (scope 8 to 31).
  Along with data_arguments_typed this supplies the finite observation.

Full-observation incremental audit: full-observation-audit-3.log exited 0 using
`opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`. Attempt -2 had a tactic bullet
focus error in the certificate conjunction and is retained. No admissions or
new axioms were introduced. The incremental functional audit has 231 closed
assumption reports.

Fresh isolated full build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 600 dune build
--build-dir /tmp/pts-rk-full-observation.DNp5N1 --display=short --no-buffer`.
All 339 assumption reports are closed under the global context.
Tracked exact command/output: verification/full-observation-full-2026-10-13.log.
Complete unchanged local CI exited 0, including pristine upstream and all
original stages: `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/full-observation-final"
bash tools/check-local-ci.sh`. Tracked output: verification/full-observation-ci-2026-10-13.log.
Failure/timeout/interrupted-profile history is indexed, with explicitly partial
error excerpts, in verification/full-observation-history-2026-10-13.log;
the full raw attempt logs remain at the paths listed there.
`git diff --check` exited 0. No new remote CI result is claimed.

Commit checkpoint: `Construct all finite observation arguments in the original PTS`,
parent aa443af, commit d348299014ccf659688c6ad077307de94ccd9eab. This is partial
progress on the requested Theorem 7, not its completion.
`GIT_TERMINAL_PROMPT=0 timeout 45 git push origin main` exited 0 and reported
`aa443af..d348299 main -> main`. User logs/ was the only untracked worktree
entry after the proof commit; it is excluded and untouched. This delivery note
is a documentation-only follow-up, with no proof changes after validation.

First remaining goal: lift the closed observation argument spine to an arbitrary
ambient PTS context, specialize the original E/O bodies, and prove finite fold
evaluation/no_back for the four-constructor presentation domain. Do not use the
unary Theorem4 observation as the functional one. Then prove negative ground
faithfulness, the four-constructor bounded invariant, R3/R4/R5 and independent
functional deduction preservation. Theorem 7 is NOT complete.
Next exact command after implementing context lifting/separation:
`opam exec --switch=pts-rk-ci -- timeout 1200 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

## Historical continuation: successor congruence, following a0e095b

Request: proceed proving, then commit and push. Starting HEAD:
a0e095bd4f3913bc090fe367e2cdcde58c2a44e2. Preserve and include the previous
uncommitted symmetry/transitivity checkpoint. Untracked user logs/ is untouched.
Theorem 7 is NOT complete.

Baseline complete local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/successor-prefix-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Output: _build/local-ci-logs/successor-prefix-baseline.log.

DirectRFiniteDomainPrefix now proves successor_application_certificate for
every q>0, with original predicate/equality-table/operation applications.
unary_congruence_application_typed and unary_congruence_application_beta
give exact formation and conversion for any typed unary operation.
successor_annotation_specialized and successor_prefix_matches_source check
the original source field 107 and its entire sixteen-field prefix, for every
dependent named suffix. successor_specialization proves original Typed typing
after the actual sixteen applications with the exact suffix substitution.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteDomainPrefix.vo`.
Exit 0 on first attempt: _build/local-ci-logs/successor-prefix-1.log.

First remaining goal: source fields 108/109, addition/multiplication congruence.
Package their four interleaved object/domain guards and relation/operation
applications, convert to FiniteBinaryCongruence's checked expanded types,
then extend the exact dependent application spine. Thirteen further arguments
follow these two. Full finite observation specialization, separation/negative
ground faithfulness, the four-constructor bounded invariant, R3/R4/R5 and
independent functional deduction preservation remain open.

Next command after the next prefix addition:
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
Fresh isolated full build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
--build-dir /tmp/pts-rk-successor-prefix.JYfA53 --display=short --no-buffer`.
All 234 assumption reports are closed under the global context, with no Axioms
report. Exact output: verification/successor-prefix-full-2026-10-13.log.
Complete local CI also exited 0, including pristine upstream and every original
stage, using `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/successor-prefix-final"
bash tools/check-local-ci.sh`. Its functional audit has 126 closed reports.
Exact output: verification/successor-prefix-ci-2026-10-13.log.
`git diff --check` exited 0. No new remote CI result is claimed.

Commit checkpoint: `Extend finite observation specialization through congruence`,
parent a0e095b, commit aa25111b4945cb34d6b82fae722a413f2fddd4d8; includes the
symmetry/transitivity and successor-congruence proofs, audit, handoff and logs.
`GIT_TERMINAL_PROMPT=0 timeout 45 git push origin main` exited 0 and reported
`e959029..aa25111 main -> main`. The prior credential-helper blocker did not
recur. This confirms delivery, not remote CI success. After the proof commit,
the only worktree entry was untracked user logs/. This delivery note is a
separate documentation-only follow-up; no proof source changed after validation.

## Historical continuation: equality equivalence laws, following a0e095b

Request: proceed proving theorem 7. Starting HEAD:
a0e095bd4f3913bc090fe367e2cdcde58c2a44e2, with only untracked user logs/.
No commit or push requested this turn. User logs/ remains untouched.
Theorem 7 is NOT complete.

Baseline complete local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/symmetry-prefix-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Output: _build/local-ci-logs/symmetry-prefix-baseline.log.

DirectRFiniteDomainPrefix now proves symmetry_application_certificate and
transitivity_application_certificate uniformly for q>0 and Boolean relations
satisfying the corresponding bounded numerical law. Their types retain the
original predicate and relation-table applications; exact formation is rank 5.
Specialization to Nat.eqb discharges both numerical laws unconditionally.

symmetry_prefix_matches_source and transitivity_prefix_matches_source identify
the exact original first 14/15 fields for every named suffix. The corresponding
specialization theorems prove original Typed judgments after all 14/15 actual
applications, at the precise substitution retaining every chosen proof term.
They neither assume a full observation nor change a PTS rule.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteDomainPrefix.vo`.
Exit 0 logs: _build/local-ci-logs/symmetry-prefix-1.log and
_build/local-ci-logs/transitivity-prefix-2.log. The retained failed attempt
transitivity-prefix-1.log had a missing closing parenthesis in both new types.

First remaining goal: source field 107, successor congruence. Convert its
predicate/table/operation applications to the existing unary-congruence law,
prove its source-prefix equality, and extend the exact suffix substitution.
Then apply the other fifteen arguments. Full finite observation specialization,
no_back/negative ground faithfulness, the four-constructor bounded invariant,
R3/R4/R5 and independent functional deduction preservation remain open.

Next command after the next prefix extension:
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
Complete local CI exited 0, including pristine upstream and all original stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/equivalence-prefix-final"
bash tools/check-local-ci.sh`. Its functional audit has 119 closed assumption
reports and no Axioms report. Command and output are retained in
verification/equivalence-prefix-ci-2026-10-13.log. The successful incremental
results and failed parser attempt are retained in
verification/equivalence-prefix-incremental-2026-10-13.log.
Fresh isolated full build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
--build-dir /tmp/pts-rk-equivalence-prefix.F0jhSA --display=short --no-buffer`.
All 227 assumption reports are closed under the global context, with no Axioms
report. Exact command/output: verification/equivalence-prefix-full-2026-10-13.log.
`git diff --check` exited 0. The proof/audit changes, handoff updates and three
verification logs remain uncommitted. No push was attempted and no new remote
CI result is claimed. Untracked user logs/ remains excluded and untouched.

## Historical continuation: equality reflexivity, following e959029

Request: proceed proving then commit (no push requested). Starting HEAD:
e9590295595b2fc6cf28b71b4860a422f6c39d17. The previous uncommitted four-domain
prefix work is retained and will be included in this proof checkpoint.
Untracked user logs/ is untouched. Theorem 7 is NOT complete.

Baseline complete local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/reflex-prefix-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Output: _build/local-ci-logs/reflex-prefix-baseline.log.

New checked results in DirectRFiniteDomainPrefix:
- relation_application_typed and relation_application_beta hold at arbitrary
  scope for the original annotated relation table.
- reflexivity_application_certificate: for every q>0 and every Boolean r
  reflexive below q, a closed PTS inhabitant of
  `Pi u:Fq. predicate_q u -> (relation_table q r u u -> Bottom)`.
- reflexivity_annotation_specialized and reflexivity_prefix_matches_source
  check the actual original field 104, for every dependent named suffix.
- reflexivity_specialization applies all thirteen actual arguments and gives
  original Typed typing at the exact substitution by the eight data terms
  and all five chosen proof terms. No premise assumes the observation itself.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteDomainPrefix.vo`.
Exit 0: _build/local-ci-logs/reflex-prefix-3.log.
Retained failures: reflex-prefix-1.log needed a positive-q case split to
resolve the selector formation rank; reflex-prefix-2.log used the wrong
direction of lift_closed_shift. Both are fixed without changing the calculus.

First remaining goal: source field 105 (equality symmetry). Build its exact
interleaved predicate-application type, convert to the existing symmetry_type,
and extend the dependent prefix through the actual symmetry proof. Then apply
the remaining seventeen relation laws. Full observation specialization,
no_back/negative ground faithfulness, the four-constructor bounded invariant,
R3/R4/R5 and independent functional deduction preservation remain open.

Next command after extending the prefix:
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
Updated complete local CI exited 0, including pristine upstream and every
original stage. Command:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/reflex-prefix-final"
bash tools/check-local-ci.sh`. The functional audit has 105 closed assumption
reports and no Axioms report. Tracked output with command/exit status:
verification/reflex-prefix-ci-2026-10-13.log. The three incremental results,
including both failures, are retained in
verification/reflex-prefix-incremental-2026-10-13.log.
Fresh isolated full build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
--build-dir /tmp/pts-rk-reflex-prefix.KuZtT6 --display=short --no-buffer`.
All 213 assumption reports are closed under the global context; no Axioms
report appears. Exact output: verification/reflex-prefix-full-2026-10-13.log.
`git diff --check` and `bash -n tools/ci-check-direct-r.sh` also exited 0.
This is local verification, not a new remote CI result.

Commit checkpoint: `Prove finite domain and reflexivity observation specialization`,
parent e959029. Includes the two new proof modules, their module/CI registration,
assumption audit, handoff and retained verification logs. No push is requested
or attempted. The only excluded user data is untracked logs/.

## Historical continuation: all domain binders, following e959029

Request: proceed proving. Starting HEAD was
e9590295595b2fc6cf28b71b4860a422f6c39d17 on main, with only untracked user logs/.
The local commits e959029 and 371f5bb are preserved. This turn makes no commit
or push; the previous Keychain delivery blocker is unchanged and no remote
state is claimed. Theorem 7 is NOT complete.

Complete baseline local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/binary-domain-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Output: _build/local-ci-logs/binary-domain-baseline.log.

DirectRFiniteBinaryDomain now proves the closed interleaved addition and
multiplication domain certificates, uniformly for q>0:

```
Pi u:Fq. predicate_q u -> Pi v:Fq. predicate_q v -> predicate_q (add u v)
Pi u:Fq. predicate_q u -> Pi v:Fq. predicate_q v -> predicate_q (mul u v)
```

Their names are addition_certificate and multiplication_certificate.
The generic bounded-table result uses positive delta_binary closure, not the
rank-three relational elimination lemma. Formation, beta conversion and the
final application-type certificates are checked in the original PTS.

DirectRFiniteDomainPrefix.domain_specialization extends the previous ten-argument
result through both actual proof arguments, yielding original PTS typing after
twelve applications and the exact suffix substitution by all four domain proofs.
domain_prefix_matches_source identifies the prefix with firstn 12 of the existing
Codes.observation_fields for every named suffix. The two annotation-specialization
equalities check fields 102/103, rather than assuming their types match.

Incremental commands (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteBinaryDomain.vo` and the analogous
DirectRFiniteDomainPrefix.vo target. Exit-0 logs:
_build/local-ci-logs/binary-domain-3.log and domain-prefix-3.log.
Earlier numbered failures are retained: unconstrained intermediate conversion
types needed explicit source proofs; nested product/arrow substitution needed
alternating rewrites; change needed an explicit right-hand type. No admissions
or new assumptions were introduced.

The first twelve of thirty-one observation arguments are now connected. All
nineteen relational laws have individual proofs but remain to be applied in
their source binder order. Negative ground faithfulness, the four-constructor
bounded invariant and independent functional deduction preservation remain open.

Exact next goal: extend domain_specialization through source field 104,
equality reflexivity. Prove that the specialized annotation converts to the
checked finite equality-reflexivity type, rewriting both predicate applications
and equality-table applications by their beta lemmas. Retain the dependent
suffix substitution by the chosen reflexivity proof. Repeat for the remaining
eighteen relation binders; do not claim full observation specialization or
no_back until all thirty-one arguments are checked.

Next command after the reflexivity-prefix addition (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
Fresh isolated full build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
--build-dir /tmp/pts-rk-domain-prefix.57mug7 --display=short --no-buffer`.
Its 204 Print Assumptions reports are closed under the global context;
there is no Axioms report. Exact command and output are retained in
verification/domain-prefix-full-2026-10-13.log.

Updated complete local CI exited 0, including pristine upstream and all
original stages, using
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/domain-prefix-final"
bash tools/check-local-ci.sh`. The functional audit has 96 closed reports.
Exact command and output: verification/domain-prefix-ci-2026-10-13.log.
The stage-by-stage logs and exit-code manifest remain in that diagnostic
directory. This is local CI evidence, not a new GitHub Actions result.

`git diff --check` and `bash -n tools/ci-check-direct-r.sh` both exited 0.
The two new proof modules, module registration, audit, CI stages, handoff
updates and verification logs remain uncommitted. User logs/ is untouched.

## Historical continuation: typed observation prefix, following 371f5bb

Request: proceed proving, then commit and push. Starting HEAD was
371f5bb3092531abde5e769f180dc26a42ef56a5 on main, with only untracked user logs/.
That local order-law commit is preserved. Its prior pushes timed out in Keychain;
the last verified remote was 4deb711. Theorem 7 is NOT complete.

Complete baseline local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/assembly-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Output: _build/local-ci-logs/assembly-baseline.log.

New checked results:
- DirectRTelescopeArguments.arguments_application: an actual typed dependent
  argument spine applied to a telescope-typed term has the exactly substituted
  suffix type. Each argument is checked against its preceding substitution.
- DirectRFiniteData.data_specialization supplies all eight finite data terms.
- initial_specialization additionally supplies the zero-domain proof.
- step_specialization additionally supplies successor-domain closure, proving
  actual original PTS typing after all ten applications, with the exact suffix
  substitution extending by both chosen proof terms.
- data_prefix_matches_source, initial_prefix_matches_source and
  step_prefix_matches_source identify these prefixes with the first 8/9/10
  fields of the EXISTING Codes.observation_fields, for every named suffix.

These are elimination/application theorems with an arbitrary typed input term,
not yet a closed implementation of the full observation. The eight data terms
are Fq, point q 0, capped successor/addition/multiplication, the finite membership
predicate, and the equality/order tables. Theorems are uniform for all q>0.
No annotation erasure, new axiom, or altered source/PTS rule was introduced.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteData.vo`.
Exit-0 logs: _build/local-ci-logs/finite-data-5.log (eight arguments),
finite-data-6.log (nine), finite-data-9.log (ten).
Earlier numbered failures remain recorded: unavailable notation/fin_case,
dependent substitution normalization through nested arrows, explicit var scope,
and shift-versus-lift_closed normalization. All were repaired and recompiled.

All nineteen relational laws remain individually proved, but only the first
ten of the full thirty-one observation arguments are now connected to the
source telescope. Negative ground faithfulness, the four-constructor bounded
invariant and independent functional deduction preservation remain open.

Exact next goal: package BinaryObservations.delta_addition and
delta_multiplication into the closed interleaved two-object closure certificates.
Convert their types from delta q u to app (Separation.predicate q) u, prove that
the next source annotations (fields 102/103) specialize to those types, and
extend step_specialization through both proof arguments. Then apply the nineteen
relational certificates, checking their dependent binder types in source order.
Only after all thirty-one arguments are checked should finite specialization of
LeAt and the uniform no_back refutation be claimed.

Next command after the binary-domain additions (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
Fresh isolated full build exited 0, including all legacy examples:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-finite-data.Ame1i4 --display=short --no-buffer
```

All 191 assumption reports are closed (83 in the functional audit). Exact public
theorem types, prefix definitions and full output are retained in
verification/finite-data-full-2026-10-13.log; raw output is in
_build/local-ci-logs/finite-data-full.log. Complete updated local CI also exited 0,
including pristine upstream and both added stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/finite-data-final"
bash tools/check-local-ci.sh`. Inventory and results are retained in
verification/finite-data-ci-2026-10-13.log and _build/local-ci-logs/finite-data-ci.log.
Shell syntax, actionlint and git diff --check pass. Remote CI has not been
inspected. This checked proof-progress checkpoint follows the preserved local
371f5bb commit and is authorized for ordinary commit and push.

The checkpoint was committed locally. `timeout 45 git push origin HEAD:main`
exited 124, again stalled in git-credential-osxkeychain. The local origin/main
tracking ref remains 4deb711; neither this checkpoint nor 371f5bb should be
reported as delivered. Unlock/authorize Git's macOS Keychain access, then run
`timeout 45 git push origin HEAD:main` with the documented local bin directory
on PATH and verify the remote ref. No force-push or credential workaround was
attempted. The user's untracked logs/ remains the only unrelated worktree path.

## Historical continuation: all finite order laws, following 4deb711

Request: proceed proving, then commit and push. Starting HEAD was
4deb711baab72f9a75eebb5325b5f0a87600437b on main. Only untracked user logs/
was present and is preserved. Theorem 7 is NOT complete.

Complete baseline local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/order-laws-baseline"
bash tools/check-local-ci.sh` with the documented local bin directory on PATH.
Raw output: _build/local-ci-logs/order-laws-baseline.log.

DirectRFiniteOrderLaws constructs all five remaining finite order certificates
uniformly for every q>0. With le(u,v)=Neg(C0 u v), s/add/mul the capped tables
and one=s(point q 0), their expanded closed types are:

```
Pi u:Fq. delta(u) -> le(u,s u)
Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) -> le(u,add u v)
Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) -> le(v,add u v)
Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) -> le(one,v) -> le(u,mul u v)
Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) -> le(one,u) -> le(v,mul u v)
```

Public theorem names: successor_order_realized, addition_order_left_realized,
addition_order_right_realized, multiplication_order_left_realized and
multiplication_order_right_realized. Each has only the premise 0<q.
The generic unary_law_realized/binary_law_realized turn uniformly valid native
order implications into original PTS inhabitants through the checked finite
expression reductions and Boolean Horn constructor. Each exported expanded
type has exact rank five; beta conversion retains all annotations and guards.
The q=1 multiplication branch is handled explicitly, not excluded.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteOrderLaws.vo`.
Exit-0 log: _build/local-ci-logs/order-laws-3.log. Earlier compiler failures
are retained: order-laws-1.log needed a third tactic branch for q=0/1/>1;
order-laws-2.log needed introduction of the conditional positivity premise
before applying capped_product_lower. Neither error was bypassed or admitted.

All nineteen relational observation laws now have individual proofs, in
addition to the four checked positive-domain certificates. This does NOT yet
constitute typed assembly of the full 31-argument observation telescope.
Negative ground faithfulness, the four-constructor bounded invariant and
independent functional deduction preservation remain open. No new axioms,
admissions, changed PTS rules or native-Prop replacement were introduced.

Exact next goal: construct the closed specialization of the fixed observation
telescope at q=K+2, supplying all eight finite data terms and all twenty-three
certificates in their dependent binder order. Prove conversion of each existing
expanded law type to its specialized telescope binder, then use ordinary PTS
application typing to obtain a specialization lemma for E/O. Use it to prove
`Realizes (Arrow (LeAt (numeral (S n)) (numeral n)) Bottom)` uniformly in n;
LeAt is the existing Codes application of O. The finite folds are
points n+1 and n at q=n+2 and the reversed comparison yields Top -> Bottom.
Do not declare the observation complete merely from a native list of proofs.

Next command after adding the assembly module and audit (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
Fresh isolated full build exited 0, including all legacy examples:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-order-laws.fq6laF --display=short --no-buffer
```

All 181 assumption reports are closed (73 in the functional audit). Exact public
theorem types, expanded definitions and full output are retained in
verification/order-laws-full-2026-10-13.log; raw output is in
_build/local-ci-logs/order-laws-full.log. Complete updated local CI also exited 0,
including pristine upstream and the new finite-order-laws stage:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/order-laws-final"
bash tools/check-local-ci.sh`. Inventory, stages and result are retained in
verification/order-laws-ci-2026-10-13.log and _build/local-ci-logs/order-laws-ci.log.
Shell syntax, actionlint and git diff --check pass. Remote CI has not been
inspected. This checked progress checkpoint follows 4deb711 and is authorized
for ordinary commit and push; it does not claim an unconditional Theorem 7.

The checkpoint was committed locally. Two attempts of
`timeout 45 git push origin HEAD:main` exited 124. The retry remained in
git-credential-osxkeychain; the remote is reachable but authentication stalls.
A credential-free ls-remote confirmed origin/main still at 4deb711 after the
first attempt, and the local tracking ref remained there after the retry.
No force-push or credential workaround was attempted. The only untracked path
is the preserved user logs/. Next delivery command, after unlocking/authorizing
Git's Keychain access: `timeout 45 git push origin HEAD:main` with the local bin
directory on PATH. Do not report this checkpoint as pushed without verification.

## Historical continuation: finite recursion equations, following 281a252

Request: retry push, proceed proving, commit and push. Starting HEAD was
281a252cd48a8f7bc43ef1174da29a219e744076 on main. Only untracked user logs/
was present and is preserved. The prior push stalled in macOS Keychain and was
terminated (143); this session's `timeout 45 git push origin HEAD:main` exited 0
and pushed 281a252 to origin/main. Theorem 7 is NOT complete.

Complete baseline local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/recursion-laws-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Raw log: _build/local-ci-logs/recursion-laws-baseline.log.

New checked modules:
- DirectRFiniteExpressions proves original PTS typing, substitution compatibility,
  bounded numerical evaluation and beta evaluation for nested finite-table
  expressions in two variables. This auxiliary syntax does not change D.
- DirectRFiniteRecursionLaws compiles a numerical equation valid on all selector
  pairs into a closed guarded PTS equality certificate. The two public instances
  have only the premise q>0, and realize the expanded types:

```
Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) ->
  Neg(R0 (add (s u) v) (s (add u v)))
Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) ->
  Neg(R0 (mul (s u) v) (add v (mul u v)))
```

Here s/add/mul are capped tables and R0 is the finite equality test. The
public names are addition_successor_realized and multiplication_successor_realized.
Their expanded types have checked rank five and retain both domain guards.
The generic equation_realized uses native equations only to build the selector
branch proofs, followed by original PTS positive-membership elimination.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteRecursionLaws.vo`.
Exit-0 log: _build/local-ci-logs/recursion-laws-3.log. Earlier compiler errors
are retained in recursion-laws-1.log (beta_app needed eapply for its intermediate
term) and recursion-laws-2.log (the capped identities live in CappedArithmetic,
not ArithmeticCore). No error was bypassed or admitted.

Fourteen of nineteen relational observation certificates are now proved,
including all five arithmetic equations. Five order-propagation laws remain.
Full observation assembly, negative ground faithfulness, the four-constructor
bounded invariant, and independent functional deduction preservation remain open.
The external set model is out of scope under the replacement AGENTS instructions.

Exact next goal: uniformly for q>0, construct
`Pi u:Fq. delta(u) -> Neg(C0 u (s u))`, where C0 is the finite order test.
Use a rank-two unary family and guarded_finite_realized. The point branch is
i <= min(S i,pred q), for i<q; construct negative_true after checked table
conversion. Then compile the two addition and two conditional multiplication
order-propagation laws with the finite-expression evaluator.

Next command after implementing the next law (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
Fresh isolated full build exited 0, including all legacy examples:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-recursion-laws.3JZyHM --display=short --no-buffer
```

All 170 assumption reports are closed (62 in the functional audit). The exact
public theorem types, expanded definitions and output are retained in
verification/recursion-laws-full-2026-10-13.log; raw output is in
_build/local-ci-logs/recursion-laws-full.log. Complete updated local CI also
exited 0, including pristine upstream and the two new stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/recursion-laws-final"
bash tools/check-local-ci.sh`. Its inventory and results are retained in
verification/recursion-laws-ci-2026-10-13.log and raw
_build/local-ci-logs/recursion-laws-ci.log. Shell syntax, actionlint and
git diff --check pass. Remote CI has not been inspected. This checked progress
checkpoint follows 281a252 and is authorized for ordinary commit and push.

## Historical continuation: finite zero laws, following 9ef8568

Request: proceed proving Theorem 7, commit and push. Starting HEAD was
9ef85681155441855a38295ba6c077b3705d38a0 on main. Only the user's untracked
logs/ was present; it is preserved and excluded from the commit.
Theorem 7 is NOT complete. The original functional interpretation is unchanged.

Baseline complete local CI driver, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/arithmetic-laws-baseline"
bash tools/check-local-ci.sh` with the documented local bin directory on PATH.
Raw log: _build/local-ci-logs/arithmetic-laws-baseline.log.

DirectRFiniteZeroLaws now constructs three original PTS inhabitants, for every
q>0, of these expanded closed types (R0 is the finite equality test):

```
Pi u:Fq. delta(u) -> Neg(R0 (add (point q 0) u) u)
Pi u:Fq. delta(u) -> Neg(R0 (mul (point q 0) u) (point q 0))
Pi u:Fq. delta(u) -> Neg(R0 (mul u (point q 0)) (point q 0))
```

The public theorems are addition_zero_realized,
multiplication_zero_left_realized and multiplication_zero_right_realized.
Their only premise is 0<q. Generic zero_law_realized accepts a typed binary
operation and its pointwise beta action; the public laws discharge both using
the existing capped tables. expanded_type_typed proves exact rank five and
expanded_type_beta preserves annotations and the interleaved domain guard.

The first incremental build exited 0, without any compiler-error iteration:
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteZeroLaws.vo` with documented OPAMROOT/PATH.
Output: _build/local-ci-logs/zero-laws-1.log.

Fresh isolated full build exited 0, including all legacy examples:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-zero-laws.cYmQHT --display=short --no-buffer
```

All 162 assumption reports are closed (54 in the functional audit). The public
theorem types, expanded definitions and fresh output are retained in
verification/zero-laws-full-2026-10-13.log; raw output is in
_build/local-ci-logs/zero-laws-full.log. Complete updated local CI also exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zero-laws-final"
bash tools/check-local-ci.sh`. Its inventory, stages and result are retained in
verification/zero-laws-ci-2026-10-13.log and _build/local-ci-logs/zero-laws-ci.log.
Shell syntax, actionlint and git diff --check pass. Remote CI is not inspected.
This proof-progress checkpoint follows 9ef8568 and is authorized for ordinary
commit and push; it is not a completed Theorem 7.

Twelve of nineteen relational observation laws are now proved. Seven remain:
addition/successor and multiplication/successor equations, and the five order
propagation laws. The full 31-argument observation assembly, negative ground
faithfulness, four-constructor bounded invariant, and independent functional
deduction preservation remain open. No new axioms or admissions were added.

Exact next goal: uniformly for q>0, construct
`Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) ->
Neg(R0 (add (s u) v) (s (add u v)))`, for the capped successor and addition.
Use guarded_finite_realized with a rank-two binary family, reduce selector
branches using capped_successor_action and capped_addition_action, and prove
the resulting capped index equation. The analogous multiplication step must
handle a zero right factor separately when reasoning about saturation.

Next command after implementing the next law (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

## Historical continuation: operation congruence, following bc5cee0

Request: proceed proving Theorem 7, commit and push. Starting HEAD was
bc5cee044179b6adbd3ec5ed6415d560886fffd5 on main. The user's untracked logs/
is preserved and excluded from the commit. Theorem 7 is NOT complete.

The complete baseline local CI driver exited 0, including pristine upstream:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/operation-congruence-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Raw output: _build/local-ci-logs/operation-congruence-baseline.log.

New checked results: FiniteUnaryCongruence.successor_congruence_realized,
FiniteBinaryCongruence.addition_congruence_realized and
FiniteBinaryCongruence.multiplication_congruence_realized, uniformly for q>0.
Each returns Realizes of the expanded, interleaved domain-guard telescope.
The unary conclusion is Neg(R0 (s u) (s v)) under Neg(R0 u v).
The binary conclusion is Neg(R0 (op u v) (op u' v')) under both equality
premises; all four objects have their own immediately following delta guard.
R0 is the finite equality relation, s/op the existing capped selector tables.
Explicit beta equivalences and rank-five formation retain all annotations.

The generic proofs require typed operations and admitted outputs on every
selector tuple. Existing delta_successor/delta_addition/delta_multiplication
discharge these premises, without an assumed equality-congruence theorem.
RelationTables.boolean_premises_realized handles Boolean premises with an
arbitrary rank-one negative conclusion; it does not assert general ex falso.

Incremental commands (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteUnaryCongruence.vo` and the analogous
DirectRFiniteBinaryCongruence.vo target. Both compiled; exit-0 output is in
_build/local-ci-logs/unary-operation-congruence-2.log and
binary-operation-congruence-2.log. First attempts retained in numbered logs:
the unary conversion needed lift_closed_zero normalization before conversion;
the binary operation type needed an explicit closed_term scope annotation.
Neither failure was bypassed or admitted.

Nine of nineteen relational observation certificates are now proved. Ten
remain: five arithmetic equations and five order-propagation laws. The entire
31-argument observation, negative ground faithfulness, four-constructor bounded
invariant, and independent functional deduction preservation remain unfinished.

Exact next goal: the finite addition-zero certificate, uniformly for q>0:
`Pi u:Fq. delta(u) -> Neg(R0 (add z u) u)` with z=point q 0 and
add=capped_addition q. Reduce each admitted selector branch with the checked
binary table action, prove the bounded native index equality, and construct
the PTS negative equality inhabitant before closing the guarded telescope.

Next command after implementing that certificate (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

Fresh isolated full build exited 0, including the legacy examples:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-operation-congruence.25yLVh --display=short --no-buffer
```

All 156 assumption reports are closed (48 in the functional audit). Exact
public theorem types, expanded definitions and output are retained in
verification/operation-congruence-full-2026-10-13.log. Raw output:
_build/local-ci-logs/operation-congruence-full.log.
The complete updated local CI driver also exited 0, including pristine upstream:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/operation-congruence-final"
bash tools/check-local-ci.sh`. Output is retained in
verification/operation-congruence-ci-2026-10-13.log and raw
_build/local-ci-logs/operation-congruence-ci.log. Shell syntax, actionlint and
git diff --check pass. Remote CI has not been inspected.
This checked proof-progress checkpoint follows bc5cee0 and is authorized for
ordinary commit and push. It does not claim an unconditional Theorem 7.

## Historical continuation: finite transitivity and congruence, following 5b8e676

Request: proceed proving Theorem 7, commit and push. Starting HEAD is
5b8e676f288aa6c12e0c61d7e6b60cab5692754d on main. Only the user's untracked
logs/ was present; it is preserved. Theorem 7 is still NOT complete.

The baseline complete local CI driver exited 0, including pristine upstream:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/theorem7-transitive-baseline"
bash tools/check-local-ci.sh` (with the documented local bin directory on PATH).
Log: _build/local-ci-logs/theorem7-transitive-baseline.log.

New checked modules:
- DirectRGuardedFiniteLaws opens arbitrary finite telescopes of interleaved
  selector/domain binders, then uses the already checked rank-three finite
  eliminator. guarded_typed proves exact rank r for arity zero and max(5,r)
  otherwise. No membership certificate is eliminated into the rank-five
  guard telescope; all guards are opened first.
- DirectRFiniteTransitivity constructs closed equality- and order-transitivity
  certificates for every q>0. Their PUBLIC types are the expanded three-object
  telescopes, with a domain guard immediately after each object.
- DirectRFiniteCongruence proves equality transport in both arguments of every
  finite Boolean relation, hence the observation's order-congruence certificate.
  Its public type is the expanded four-object interleaved telescope.

All three laws are original PTS inhabitants. Explicit beta equivalences and
rank-five formation proofs connect the generic curried families to those
expanded statements; annotations are retained. Boolean Horn branch validity
is discharged using native equality/transitivity only as numerical side facts.
There is no new axiom, admission, cumulativity or unchecked cast.

Incremental commands used the documented opam switch and
`timeout 90 dune build --display=short --no-buffer TARGET.vo`.
Exit-0 logs under _build/local-ci-logs: guarded-telescope-5.log,
finite-transitivity-4.log, finite-congruence-2.log, finite-laws-audit-2.log.
The extended functional audit has 38 closed assumption reports.
Earlier numbered compiler failures remain available: fixed renaming scope,
dependent empty-index elimination, list-predicate inference, a bracket typo,
and a rank-max arithmetic normalization step. None was admitted.
The updated complete local CI driver exited 0, including the three added
stages and pristine upstream; raw log _build/local-ci-logs/finite-laws-ci-driver.log.
Fresh isolated FULL build exited 0, including every legacy example:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-finite-laws.uRpSAn --display=short --no-buffer
```

All 146 assumption reports are closed (38 in the functional audit). Exact
public types, expanded definitions and full output are retained in
verification/finite-laws-full-2026-10-13.log; raw log:
_build/local-ci-logs/finite-laws-fresh-full.log. The local CI inventory, stage
statuses and exit result are in verification/finite-laws-ci-2026-10-13.log.
Shell syntax, actionlint and git diff --check pass. This checkpoint is committed
as proof progress after 5b8e676; it does not claim remote CI success or a complete
Theorem 7. Ordinary commit and push are authorized by the current request.

Exact next proof goal: for every q>0, construct the closed successor-congruence
certificate
`Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) ->
Neg(R0 u v) -> Neg(R0 (s u) (s v))`,
where R0 is the equality test and s is capped_successor q. Use the generic
guarded_finite_realized theorem and capped table beta action. Then handle
addition/multiplication congruence analogously using binary_table_action.

Six of the nineteen relational observation certificates are now proved:
equality reflexivity/symmetry/transitivity, order reflexivity/transitivity,
and order congruence. Thirteen remain: three operation congruences, five
arithmetic equations and five order-propagation laws. Assemble the entire
observation telescope before claiming no_back or negative ground faithfulness.
The four-constructor invariant and independent functional deduction preservation
also remain open. This checkpoint is NOT an unconditional Theorem 7.

Next build command after implementing the next law (with documented OPAMROOT/PATH):

```sh
opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short --no-buffer \
  theories/DirectRFunctionalAudit.vo
```

## CI continuation: supplied logs_103946087456

The supplied job reports a runner shutdown, exit 143, not a Rocq diagnostic or
elapsed workflow/stage limit. See CI-103946087456.md for exact evidence.
Locally reproduced a separate memory bottleneck in the legacy examples:
reifying the entire generated syntax in Ltac grew to approximately 19 GB.
The compact-witness repair preserves the generator, statements and fuel 65536.
DirectRTests now compiles (exit 0), with all nine assumption reports closed;
log `_build/local-ci-logs/ci-examples-compact.log`. A fuel-256 experiment timed
out (124) and was reverted. The original high-memory attempt was manually
terminated (143). A fresh full build in /tmp/pts-rk-ci-repaired.sh2eTQ exited 0;
the complete local CI driver also exited 0, including pristine upstream and
all legacy examples. Exact output is in verification/ci-repaired-full-2026-10-13.log
and _build/local-ci-logs/ci-repaired-driver.log. CI repair commit 61330e3 was
pushed to origin/main. No subsequent remote CI outcome has been inspected.
The driver now records TERM/INT interruptions without weakening any check.
Signal-injection test, shell syntax and actionlint passed.

## Current request and exact targets

Active focus (latest user request): continue Theorem 7, commit and push
the checked proof progress. See the current continuation at the top.
Theorem 7 is NOT complete. Theorem 4 remains proved as Theorem4.theorem4.
The PTS set model is not being advanced in this continuation.

The authoritative new reference is
`PTS_rk_interprets_Tarski_Mostowski_Robinson_arithmetic_R_harmonized.tex`.

- Theorem 4, label `main`: the unary-domain relational interpretation.
- Theorem 7, label `thm:direct-R`: the arithmetic-expression functional interpretation.
- Both include all-index axiom realization, preservation of independently
  defined classical source deductions, ground proofs/refutations, and
  nonfaithfulness on arbitrary sentences.
- The unary Theorem 4 is proved. The functional Theorem 7 remains open.
  The old `Kernel.Theorem5Target` is only the functional axiom-witness component.
- The latest user additionally requests the paper's PTS set model using
  rocq-archive/zfc, after the arithmetic work, with separate commits/pushes.
  This supersedes the older exclusion of set models. Its soundness has NOT
  been formalized. The paper states ZF+GCH, not unconditional ZFC.
- Ordinary commits/pushes are authorized. No gh, publish.sh, force-push, or merge.

## Checkout and environment

The earlier continuation started at main commit
`04cf08bb26def30c100ebb1c6cceca6a4de75138` (complete unary relational Theorem 4).
Only the existing untracked logs/ directory was present. It was preserved.

Arithmetic progress checkpoint on main: `a16646b`
(`Prove ground arithmetic and add harmonized unary foundations`), pushed.
It follows `b6fa20660860258717637426605353e0bf3e38e5`.
Inspect git log/status for subsequent model work; do not reset.
User's new harmonized TeX is preserved, including its
pre-existing trailing space at line 287. Downloaded `logs/` remain untouched
and untracked.

Installed local environment: `$HOME/.local/share/pts-rk-ci`; opam root
`opam/`, switch `pts-rk-ci`, binaries `bin/`, native ARM GMP `native/`.
OCaml 4.14.2, Rocq core/runtime 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
Dune 3.23.1, opam 2.6.1, actionlint 1.7.12. GNU timeout is available.
The pristine upstream requires Rocq 9.2's Create Rewrite HintDb.

## Actually compiled

### Historical functional checkpoint through 5b8e676

The current continuation at the top supersedes this checkpoint's remaining-law
counts and next goal; its commands and logs below remain historical evidence.

The target is the harmonized thm:direct-R, using the EXISTING Codes.Domain,
Good, Equality, Order and four expression constructors, not Unary.Domain or a
graph interpretation. Its desired closed preservation judgment is
`exists p, @typ nat RankSorts 0 ε p (FirstOrder.sentence_translation A)` for
each independent classical functional derivation of A. FirstOrder currently
has syntax/translation but no complete independent deduction judgment.

New checked modules:
- DirectRFunctionalTerms: arbitrary open-term typing, Good closure and observed
  closure; every closed expression has a genuine EqAt proof to its numerical
  value's numeral. This covers arbitrary nested addition and multiplication.
  True ground equations and comparisons now have PTS inhabitants for arbitrary
  closed source terms, not just numeral instances.
- DirectRFunctionalLogic: fixed, fully annotated equality/order stability
  certificates over the entire 31-argument arithmetic observation telescope;
  contextual double-negation elimination for the two atomic relations.
- DirectRBinaryTables: generic binary selector tables, their typing and uniform
  beta action; capped addition and multiplication as specializations.
- DirectRBinaryObservations: positive delta closure for every bounded binary
  table, by two rank-three motive eliminations, then abstraction over the
  target membership continuation. Capped addition/multiplication closure are
  checked corollaries. No selector-canonicity assumption is used.
- DirectRRelationTables: generic equality/order test matrices, rank-one result
  typing and point computation, plus PTS proofs of true negative entries and
  contradiction from false negative entries. The latest continuation also
  compiles arbitrary Boolean Horn branches to PTS inhabitants, uniformly in
  the number of premises, and proves their exact rank (two or three).
- DirectRFiniteLawElimination: exact lifting via J2 -> A, and elimination of
  arbitrarily many positively admitted selector arguments into a law of rank
  at most three. The branch premise ranges over all bounded tuples, uniformly
  in arity. This is derived from original typing, not assumed cumulativity.
- DirectRFunctionalFiniteLaws: closed guarded equality- and order-reflexivity
  and equality-symmetry certificates, uniform in every positive selector arity.
  Symmetry eliminates two positively admitted arguments; its false-premise
  branch constructs only a negative conclusion. The other 16
  relational certificates of the functional observation are not yet proved.

Baseline build of DirectR.vo and DirectRRelationalAudit.vo exited 0; log
_build/local-ci-logs/theorem7-baseline.log. Incremental commands use
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short --no-buffer`
with the corresponding module target. Exit-0 logs: functional-terms-build-2.log,
functional-ground-build-2.log, functional-logic-build-1.log,
binary-tables-build-7.log, binary-observations-build-2.log,
relation-tables-build-3.log, finite-law-elimination-build-4.log,
functional-finite-laws-build-1.log. All are under
_build/local-ci-logs; earlier failed attempts remain available. Fixed actual
errors in rename/substitution normalization, intermediate beta terms, and
missing imports; no proof was admitted or assumed.

Exact remaining proof obligations:
1. Apply the checked relation tables and arbitrary-arity finite-law eliminator
   to the remaining 16 guarded relational laws. Prove their arithmetic-expression
   branch computation and assemble all 23 proof arguments of the functional
   finite observation, then derive functional no_back and unequal-numeral
   refutations. Reflexivity and symmetry are done; the next law is guarded
   equality transitivity (then order transitivity using the same construction).
2. Prove the four-constructor positive invariant with functional CaseAt, using
   transferred guarded laws. Unary bounded_case is NOT this theorem.
3. Complete independent functional deduction preservation, formula stability
   and guarded equality transport. Connect source countermodel soundness and
   ground negative refutations; assemble an unconditional final Theorem 7.
Do not substitute Theorem4.theorem4 or the conditional generator record.

Earlier isolated proof build exited 0 (before symmetry/Horn branch additions):

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-functional-final.ILSavU --display=short --no-buffer \
  theories/DirectRFunctionalAudit.vo theories/DirectRRelationalAudit.vo \
  theories/DirectRUnaryAudit.vo theories/DirectR.vo \
  theories/DirectRArithmetic.vo models/SetFunctions.vo
```

All 25 new functional Print Assumptions queries are closed under the global
context; 124 closed reports including the previous audits. Theorem 4 rebuilt
successfully. Exact public types and output are retained in
verification/functional-progress-2026-10-13.log, raw log
_build/local-ci-logs/functional-progress-fresh.log. The earlier isolated build
in /tmp/pts-rk-functional-check.LbunRw also exited 0 before the last finite-law
extensions; its raw log is functional-foundations-fresh.log.
No final unconditional Theorem 7 type exists yet; this audit explicitly says so.

Earlier full-suite command `opam exec --switch=pts-rk-ci -- timeout 120 dune build
--build-dir /tmp/pts-rk-functional-final.ILSavU --display=short --no-buffer`
exited 124 in unchanged DirectRTests. Raw log:
_build/local-ci-logs/functional-progress-full.log; tracked transcript:
verification/functional-progress-full-2026-10-13.log. This is not a successful
full-suite build or remote CI run. Whitespace, shell syntax and actionlint checks
pass. Eight new CI stages cover the added proof
modules; no stage or timeout was removed or weakened. This earlier timeout is
superseded by the successful full build after the compact-witness CI repair;
retain it as historical evidence, not the current result. The functional work
is a separate progress commit after 61330e3, NOT a completed Theorem 7.
Existing untracked logs/ is untouched.

Exact next build command, after implementing the next guarded finite law:

```sh
opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short --no-buffer \
  theories/DirectRFunctionalFiniteLaws.vo theories/DirectRFunctionalAudit.vo
```

The next exact goal is a closed proof of the telescope
`Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) -> Pi w:Fq. delta(w) ->
Neg(R0 u v) -> Neg(R0 v w) -> Neg(R0 u w)` for R0 = equality_test q.
Use delta_eliminate_arguments at rank three, relation-table point computation,
and boolean_horn_realized. The analogous order law uses Nat.leb transitivity.
Do not rely on the unchecked named generator or on a finite successful example.

Latest checked public certificate:
`forall q, 0 < q -> Realizes (FunctionalFiniteLaws.symmetry_type q Nat.eqb)`.
Here symmetry_type is the exact interleaved telescope
`Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) -> Neg(R0 u v) -> Neg(R0 v u)`.
Realizes means `exists p, @typ nat RankSorts 0 ε p T`, not a checker predicate.
Incremental symmetry build exited 0 in functional-symmetry-12.log; the extended
audit (including arbitrary Boolean Horn branches) exited 0 in
functional-horn-1.log. Earlier numbered failures are retained in
_build/local-ci-logs and were repaired, not admitted.

Final fresh FULL build of this functional progress checkpoint exited 0:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-theorem7-progress.cWBK5u --display=short --no-buffer
```

All modules, including DirectRTests, compiled. The functional audit has 29
closed assumption reports; the whole fresh build has 137. Public types and
full output are retained in verification/theorem7-progress-full-2026-10-13.log
(raw: _build/local-ci-logs/theorem7-progress-full.log).
The preceding complete local CI driver's inventory/stages/result are retained
in verification/ci-repaired-stages-2026-10-13.log; every stage passed, including
pristine upstream. Shell syntax, actionlint and git diff --check also pass.
No new assumptions, admissions or checking bypasses were introduced.
This is verified proof progress, not an unconditional final Theorem 7.

### Complete unary relational Theorem 4, following a13b0d6

DirectRRelationalTranslation now proves implication/universal introduction,
typed and admitted environment extension, arbitrary-formula stability, classical
DNE and equality reflexivity. Stability includes arbitrary nesting of guarded
quantifiers. DirectRLogic adds double-negation mapping using actual PTS terms.

DirectRRelationalEquality proves term and binary-operation congruence, atomic
equality/order transport, arbitrary-formula transport and equality replacement.
The quantifier case compares the same bound object and Good guard; it does NOT
assume that Good is invariant under raw E. Binary congruence uses fully annotated
lambda abstraction and beta conversion only.

DirectRRelationalDeduction proves preservation by induction on the INDEPENDENT
Relational.derives judgment, with all nine constructors handled. Its closed
corollary is exactly:

    forall A : Relational.formula 0, Relational.derives [] A ->
      exists p, @typ nat RankSorts 0 ε p (RelationalTranslation.sentence A).

DirectRRelationalCountermodel connects the existing option-nat SOURCE model to
the independent calculus. Atomic decidability and formula stability prove
classical-rule soundness constructively, without any native classical axiom.
It proves non-derivability of forall x, x <= x. This is not a PTS set model.

DirectRTheorem4 combines all-index source axiom realization, full deduction
preservation, proofs/refutations for every closed source atom, and nonfaithfulness.
The latter uses Unary.rho_realized and source order_reflexivity_underivable.
Theorem4.theorem4 is a conjunction of those unconditional conclusions in original
typ, not a record hypothesizing preservation or a finite test collection.

Baseline: `opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer
theories/DirectRRelationalAudit.vo`, exit 0, relational-intro-baseline.log.
Incremental commands use `opam exec --switch=pts-rk-ci -- timeout 90 dune build
--display=short --no-buffer` with the corresponding module target. Successful
logs under _build/local-ci-logs: relational-intro-build-2.log,
relational-stability-build-4.log, relational-equality-build-6.log,
relational-transport-build-2.log, relational-deduction-build-1.log,
relational-countermodel-build-5.log and theorem4-build-1.log. Earlier failed
attempts are retained: scope inference, explicit intermediate terms, a missing
decidability import and tactic syntax were repaired; no assumption was added.
The final incremental audit reports all 34 assumptions queries closed.

Fresh isolated build exited 0:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-theorem4-check.CvEbQd --display=short --no-buffer \
  theories/DirectRRelationalAudit.vo theories/DirectRUnaryAudit.vo \
  theories/DirectR.vo theories/DirectRCountermodel.vo \
  theories/DirectRArithmetic.vo models/SetFunctions.vo
```

Log: _build/local-ci-logs/theorem4-fresh.log. All original PTS dependencies and
the complete unary proof rebuilt. There are 99 closed assumption reports across
the audits, including all 34 relational audit queries. The final unconditional
theorem types and the compiler transcript are retained in
verification/theorem4-2026-10-13.log. No full-suite or remote-CI success is inferred
from this proof-target build.

Full-suite command `opam exec --switch=pts-rk-ci -- timeout 120 dune build
--build-dir /tmp/pts-rk-theorem4-check.CvEbQd --display=short --no-buffer`
exited 124 in unchanged DirectRTests. Raw log: _build/local-ci-logs/theorem4-full.log;
tracked transcript: verification/theorem4-full-2026-10-13.log. This repeats the
previous legacy-examples timeout, not a compiler error in the new proof. No CI
stage or timeout was removed or weakened; four new stages cover equality,
deduction, source countermodel and the final theorem. Shell syntax, actionlint,
and git diff --check pass. The user logs/ directory remains untouched/untracked.
The changes are prepared for the authorized ordinary commit/push with message
`Prove unary relational Theorem 4`.

Next exact command (recheck the final theorem and transitive assumptions):

```sh
opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer \
  theories/DirectRRelationalAudit.vo
```

No unary Theorem 4 proof goal remains. Preserve the separate functional target
and model work; do not silently relabel either as completed by this theorem.

### Independent relational source and structural translation, following 7e2e736

DirectRRelationalSyntax defines independent scoped terms/formulas and the
relational arithmetic schemes. Its inductive derives judgment has hypothesis,
theory, implication introduction/elimination, universal introduction/elimination,
classical DNE, equality reflexivity and formula equality replacement. Universal
introduction weakens the entire source context, encoding the freshness condition.
No target typing/inhabitation occurs in any derivation constructor. Only Fin is
shared with Syntax. Conjunction/disjunction/existential/iff are classical
abbreviations over falsity/implication/universal with the paper's fixed encoding.

DirectRRelationalTranslation proves term/formula renaming and substitution,
including instantiate_translation at binders; exact formula ranks; original
PTS term typing and Good evidence under typed/admitted environments; closed
source term translation to unary numerals; implication and guarded universal
elimination. DirectRRelationalAxioms proves the original typing judgment for
the structural translation of every independently stated source axiom, in
arbitrary target contexts. DirectRRelationalGround proves true/false equality,
order, addition-graph and multiplication-graph source atoms for ALL closed
source terms, not just a separate family of target-side atom definitions.

Baseline command `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRUnaryAudit.vo` exited 0, log
_build/local-ci-logs/relational-source-baseline.log. Incremental commands used
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short --no-buffer`
with targets DirectRRelationalSyntax.vo (relational-syntax-build-3.log),
DirectRRelationalTranslation.vo (relational-translation-build-2.log and -3.log),
DirectRRelationalGround.vo (relational-ground-build-1.log),
DirectRRelationalAxioms.vo (relational-axioms-build-1.log), and both last targets
(relational-rules-build-1.log): all exit 0. Logs remain in _build/local-ci-logs.
Earlier failed scripts (source context weakening and an omitted falsity branch
in a structural induction) remain recorded and were repaired without admissions.

Fresh isolated build exited 0: `opam exec --switch=pts-rk-ci -- timeout 300
 dune build --build-dir /tmp/pts-rk-source-check.Vath3i --display=short --no-buffer
 theories/DirectRRelationalAudit.vo theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo models/SetFunctions.vo`.
All original PTS dependencies and new source/translation modules rebuilt.
All 21 new Print Assumptions queries are Closed under the global context,
with 86 closed reports including prior audits. The exact derivation definition,
public theorem types and compiler transcript are tracked in
`verification/relational-source-2026-10-13.log`; local copy is
`_build/local-ci-logs/relational-source-fresh.log`. Whitespace, shell syntax,
and actionlint checks passed. Five dedicated source/translation CI stages
were added; no existing stage or timeout was removed or weakened.
Full build `opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-source-check.Vath3i --display=short --no-buffer`
exited 124 in unchanged DirectRTests. Exact output is retained in
`verification/relational-source-full-2026-10-13.log` and the local
`_build/local-ci-logs/relational-source-full.log`. No full green build or
remote CI success is claimed. User logs/ and the TeX were left untouched.

Theorem 4 remains INCOMPLETE. Exact next goal: formula stability and formula
equality transport for two typed/admitted environments whose corresponding
terms are E-related. Use these to preserve classical DNE and equality_replace;
prove introduction rules and induction on Relational.derives. Then prove
semantic soundness of that independent system in the existing source
countermodel to establish non-derivability of universal reflexivity. No final
deduction-preservation theorem or source non-derivability theorem is yet present.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRRelationalAudit.vo`.

### All relational axiom schemes, following cf105ba

- DirectRUnaryBounded proves both directions of bounded order for arbitrary
  admitted objects, packages the negative biconditional, and proves R4_realized
  for every cutoff. It retains the Good guard. The converse uses stable O;
  the forward large branch is refuted by the checked no_back witness.
- DirectRUnaryEvaluation now proves fully annotated Church normal forms and
  the all-index beta equations Add nu_m nu_n =beta nu_(m+n), and
  Mul nu_m nu_n =beta nu_(m*n). No eta equality or altered annotation is used.
- DirectRUnaryArithmetic proves relational R1/R2 for arbitrary admitted third
  arguments. Ground addition/multiplication atoms have witnesses when the
  external numerical equation is true, and internal Neg witnesses when false.
- all_axioms_realized covers every relational axiom index (R3 carries its
  specified distinctness side condition). The audit restates it as
  `forall a, exists p, @typ nat RankSorts 0 epsilon p (axiom_translation a)`.
  This is axiom realization, NOT preservation of an independent proof system,
  and NOT the functional Kernel.Theorem5Target.

Baseline: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRUnaryAudit.vo`, exit 0, r4-baseline.log.
Meaningful incremental builds (same command with `timeout 90` before dune):
DirectRUnaryBounded.vo (r4-build-3.log), DirectRUnaryEvaluation.vo
(unary-arithmetic-build-2.log and unary-arithmetic-build-4.log), and
DirectRUnaryArithmetic.vo (unary-relational-arithmetic-build-1.log and
unary-relational-arithmetic-build-2.log), all exit 0. Logs are retained in
_build/local-ci-logs. Earlier numbered failures were opaque Neg substitution,
closed-term shift normalization, and a missing parenthesis, all repaired.

Fresh isolated build exited 0: `opam exec --switch=pts-rk-ci -- timeout 300
 dune build --build-dir /tmp/pts-rk-relational-check.8oST6u --display=short
 --no-buffer theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo models/SetFunctions.vo`.
Original PTS dependencies, the new proofs and the existing modules rebuilt
successfully. All 13 new Print Assumptions queries report Closed under the
global context; the transcript contains 65 such reports including previous
and set-function audits. Exact types/output are retained in
`verification/unary-relational-2026-10-13.log`, with local working copy
`_build/local-ci-logs/relational-fresh.log`. Whitespace, shell syntax and
actionlint passed. CI now explicitly checks unary bounded-order and arithmetic
before the expanded audit; no old stage or timeout was removed or weakened.
Full build: `opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-relational-check.8oST6u --display=short --no-buffer`
exited 124 while compiling unchanged DirectRTests. Exact output is retained
in `verification/unary-relational-full-2026-10-13.log` and the local
`_build/local-ci-logs/relational-full.log`. No full green build or remote CI
success is claimed. Existing user logs/ and the TeX were left untouched.

Theorem 4 remains incomplete. Exact next goal: define an independent scoped
classical deduction system for the relational signature {0,S,=,<=,A,M}, with
its own axiom schemes and rules; define its structural guarded negative
translation and prove substitution, formula stability, admitted equality
replacement and rule preservation. Do not define source provability as target
inhabitation. Connect the existing source countermodel to semantic soundness
of that system to establish non-derivability of universal reflexivity. Ground
source terms must also be connected structurally to the checked numeral atoms.
DirectRFirstOrder is the old functional-signature translation (binary + and *
terms, no ternary A/M formulas); do not mistake it for the relational system
or silently reuse its distinct Codes.Domain in the unary interpretation.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRUnaryAudit.vo`.

### Upward closure and numeral evaluation, following b89cdd2

DirectRFiniteUp.upward_realized now constructs the uniform closed judgment
`Realizes (Pi u:F_(c+1). delta_(c+1)(u) -> Neg(Pu) -> Neg(P(su)))`.
Its exact-rank-three motive is eliminated using the positive delta predicate.
Below the cap an inhabitant of Top supplies the contradiction; at the cap
the negative implication is identity. No positive ex-falso is used.
DirectRUnaryEvaluation.numeral_evaluation proves the actual unary numeral
fold into arbitrary scoped arguments, and finite_numeral_evaluation connects
it to the capped selector at min(k,c), uniformly in both external indices.
Fixed open zero/successor beta schemas are instantiated by the original
replace_equiv lemma; this is not finite testing or annotation erasure.
Incremental commands: `opam exec --switch=pts-rk-ci -- dune build
 --display=short --no-buffer theories/DirectRFiniteUp.vo`, then the same
command with DirectRUnaryEvaluation.vo and DirectRSeparation.vo.
Logs `_build/local-ci-logs/up-build-2.log`, `unary-evaluation-build-1.log`,
`separation-build-2.log` exited 0. The last includes exact observation
predicate d0/ds/Up wrappers and a checked fixed order eliminator.
The first Up attempt needed an explicit scope; the first observation wrapper
needed an explicit rank-one formation proof. Both failures are retained.
Specializing the complete telescope with unstructured substitutions was
interrupted (exit 130); a repeat timed out at 45 seconds (exit 124).
Logs `separation-build-3.log` and `separation-build-4.log` preserve these.
Compact intermediate observation types now solve the telescope specialization;
the new replace_observation lemma keeps closed encodings opaque. Remaining
compiler errors were scope/rank inference and selector substitution, repaired
without changing a statement. `separation-build-7.log`, `separation-build-10.log`
and `separation-build-11.log` exited 0 (60-second command limit).
Separation.no_back_realized is now unconditional for every external k:
`exists p, @typ nat RankSorts 0 ε p
 (Neg (Unary.O (Unary.numeral (S k)) (Unary.numeral k)))`.
Separation.ground_order_refutation handles every j<i, and
Separation.R3_realized handles every i<>j with an internal E refutation.
No hypothesis asserts canonicality of raw selectors or the desired theorem.
Theorem 4 remains incomplete. Exact next goal: both directions of relational
R4, combining bounded_case_realized with no_back_in_context to eliminate
the large branch, and the existing ground comparison for the converse.
Also remaining: unary arithmetic beta equations and relational R1/R2,
ground ternary atoms, and independent classical deduction preservation.
Fresh isolated build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
 --build-dir /tmp/pts-rk-separation-check.Xxoo9H --display=short --no-buffer
 theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo models/SetFunctions.vo`.
The original PTS dependencies were rebuilt from source alongside the new
proofs and existing interpretation modules. All ten new Print Assumptions
queries are closed under the global context (52 closed reports in total,
including existing modules). Exact types and compiler output:
`verification/unary-separation-2026-10-13.log`; working copy:
`_build/local-ci-logs/separation-fresh.log`.
Whitespace, shell syntax and actionlint checks passed. Dedicated finite-Up,
unary-evaluation and separation stages were added without removing old checks.
The subsequent full build exited 124 after 120 seconds in unchanged
DirectRTests: `opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-separation-check.Xxoo9H --display=short --no-buffer`.
Output is retained in `verification/unary-separation-full-2026-10-13.log`
and `_build/local-ci-logs/separation-full.log`. No full green build or remote
CI result is claimed. Only the pre-existing user logs/ directory remains
outside the intended commit; no user changes were modified.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRSeparation.vo`.

### Positive finite-observation certificates, following 8b49750

DirectRPositive now derives finite positive argument telescopes, their
introduction/application and rank bounds, and positive finite membership
formation/introduction/elimination. Context-extension transport is proved
from original PTS weakening; no semantic validity assumption is introduced.
DirectRFiniteObservations instantiates exactly
`delta q u = Pi Q:(Fq -> U3). Q e0 -> ... -> Q e(q-1) -> Q u`.
Checked: rank-4 formation for q>0, every point certificate, arbitrary rank-3
predicate elimination, and capped-successor preservation. In particular:
`delta_step_realized : forall q, 0 < q -> Realizes
 (Pi u:Fq. delta q u -> delta q (capped_successor q u))`.
This is an actual existential original-PTS term, not a host arithmetic fact.
No assertion that arbitrary raw selectors are canonical is used.

Incremental builds: `_build/local-ci-logs/positive-arrows-build-2.log`
and `positive-arrows-build-4.log`, `positive-arrows-build-5.log`,
`finite-observations-build-1.log`, `finite-observations-build-2.log`,
`finite-observations-build-5.log`, `finite-observations-build-6.log` exited 0.
Failed attempts remain in the same directory: folded Arrows rewrite mismatch,
in_map inference, and two missing scope annotations, all repaired. Final
incremental command was `opam exec --switch=pts-rk-ci -- dune build
 --display=short --no-buffer theories/DirectRUnaryAudit.vo`.
All nine added Print Assumptions queries report Closed under the global context.

Fresh isolated build exited 0, rebuilding original PTS dependencies, unary
audit, DirectR, countermodel, arithmetic and existing SetFunctions. Command:
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
 --build-dir /tmp/pts-rk-positive-check.7cdK7J --display=short --no-buffer
 theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo models/SetFunctions.vo`.
Exact transcript, types and assumption output are retained in
`verification/unary-positive-2026-10-13.log` (42 closed-context reports,
including the existing set-function queries).
Shell syntax, actionlint and git diff --check passed.
The subsequent full build, `opam exec --switch=pts-rk-ci -- timeout 120
 dune build --build-dir /tmp/pts-rk-positive-check.7cdK7J --display=short
 --no-buffer`, exited 124 while compiling unchanged DirectRTests. Transcript:
`verification/unary-positive-full-2026-10-13.log`. No full-build or remote
CI success is claimed, and no CI timeout or test was weakened.

At that checkpoint the next proof goal was: build Up(separating_test c) using delta elimination
at the rank-3 motive `Neg(P v) -> Neg(P(s v))`. Finite branches below the cap
use the inhabited Top; the capped branch is identity on Neg Bottom.
Then prove unary numeral evaluation in this observation, specialize O at
these data, and obtain uniform no_back. Remaining Theorem-4 obligations
include unary R1/R2, R3/R4, ground refutations and independent deduction
preservation. Theorem 4 remains incomplete.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRUnaryAudit.vo`.

### Comparability and finite-table milestone, following 7c10cc1

- DirectRUnaryAxioms now proves the complete relational comparability scheme
  R5_realized for every external cutoff and arbitrary Good object. It is
  restated as unary_comparability against the original Typing.typ in the audit.
  Both finite and large branches use the checked Case_n theorem; no separation
  premise or native expression-tree induction is assumed.
- DirectRFiniteTables constructs all-arity scoped projection terms and unary
  selector tables. table_typed and table_action prove typing and beta action
  uniformly. The capped table has the exact action i |-> min(i+1,q-1), with
  a checked bound on output indices when q>0.
- The separating test is typed and beta-evaluates to Top below the cap and
  Bottom at the cap. iterate_computation proves every external iteration
  beta-equal to the selector at min(k,c). These are PTS terms and beta proofs,
  not host-logic truth tables or an eta/annotation-erasing bridge.
- Valid selector indices are explicitly bounded in action theorems. No claim
  is made that every raw inhabitant of selector_type q is a selector. The
  required delta_q certificates are still missing, so no_back is NOT proved.

Successful incremental commands (OPAMROOT/PATH as below):
`opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer theories/DirectRUnaryAxioms.vo`
and the analogous targets DirectRFiniteTables.vo and DirectRUnaryAudit.vo.
Logs (under `_build/local-ci-logs`): `unary-r5-build-3.log`,
`finite-tables-build-3.log`, `finite-tables-action-build-5.log`,
`finite-separating-test-build-2.log`, `unary-comparison-audit.log`, all exit 0.
Earlier numbered logs retain actual failures involving binder/type inference,
list equality rewrites and an implicit nth_indep argument. No axiom/admission
was added. All 27 assumption queries in the expanded unary audit are closed.

Fresh isolated build (exit 0):
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
 --build-dir /tmp/pts-rk-comparison-check.fCSJuL --display=short --no-buffer
 theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo
 models/SetFunctions.vo`.
This rebuilt the shared original PTS dependencies and existing DirectR modules
alongside the new proofs. Full transcript, exact theorem types and assumptions:
`verification/unary-comparison-2026-10-13.log`; local copy:
`_build/local-ci-logs/unary-comparison-fresh.log`.
Workflow lint, shell syntax and git diff --check also passed.
The subsequent full build
`opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-comparison-check.fCSJuL --display=short --no-buffer`
returned 124 in the unchanged DirectRTests module. No full green CI claim is
made. Exact output is retained in `_build/local-ci-logs/unary-comparison-full.log`
and `verification/unary-comparison-full-2026-10-13.log`.

At that checkpoint the next goal was: construct delta_q(u) at rank four for q>=2, its point
certificates and closure under capped_successor q, then the Up certificate for
separating_test (q-1). Combine these with unary numeral evaluation to obtain
the uniform original-PTS no_back witness. The finite-table definitions are
intrinsically scoped alternatives to the old named table generator; no bridge
to that unused generator is required for this unary construction.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer theories/DirectRUnaryAudit.vo`.

### Previously checked bounded cases

Checked Theorem-4 bounded-case milestone (on top of cfb1dc2):
- Unary equality reflexivity/symmetry/transitivity and congruence for every
  raw endofunction; positive G closure and Good-to-G via exact rank lifting.
- Raw order transitivity, equality-to-order, G-guarded successor order,
  compatibility in both arguments, and equality/order double-negation stability.
- Uniform numeral typing/admission/observation and ground_order_realized for
  every external i <= j (not a finite test).
- Generic rank-ten invariant eliminator cases_from_closure_typed. Its rank-eight
  family, zero proof and G-guarded successor closure are explicit parameters.
  The actual Case_n family now satisfies all those premises uniformly.
- DirectRLogic: all-arity flat disjunction formation, injection and application;
  stability and elimination into stable targets; positive invariant formation
  and introduction. No Bottom elimination into arbitrary positive types.
- DirectRUnary: exact Case_n/Inv_n ranks, zero witnesses, all-cutoff successor
  closure in arbitrary contexts, and the UNCONDITIONAL bounded_case_realized.
  DirectRUnaryAudit restates this as unary_bounded_cases in original typ:

  `forall cutoff, exists p : Term nat 0, @typ nat RankSorts 0 ε p
   (Π Unary.Domain (Codes.Arrow (Unary.admitted Codes.V0)
      (Unary.Case cutoff Codes.V0)))`.

  This quantifies over arbitrary admitted raw objects, not native expression
  trees. It is Lemma `case` of the harmonized note, NOT all of Theorem 4.

Latest successful command (exit 0):
`opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer theories/DirectRUnary.vo`
with OPAMROOT/PATH as below. Logs: `_build/local-ci-logs/unary-basic-build.log`,
`unary-ground-build.log`, `unary-invariant-build.log`, `unary-case-build.log`,
`unary-case-zero-build.log`. The new generic logic layer first failed on a
nonexistent rename lemma, then on folded syntax, a list-length equation, and
a backwards shift rewrite. Exact failures are retained in
`negative-logic-build.log` and `negative-logic-build-{2,3,4}.log`; the repaired
build is `negative-logic-build-5.log` (exit 0). No failed proof was admitted.

Subsequent successful logs: `negative-stability-build-2.log`,
`negative-elimination-build.log`, `unary-context-build.log`,
`unary-case-step-build-6.log`, `unary-case-closure-build-3.log`,
`unary-bounded-build-2.log`, and `unary-audit-build.log`. Earlier numbered
attempts retain actual syntax/import/unification failures; none was bypassed.
All 15 unary/negative-logic Print Assumptions queries report
`Closed under the global context`, including unary_bounded_cases.

Fresh isolated build (exit 0, no pre-existing compiled objects):
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
 --build-dir /tmp/pts-rk-unary-check.C7rVtH --display=short --no-buffer
 theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo
 models/SetFunctions.vo`.
Full output is `_build/local-ci-logs/unary-fresh-build.log`.
The exact fresh-build transcript is also tracked as
`verification/unary-bounded-2026-10-13.log`.
The subsequent full-theory command
`opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-unary-check.C7rVtH --display=short --no-buffer`
returned 124 while compiling the unchanged DirectRTests module. Output is
`_build/local-ci-logs/unary-full-build.log` and the tracked
`verification/unary-full-build-2026-10-13.log`. Thus the fresh proof/module
build passed, but the full legacy example suite is still not verified.
`git diff --check`, actionlint on the existing workflow, and shell syntax
checking of the CI driver passed. Existing user logs/ and TeX were untouched.
The CI driver now explicitly builds negative logic and the unary assumption
audit, without removing any old stage or changing any timeout.

Next proof goal: finite unary selector observation realization and uniform
`no_back_n : O(numeral (S n), numeral n) -> Bottom`. The all-arity selector
API in DirectRStructural is available, but capped-successor tables and delta
closure must still be constructed and typed. Also pending: unary arithmetic
beta equations and relational R1/R2, all-index R3/R4 packaging, ground
refutations, independent source deductions and their preservation. The
functional R1_realized/R2_realized below do not prove unary relational R1/R2.

Next exact baseline command:
`opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer theories/DirectRUnaryAudit.vo`.

- Original pristine upstream, evaluator and checker soundness.
- DirectRStructural: structural substitution identities; generic dependent
  telescope formation/abstraction/projection; all-arity selector formation,
  typing, typed table application and beta-computation. Bridges connect to
  Codes.selector/Codes.selector_type and the named carrier nSelectorType.
  The named nSelector/operation-table/delta implementations still need bridges.
- DirectRFoundations: all fixed certificates; observed/admitted numerals;
  direct application lemmas for constructor closure, equality/congruence,
  arithmetic equations and order; functional admitted order reflexivity.
- DirectRProofs: uniform ground addition, multiplication and order,
  R1_realized and R2_realized. No legacy certify call remains in this module.
- DirectRGenerated, DirectRFirstOrder, DirectRObligations, DirectR facade,
  and the separate native-Prop arithmetic module. Compiling the definitions
  of generator contracts does NOT prove those contracts.
- DirectRUnary: the revised unary carrier and Church operations, Good,
  negative-test equality, unary-observation G and order, their exact ranks,
  constructor certificates, raw and admitted order reflexivity.
- DirectRCountermodel: the source structure N plus omega satisfies all
  relational and functional arithmetic axiom schemes, but not universal
  order reflexivity. This is NOT a PTS set model. Source non-derivability
  still needs a defined deduction system and its semantic soundness.

Assumption queries for R1_realized, R2_realized and ground_order_typed returned
`Closed under the global context`. The same holds for the checked structural
results and unary rank/closure/reflexivity certificates. No new axiom or
admission was introduced.

## Commands and evidence

Run from repository root:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer \
  theories/DirectR.vo theories/DirectRUnary.vo \
  theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo
```

Latest module-build transcript: `_build/local-ci-logs/harmonized-modules.log`.
Other exact transcripts: `ground-families-build.log`, `ground-assumptions.log`,
`structural-assumptions.log`, `unary-assumptions.log` in that directory.

`DIRECT_R_STAGE_SECONDS=120 bash tools/check-local-ci.sh` passed stages
01 through 12, including the new dependencies, then found an uninferred scope
in DirectRTests' zero-budget example. Scope is now explicitly 0.
The subsequent command
`opam exec --switch=pts-rk-ci -- timeout 120 dune build --display=short
--no-buffer theories/DirectRTests.vo`
returned 124. Transcript: `_build/local-ci-logs/examples-build.log`.
No full green test/CI run is claimed; the ordinary CI stage limit remains 1200.
An attempted timing probe during dependency rebuilding failed to import the
temporarily absent Foundations object; this is not a new source proof error.
A subsequent probe after rebuilding reached and completed R3_1_0 (about
8 seconds for construction/checking, 2 seconds for Qed), then reached R4_0
without completing it within its 20-second diagnostic limit. The full
120-second examples timeout is still a failure to verify the whole suite.

Tracked build/type/assumption evidence is retained in
verification/harmonized-2026-10-13.log. All 22 final assumption queries there
returned Closed under the global context, with no import or query errors.

Workflow lint and shell syntax were checked. Whitespace checking of agent
changes passes; the supplied TeX's existing trailing space is unchanged.

## Exact remaining work and next commands

First rerun the changed modules using the command above, then inspect the slow
example with (from `_build/default`, after dependencies finish):

```sh
opam exec --switch=pts-rk-ci -- timeout 120 rocq compile -time \
  -R theories PTSrk theories/DirectRTests.v
```

Uniform mathematical goals:
1. Finite unary observations and no_back are now checked in DirectRSeparation,
   with Up and numeral evaluation in their own modules. The unused legacy
   named-generator bridge is not required for the unary interpretation.
2. Unary Theorem 4's uniform invariant and bounded-case proof are now checked.
   The separate functional Theorem 7's four-constructor invariant remains open.
3. All unary relational axiom schemes and ground atoms are checked and now
   connected to independent relational syntax via a structural translation.
4. Unary guarded equality replacement, formula stability, full deduction
   preservation and source non-derivability are now checked. Theorem4.theorem4
   assembles the complete unary statement. Do not redo these obligations.
5. Functional Theorem 7 and the PTS set model remain separate unfinished tasks;
   only advance them on an applicable user request. The legacy DirectRTests
   timeout is a separate full-suite verification issue, not an open Theorem 4
   proof obligation.

Earlier failed approaches: blanket cbv in the symbolic tactic unfolds symbolic
numerals and loses reusable typing evidence. Direct tApp/arrow applications
plus Structural.structural_substitution_in avoid that. Eauto with transitivity
as a global search rule became expensive for multiplication; the successful
proof supplies the two transitivity steps explicitly.

## Subsequent set-model foundations checkpoint

The requested ZFC dependency was inspected at
`ede7126560844c381c2b021003a8dbcb0668ecad`. Its full Makefile failed on the
removed elimtype tactic. A pinned, licensed subset (Sets/Axioms/Cartesian)
is now vendored; one tactic in Cartesian was translated without changing
its statement or assumptions. No gh or publish.sh was used.

`models/SetFunctions.v` constructs the ordinary dependent function set as a
subset of a powerset. Graph abstraction, beta computation, relational
application, uniqueness and empty-fiber emptiness compile, with all five
Print Assumptions reports closed under the global context.

Exact successful command:
`opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer models/SetFunctions.vo`.
Log: `_build/local-ci-logs/set-functions-build.log`; tracked report under
`verification/set-functions-2026-10-13.log`. CI has a separate model-foundations
dependency stage and still checks every original stage.

This is NOT yet the PTS model or its soundness theorem. Next mathematical
work is the actual countable cardinal/sort-code universes and extensional
decoding, followed by finite-aleph/GCH bounds, coherent coding bijections,
substitution/beta semantics and soundness of the original typing judgment.
See models/README.md. Do not replace those obligations by a record assuming
model laws, or infer Bottom nontriviality merely from the empty-fiber lemma.
