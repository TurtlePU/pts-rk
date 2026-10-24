# Decisions and proof-engineering history

## 2026-10-24 — second-paper scope; planning only

The user requests a plan, explicitly not further development. The six goals
are three principal binder-free Agda presentations (Church-encodable
natural-model QIIRT; normal-form-first (Q)IIRT with closed definitional beta
agreement; cumulative whole-rank/length-bounded models with Church application
and native extraction), Hilbert/MM0 correspondence, partial finite models and
internal bounded soundness toward the specified consistency target, and an
indexed self-interpreter with source folds and typed CPS.

Record them in the paper's introduction and SECOND-PAPER-PLAN.md. Do not
create three placeholder modules or begin proof work. First freeze contracts,
then natural/Hilbert adequacy, normal-first feasibility, bounded hierarchy,
Church/internal soundness, interpretation/CPS and finally uniform consistency.
Closed definitional agreement is stronger than a propositional normalization
law or equality of code projections. Church realization of quotient equations
and dependent elimination is not automatic. Whole-input rank/label/annotation
bounds and grade-raising application are explicit. Fixed-grade programs do
not constitute a uniform evaluator; TOWER hardness alone does not establish
its representation-independent impossibility. Source folds must retain
intensional codes or respect quotient equations. Preserve the exact internal
proof predicate/domain and audit uniformity/incompleteness obligations.

## 2026-10-24 — dependent normal algebra and original raw typing decision

Extend normal substitutions to typed-normal families over ORIGINAL contexts.
Keep normal syntax explicit and truncate only typing witnesses; use original
normalization uniqueness for actual substitution/coherence paths. A smart
cast transports typing evidence without changing the subject and is proved
equal to ordinary record transport. This avoids making Cubical proof transport
part of the normalizer's input. Pi/lambda are structural normal operations;
application normalizes both the dependent result type and its inhabitant.
Universe decoding is the identity on the appropriate normal family.

Prove comprehension, normalized lifting, beta and product/lambda/application
naturality before claiming a model of the QIIRT signature. Its Sub direction
is opposite to native SubNF. The analogous laws do not yet constitute an
eliminator respecting every path, S/K/P template and computed-type guard.
Context eta is structural, never function eta. Retain the existing QIIRT.

Separate three interfaces: typed normal fibres; normal subjects with mere
typability and a computed unique type; and structural raw inference/checking.
The last must accept/refute ORIGINAL Typ and recursively check annotations,
normalizing inferred types only after constructing original typing evidence.
Its raw-context entry decides well-formedness AND typing, not bare Typ in an
arbitrary malformed context. The original native rules are unchanged.

The normal-context experiment is genuine induction--recursion: Con extends
by a normal declaration over its recursively decoded native context. Derive
mere well-formedness internally and eliminate it via witness independence,
not choice. Explicit normalization source/type parameters prevent expensive
metavariable reconstruction; this repairs elaboration without changing the
mathematics. Dependent refl examples test actual computation, including type
changes under substitution and polymorphic identity application.

This is not a simultaneous IIRT of all dependent normal syntax and hereditary
evaluation. Existing native binders/metatheory still implement normalization.
IR context sethood/adequacy, literal QIIRT interpretation and dependent source
completeness remain open. Quotient elimination disappears from the normal
carriers; coherence remains as proved operation laws. Do not claim a smaller
full presentation by comparing this implementation with a bare signature.

## 2026-10-24 — normal-first operations without assumed coherence

Integrate a syntax-only sufficient redex budget into the existing source
normalizer instead of maintaining parallel fast/canonical adapters. Prove
agreement with independently sufficient native budgets. Computation should
not inspect normalization typing witnesses; public refl regressions now test
the integrated canonicalizer. Compiler output size requires its own theorem:
count open variables as atoms, use the computed budget, and exclude indexed
payloads and working memory from the resulting atom-count bound.

Use direct weak SK evaluation as native-beta canonicalization only where
proved: ground output. A checked function-output counterexample shows the
chosen canonical compiler image is not closed under weak application, even
on canonical inputs. Seek an abstraction-sensitive closure/spine evaluator
for arbitrary output; do not add eta or declare weak conversion complete.

A normal-form-first presentation should make application/substitution smart
operations returning normal forms, not unrestricted normal constructors.
Use ordinary Sigma when simple types do not depend on terms. For original
dependent substitution, store normal images and truncate only typing proofs;
prove composition independent of those witnesses, then identity and
associativity as actual paths. A point-computing nested truncation recursor
avoids the library product-equivalence expansion's memory blow-up without
changing logical statements or assuming proof irrelevance of native Typ.

Mutual IIRT syntax and hereditary operations can eliminate conversion-quotient
path elimination and repeated guard handling, not the need for termination,
positivity, naturality or source adequacy. Normalized dependent type action,
comprehension and products remain unconstructed. The CPP QIIRT example's
substitution-calculus normalization and strictification of a given model
are not initial full-PTS normalization. Retain the original QIIRT as the
reference until the beta-only dependent equivalence is proved. No full-system
code saving or completed mutual IIRT is claimed at this checkpoint.

## 2026-10-24 — canonical SK image through intrinsic source provenance

Lift the native greedy passes to intrinsic simply typed lambda source and
prove exact erasure commutation. This preserves compiler-domain membership
constructively; do not parse arbitrary native normal forms or assume that
normalization preserves the surface fragment. Prove source erasure
injective, recovering hidden application domains from annotations and
typing, before invoking native normal-form uniqueness.

Use deterministic beta-only bracket compilation. Its output on closed
native-normal sources is an actual weak SK normal form, but the canonical
image is stricter than the full weak-normal family. Define Canonical A as
the fixed points of compile-after-source-normalization. The native-beta
set quotient is isomorphic to this family, and canonical application agrees
with quotient application. Independent bidirectional checking may return
these outputs; it does not establish full original PTS completeness.

Retain the distinction between binder-free OUTPUTS and a binder-free
ALGORITHM. This reference still uses lambda source and native-derived
rank computation. Optional large definitional evaluation tests consumed
excessive memory and were stopped; this is not an efficient runtime claim.
Keep general proofs and small regressions, with failed checks preserved.
Do not transfer native size bounds through bracket compilation without a
new output-size theorem. Direct canonical evaluation and dependent QIIRT
compatibility remain substantive proof obligations, not consequences of
switching bases or strengthening the normal-form definition alone.

## 2026-10-24 — SK surface with two explicitly different equalities

Use S/K only for the surface; identity is the deterministic derived SKK.
Remove redundant basis-specific implementations rather than retaining
parallel active calculi. Preserve historical evidence and the independently
complete native Hilbert catalogue: its identity-shaped logical axiom is
not a primitive of the SK surface, and eliminating all such catalogue
leaves requires a separately proved dependent compiler.

Keep weak SK conversion distinct from original beta of annotated expansions.
The direct weak normalizer/quotient shares its computation with independent
bidirectional checking. A second, beta-faithful reference uses the proved
native expansion typing bridge and existing rank-computing native normalizer.
Its actual quotient embeds injectively into native normal syntax, with
decidable equality and application, but has no claimed SK reification.

Bracket abstraction uses no eta optimization; compiled expansions reduce
forward to the literal annotated simply typed source. On normal source
expansions, native beta equality is literal equality. This does not prove
equality of arbitrarily chosen hidden-indexed SK trees. Canonical code
construction still needs domain-preserving reification and deterministic
hidden indices. C(NF(E(c))) is a reference specification until that bridge
is constructed; direct canonical application and full dependent adequacy
must be proved afterward, not assumed in a new checker relation.

## 2026-10-24 — binder-free normalization without changing native conversion

Separate an independent simply typed BCKWI experiment from original PTS-rk.
Unsaturated combinator spines form ordinary indexed inductive normal syntax;
type-recursive computability supplies total normalizing application and
structural induction supplies the computability of every normal form.
Do not call an input reducibility hypothesis a termination proof: here the
hypothesis is actually constructed. The algorithm never expands to lambdas.
Intrinsic indices preserve types along the literal combinator trace.

Bidirectional checking decides a separately declared raw typing judgment.
Use inductive identity witnesses for positive computational casts; Cubical
path transport on indexed derivations can block concrete evaluation.
Generic source-recursive inversion families remove UnsupportedIndexedMatch
warnings without suppressing them or disabling checks. Typing proof
irrelevance and annotated-code retractions give discrete normal forms.
Proved rule/context coherence then gives the actual weak-conversion quotient
isomorphism; its operation shares the same normalizing application.

Weak normal forms are not canonical for original annotated beta conversion:
BII and I are a checked counterexample. An extensional completion is not an
acceptable shortcut either: BI and I at arrow type are beta-distinct.
The extensional simply typed/untyped algebraic-equivalence literature does
not supply the missing dependent beta-only theorem. Preserve original
QIIRT/native IIR and normalization until native adequacy, dependent coverage
and path compatibility are proved. No inference to PTS Void canonicity,
fixed-rank/length finiteness, quantitative bounds or strong normalization of
all strategies. The prototype's arbitrary natural labels already defeat
fixed-length finiteness. Compare code size only after matching theorem scope.

## 2026-10-24 — uniform clause algebras and raw-table re-abstraction

Separate an internally parameterized generic proof algebra from its concrete
source/model instance. UniformHorn binds fragment/clause/position carriers
and projections in original PTS. Its positive proof family contains no model
or native typing premise. The consumer receives its interpretation handler
explicitly; constructing that handler is a remaining theorem, not admission.
Clause restriction pulls back positions and endpoints literally; proof
transport and composition then use beta only, without selector bijectivity
or an equality assumption. Exact atom ranks1/2 are certified separately.

A rank-one selector cannot directly take the rank-two raw carrier as its
rank-zero answer argument. This does NOT rule out a bare raw-field table:
re-abstract the raw carrier's algebra, dispatch at its final X:U0, and recover
an actual table of full-type rank2. Canonical forward output is the explicit
algebra-expanded quotation. Its identification with constructor quotations
is proved by beta, never eta for arbitrary raw inhabitants. Preserve syntax
injection independently of arbitrary-input semantic coherence. The Enum_2
decoder remains useful for dependent elimination and literal forward output;
it is not necessary merely to type this nondependent table.

Dependent clause soundness remains separate: Prem_V(c)->V(head(c)) has rank3.
Finite elimination at that motive can use independent Enum_3(c), whose exact
rank is4 for nonempty supports and3 for empty supports. UniformGuardedHorn
therefore checks guard ranks3/4 separately; proof fibers have rank g+2 and
node/consumer types g+3. Do not pad the empty case by cumulativity or silently
pack a high-rank guard into a rank-one clause carrier. Concrete guard families,
dependent premise projections, source coverage and model handlers remain open.

## 2026-10-24 — proof-preserving decoding and explicit finite generation

Translate independent indexed Horn PROOFS across literal finite atom maps,
not just into a truth family. Pull back the target rank-one predicate along
the actual Church map and select mapped clause handlers. This keeps the
translator type at rank4 and accepts arbitrary open queries/proofs, without
canonicity or a source-generation premise. Semantic/raw supports must both
be fixed before the query. Reserve lists enlarge indexing only; they are
neither denial constraints nor extra inference constructors.

Separate bare finite Church codes from independent generation evidence.
Enum_r(q) quantifies P:Code->U_r and has only the canonical selector cases;
it contains no target guard property or model. Its rank is at most max(3,r+1),
with dependent-consumer type rank at most max(4,r+2). Empty alphabets keep
their exact ranks: no cumulativity may pad them. Enum_1 and Enum_3 are
different required evidence types; neither is inferred from the other or
from arbitrary bare codes. Every canonical selector has constructors at
every motive rank, using the original annotated lambda syntax.

Ordinary rank-one Leibniz equality over codes has rank3. Finite composition,
identity and retraction admit INTERNAL equality consumers at type rank<=5,
using Enum_3 and canonical beta/reflexivity branches. Do not infer native
conversion or unrestricted universe-polymorphic equality from these terms.

The raw guard graph is independently specified by facts (i,raw_guard(entry_i)),
with a rejected sentinel and both Boolean alternatives retained in support.
Its compiler consumes Enum_1 to produce an independent graph proof. Separate
Enum_3 inputs prove both input-projection identity and Boolean-projection
agreement with the direct guard table. A graph proof alone would not prove
these arbitrary-input coherence properties; keep the equality terms explicit.
Canonical accepted-source reconstruction and wrong-answer exclusion remain
external closed-inhabitant theorems using prior canonicity. Fixed table
realization does not yet internally return raw Expr/substitution records or
uniformly interpret fragment budgets. No new independent consistency or
generated-size/runtime claim follows from the constant type ranks.

## 2026-10-23 — internally quantified finite queries and raw provenance

Index independent proofs by an arbitrary ORIGINAL PTS Church atom code q.
Quantify one predicate P:Code->U1, then all actual positive clause handlers,
returning P q. Code has rank1, the predicate type rank2, and Proof(q) rank3.
Finite type dispatch uses answer rank zero: U1:U0 permits q U1 T0 ... Tm.
No dependent selector eliminator, cumulativity or parametricity is assumed.
The actual uniform consumer has TYPE rank4 and accepts arbitrary open typed
queries and proofs. Its result is the syntactic family T(q); reduction to a
specific truth proposition is asserted at canonical selectors only.

Keep a fixed anchor when generating support, so varying the internal query
does not regenerate the domain, clauses or truth table. Duplicate positions
need not receive proofs of all aliases: exact source correspondence uses
the canonical index of a supported atom. Reified semantic truth is not the
least indexed closure at every alias. Typed bridges between encodings at
canonical queries are not claimed to be mutually inverse proof bijections.

Raw observations distinguish None overflow from Some EZ and every other
closed constructor tree. Independently compute structural guard acceptance;
no native typing, source derivation, model or agreement is an admission test.
Active entries reconstruct the selected literal rule, sorted substitution
and exact argument observations. Inactive entries are tautologies. Prove
source reflection by induction on arbitrary raw derivations, rather than
inferring it from surjective clause images (which could merge proof aliases).
Retain executable semantic-to-raw proof translation and exact finite-union
source coverage. Do not claim fixed-budget raw/semantic derivability iff.

Raw provenance remains an external verified computation; compiling its
invariants and the fragment/budget parameters into one internal PTS program
is still open. Generic consumer typing is canonicity-free. The source/closed
inhabitation converse and Void specialization retain external canonicity;
they are not an independent consistency proof or a normalization-cost bound.

## 2026-10-23 — arbitrary represented proofs of a fixed finite fragment

Use a model-independent Church encoding of finite positive Horn deduction:
quantify a rank-one proposition for each finite atom, then all actual selected
clause handlers, then return the query proposition. Do not specialize its
domain to a truth table, assume a desired soundness predicate, or restrict
the input to externally generated proof codes. Original product ranks give
proof-type rank <=3 and soundness-function type rank <=4 without cumulativity.

Finite positional support contains the query, all positive clause atoms and
all denial atoms. Duplicated positions are harmless aliases; supported atoms
have exact encoding/decoding and injective encoding. Derivability and Boolean
checks are preserved exactly, with all guarded valuation instances included.
The Church type contains only positive inference constructors. Model denials
are enforced by separately typed internal refuters, not used as source rules.

The soundness term instantiates arbitrary encoded proofs at the independent
rank-one truth propositions and supplies valid clause witnesses. Its typing
does not use canonicity. Source compilation and introduction from arbitrary
encoded premises validate the intended proof reading. External exactness and
the guarded-MM0 Void specialization explicitly retain native canonicity.
Fragment/query/budget/model remain metalevel parameters of the generator;
uniform internal raw-source decoder/guard provenance is not claimed.
Do not confuse these type ranks with global normalization redex-rank bounds
or bounds on generated syntax/runtime allocations. Freeze all five sources
before a fresh 63-module build and complete recursive inventory comparison.

## 2026-10-23 — literal MM0 adequacy and consistent guarded models

Interpret the existing sorted, independent MM0 source derivation datatype;
do not replace it with a bespoke native calculus. Injective quotation and an
exact scoped decoder connect raw constructor trees to original annotated
terms. Prove all nine computational graphs in both directions, reconstruct
native reduction endpoints from native starts, and identify all17 numerical
axiom-row families with the65 catalogue schemes in both source directions.
Literal PH derivability then equals independent catalogue derivability.
This does not prove original-PTS-to-catalogue completeness or verify a parser
for external MM0 text; the unchanged transcription is separately crosschecked.

Use a concrete finite overflow algebra of closed first-order-sorted Expr
trees. All nine constructors are total on three copies of the fixed carrier.
Guards check declared variable sorts, size/depth of every value and every
premise/head argument, never typing, consistency or desired agreement.
Inactive positive instances are tautologies; universal Void denial is never
guarded away. At N>=5,D>=3 Void is genuinely represented. Every accepted
query reflects to an independent source derivation; actual source derivations
compute sufficient guards and exact decoding. Raising bounds to the Void
threshold yields exact coverage by accepted consistent finite models.

Full55 GUARDED model existence is now unconditional apart from these numeric
bounds. Nonempty universe typing is proved separately. Source Void exclusion
is derived through native catalogue typing and external canonicity; this is
not a new internal or independent consistency proof. Generated satisfaction
certificate TYPES have rank<=4. Do not confuse expression depth D, certificate
type rank, and the normalization development's global redex-rank bounds.
Uniform internal source/reflection invariants remain open.

Freeze final proof sources before fresh verification. A late21st Hilbert
endpoint raced the first audit snapshot; preserve its failed source-stability
gate and rerun from a fresh absolute build. The first wrapper also let bare
assertions fall through inside set+e. Explicit failure propagation and
negative count/whitespace regression tests repair that audit mechanism;
the first count-stage0 is not valid final-count evidence. No proof-hash change
may be normalized away. Raw failed outputs and script snapshots are retained.
The second audit's fresh compilation/kernel/inventory/source checks pass,
then its textual safety scan flags a pure structural predicate named Admitted.
Rename that predicate FitsSyntax, preserving every statement/proof otherwise,
and run a third fresh audit. Keep the simple safety scan unchanged; this was
an identifier collision, not a proof admitted to the kernel.

## 2026-10-23 — local operation provenance and its exact boundary

Keep literal original contexts distinct from certificate-context serialization.
The former stores each declaration term; the latter stores a declaration
certificate and rank. Native erasure is not an internal extraction theorem.
Original Context.index weakens the selected declaration at zero and once for
each further crossed extension. Its local zero graph need not inspect the
prefix; a separate ContextGuard certifies whole-context scoping, not typing.
An arbitrary-output scope fold is weaker than endpoint coherence and must
not be described as internal lookup functionality.

Index a comparison Trace by the actual Zip witness executed by the comparator,
as well as both endpoints and the symbolic Boolean output. Local clauses
record constructor operations, not an evaluator equation or desired answer.
Keep atom tests and conjunctions symbolic when constructing standard traces;
external canonical computation is a subsequent bridge. The intended agreement
consumer uses the already defined Same at exact predicate rank one. Such
transport can support Holds and conditional rejection, but is neither beta
equality nor arbitrary endpoint coherence; an atom-left clause on arbitrary
right input does not provide root-generation or inversion evidence.

NamedBeta factors structural beta and dependent application-spine lemmas over
the ORIGINAL annotated Syntax/Typing/DefEq judgments. Named environments are
native assembler data; they add no object-language primitives or axioms.
Avoid expanding closed payload annotations merely to prove fixed head steps.
The complete context constructors, arbitrary-output scope consumer and
executable standard realization compile. BooleanAgreement supplies reusable
scoped uses of existing Same/refl/congruence, not a new equality principle.
Comparison formation and all three arbitrary-open-input local agreement
cases compile; full Trace constructors and the arbitrary-Trace fold do not.
Preserve failed large-annotation attempts as evidence, never as library proofs.
A symbolic named-context lookup lemma can improve the current constructor
implementation. The agreement fold can independently abstract the checked
local cases and assemble them with NamedSpine; do not elevate constructor
lookup into a mathematically necessary soundness premise. Internal
finite-fragment soundness remains open; live verification status belongs in
STATE.md and BUILD.md.

The concurrent Horn development changes the preferred soundness backend:
its actual original-PTS consumer handles arbitrary inhabitants of an
independent finite Horn proof type, not only externally quoted proofs.
Reuse that consumer instead of rebuilding dependent preservation when an
internal source-to-Horn bridge suffices. The present comparison/lookup route
is one way to supply provenance, not an unconditional prerequisite. Fixed
proof/consumer rank bounds (3/4) do not internalize fragment parameters;
original-PTS catalogue coverage and the raw-source bridge remain obligations.
The Void specialization's native-canonicity dependency remains explicit.

## 2026-10-23 — explicit guarded quantified Hilbert fragments

Use original annotated syntax on finite positional carriers with one overflow
value. Admission bounds node count, tree depth and universe labels, including
constructor/substitution outputs. Never use Typ, desired semantic agreement,
normalization or consistency as an admission test. Scope-changing binder
operations are total between the appropriate fixed finite carriers.

Separate two constructions. The qualitative model has predicates P_0..P_H
and increments proof height on each rule; original beta/conversion side
conditions retain their native meaning. Its displayed-judgment bounds do not
bound those witnesses. Same-height closure is explicitly refuted. The
executable model instead bounds every beta-path state and path length, selects
finitely many numerical catalogue labels, and enumerates every bounded
parameter tuple of ALL six rules. Finite Horn saturation has no proof-height
cutoff. Its rule graph is Boolean, all semantic valuations are covered, and
Void is represented nontrivially for node bound>=3 and depth bound>=2.

Increasing syntax/path bounds and catalogue lists preserves the executable
model's positive queries. Every finite native catalogue-rule support fits
one budget, including intermediate reduction witnesses; union coverage is
exact for independent catalogue derivability and true finite-carrier queries.
This is not the still-open original-PTS-to-catalogue completeness theorem.

Finite satisfaction certificates and recursive deduction translations are
actual original PTS terms; certificate rank is at most four. Their native
Void exclusion uses external canonicity. Do not describe this externally
indexed family as a uniform internal reflection/consistency proof. The
separate literal-MM0 guarded compiler proves conditional schema/grounding
and certificate correspondence; it does not silently identify its full55
graph theory with the native six-rule fragment or assume the adequacy bridge.
Path/state bounds do not bound all host allocations or generated program size.

## 2026-10-23 — independent source graphs and internal residual agreement

Repair the resource-only contract with independent source-to-operation
clauses, never an assumed checker/evaluator equation. CheckerSourceGraph
covers all six rules, step/equality endpoints, original context lookup,
context checks and raw decoding failures. Native induction derives compiler
agreement, uniqueness, complete raw coverage and both outputs. Lookup,
substitution, encoding and decoding remain native here; do not call this an
internal raw-source relation.

Separate that native boundary from internal execution. InternalExecutionGraph
represents Run by leaf and conjunction clauses, with no evaluator equation
in its constructors. One original-PTS term of full-type rank six transports
rank-one Boolean predicates from evaluation to the reported output for
arbitrary represented Run witnesses. Same is exact-rank predicate transport,
not beta equality, symmetry or unrestricted Church parametricity. Conditional
rejection consumes a false Run proof; such a proof is never a resource field.

Generate standard execution witnesses with symbolic comparator applications
and conjunctions. CheckerGraphRealization converts them to canonical answers
only by proved computation. It realizes ordinary acceptance, including an
accepted sort example, without external Bottom emptiness. SourcedResources
combines old independent storage witnesses with the native source graph and
excludes the prior counterexample; this repair is native, not the final
internal consistency contract. No source injectivity is claimed for residual
programs or execution witnesses.

Next represent context/certificate/subject/type/expression provenance and
share chosen endpoints across consumers. Original context lookup needs all
enclosing shifts, not just substitution-environment lookup. Existing generic
replacement environments can be multivalued: prove the coherence needed by
the actual single-substitution consumer, not unconditional functionality.
Product-rank maximum and complete certificate/context parser traces also
remain to represent. A total compiler and the proposed joint Zip builder
are optional routes; internal local agreement and standard coverage are not.
Milestone 4 remains open after this continuation.

Fresh verification pins all 506 prior source paths plus the four new proof
files. Preserve 503 old bodies byte-for-byte and normalize only the three
additive registration files to their prior hashes. The third is a concurrent
combinatory Dune edit registering exactly seven new guarded-model modules;
those new independent files are outside this continuation's closure. Archive
full-tree snapshots informationally, but compare the scoped 510 hashes exactly.
Do not skip any actual kernel dependency. The first strict-gate failure is
retained; this scope adjustment does not exempt any prior proof body. Four
registrations were present before the fresh build; two more appeared during
the successful kernel check. Preserve the resulting raw post-gate failure,
verify all other 509 hashes exactly and the additive normalization separately.
A seventh entry appeared during archival; review and normalize it exactly too.
Do not call that driver run all-pass or claim to audit the concurrent modules.

Keep the roadmap concise and number the README's six remaining gates
identically. Historical finite-schema completion must not be confused with
the still-open internal finite-fragment soundness milestone.

## 2026-10-23 — separate storage, source provenance and internal soundness

Keep the complete operands and recursive payloads in residual resource data.
CheckerResourceBounds proves injectivity, size accounting and actual original
capacity witnesses for every raw source in a size-bounded fragment. These
are storage theorems only: do not infer compiler/runtime bounds or internal
agreement between an arbitrary source and a stored program.

ComputationBoundary refutes exactly that inference. A fully decoded scoped
bad_application source is rejected, while Compare(q,q) returns true with
actual generation, capacity and correct traversal evidence. The native Rocq
counterexample concerns a contract collecting actual PTS witnesses; it is
not an internal PTS negation or an impossibility theorem for the programme.
Require independent local source-indexed compilation/checking clauses and
internal correctness for both outputs, then prove standard coverage. An
admission field asserting evaluator/native-checker agreement is not a repair.

Retain the checked joint carrier J:U4, its constructors/projections and the
independent GoodJ: J->U6 interface. The proposed generation constructors,
buildZip fold and standard realization are unverified; archive their drafts
outside theories. Large repeated conversion expansion was interrupted or
killed (one probe reached about31.6GB RSS); this is an engineering limitation,
not a rank contradiction. Reuse the checked telescope abstraction/head-step
lemmas for structural conversion proofs, not further whole-term expansion.

Stop the current continuation at the proved resource-only contract failure,
before milestone4. The further soundness obligation remains independent:
derive a sufficient dependent invariant, bounded normalization/negative
continuation and terminal exclusion INSIDE PTS. Native scope/substitution
agreement and external canonicity do not supply these laws. A source-indexed
relational trace is still a viable alternative to a total internal compiler.

Streamline DIRECT_ROADMAP around target, completed foundations, this precise
boundary and six acceptance gates; keep experimental history in handoff and
verification records. Preserve the Pakhomov/Willard logical-scope audit and
the distinction between the finite internal schema and all-budget soundness.

## 2026-10-23 — execute residual comparisons before proving rejection

Keep computation correctness independent of consistency. Compile the literal
unchanged checker to Truth/Compare/Both expressions, retaining complete raw
operands in Compare. Cover all six rules, equality/context certificates,
malformed inputs and BOTH Boolean outcomes. Parsing, context lookup and
endpoint computation (including original substitution) remain external.
Do not describe that compiler as an internal raw-code checker.

Use independent synchronized traversal Zip(x,y), not a field giving equality
or its Boolean result. Its constructor cases are atom/arbitrary, pair/atom
and pair/pair with corresponding child witnesses. One fixed original-PTS
comparator consumes it and computes actual tag tests/conjunction. C:U2,
Zip(x,y):U4, full comparator type:U5. A root test opens the Boolean's X:U0
before folding raw C; Bool:U1 cannot simply be used as its U0 fold argument.
The generated traversal covers all raw pairs, regardless of parsing/checking.
Correctness is proved for canonical quotations plus these generated witnesses,
not arbitrary inhabitants of Zip. Prove any stronger admission contract
separately; do not invoke unproved Church parametricity.

Use one rank3 Church conjunction-expression carrier and one evaluator whose
type has rank4. Leaves retain actual comparator applications. Their exact
native output correspondence strengthens to forward beta reduction using
common reducts and normal, distinct Boolean points, not global normalization
or Bottom emptiness. Raw source serialization/quotation remains injective.
Residual checking programs deliberately need not be: distinct sort certificates
give the same program (checked counterexample). Never transfer source
faithfulness to this lossy residual program.

Next internalize independently certified compilation/traversal evidence and
prove resource sufficiency for the actual operations. A total internal compiler
is optional for a relational formulation: independently defined resource
witnesses could replace it, provided standard coverage and internal checker
agreement are proved, not assumed as admission fields. Rejecting all Bottom
inputs still requires internal terminal separation/preservation or another
independent soundness argument; output correctness alone cannot manufacture
All branch evidence. Traversal node count is not emitted syntax or runtime.
Freeze all earlier proof sources except additive audit/module registration;
fresh-audit every new public Lemma/Theorem/Example (92) and the full dependency
closure against fresh pristine. Preserve setup/proof failures and do not
rerun the unrelated complete older audit merely to check this extension.

Design follow-up, not formalized: do not implement a naive double fold over
Good_r and silently assume its child guards. Good_r has calculated rank
max(4,r+2); forall y:C, Good_r y -> Zip x y has rank max(5,r+3), above r.
An asymmetric higher outer guard fixes only this first mismatch; the inner
fold still supplies Zip conclusions instead of the Good_r child witnesses
required by the outer induction hypothesis. Retaining that same guard inside
the inner motive repeats the rank mismatch. This does not rule out other
representations or resource-relative constructions.

A narrow candidate is a Church joint-traversal carrier J, folding at X:U2,
with 29 C->X cases, 29 C->C->X cases and one X->X->X case. Calculated J:U4.
Project L,R:J->C by folding at C; define independent generation GoodJ_4:J->U6.
One fold at motive j -> Zip(Lj)(Rj):U4 should produce a rank7-type buildZip
term from GoodJ_4. Existing Zip constructors match its recursive evidence.
These are unverified design calculations: next construct the literal terms
and original typing derivations, then exact standard coverage. They replace
external generation from a represented joint resource, not the alignment
of two independent arbitrary C inhabitants or internal checker soundness.

## 2026-10-23 — represented dictionaries separate elimination from generation

Use a Church list of E:U1 elements, with X:U0 iteration. Because U3:U0,
it can fold into a homogeneous rank3 type telescope P(e1)->...->P(ek)->R
for P:E->U2 and R:U3. Pad ONLY the final result with an inhabited D:U2
when selecting a member. Padding the telescope accumulator differently or
silently lifting exact ranks breaks this construction; no cumulativity is used.
All is the separate branch-proof package; Fill ignores branch arguments;
Guard quantifies over arbitrary motives and is independent of checking.
Standard admission uses list membership plus Fill, never All or rejection.
Nil/cons/append operate internally, and one rank5 eliminator handles arbitrary
represented lists and guards. Reordering its arguments supplies a fixed
consumer whose dictionary and branch package are ordinary arguments.

Retain the exact original checker tables and all malformed/rejected raw-code
coverage when connecting existing finite fragments. This removes the varying
case telescope from the interface, not the remaining internal generator.
The external native-normalization proof still certifies each branch identity;
no conversion law exists for a symbolic arbitrary checker application.
An internal branch generator must consume independently justified computation/
normalization evidence and derive All, not require All as resource admission.
Independent budget/dictionary generation, faithful checker correspondence
and sufficient resources/costs remain explicit tasks. The implemented E:U1
specialization does not instantiate the existing C:U2 raw-code carrier; a
separate rank adaptation is possible work, not an established obstruction.
Output-neutral checker-trace reflection is a suitable next subgoal: retain
arbitrary Boolean outputs and certify actual local transitions. It establishes
computation correctness, not absence of accepting runs. Derive the latter
from independent finite local preservation/terminal exclusion, rather than
assuming every trace returns false. A genuinely fragment-relative finite
model or normalization history may avoid full dependent reconstruction.

Fresh audit the 56 new endpoints and their complete dependency closure; freeze
every previous proof source except additive Dune/Audit registration. Do not
repeat the expensive unrelated old audit or change it to make this target green.
Preserve failed incremental attempts and compare the complete kernel inventory
against a fresh pristine build. No Git index change is authorized this turn.

## 2026-10-23 — finite-fragment normalization bypasses dependent reconstruction

Follow the user's selected finite-fragment route and the improved combinatory
interfaces. Bound COMPLETE serialized raw certificates by tree size, including
binary labels, annotations and raw conversion instructions. Enumerate every
raw tree; do not filter admission by parsing, acceptance or rejection. The
common normalization envelope decodes scoped certificates but does not filter
by acceptance. It computes maximum conservative rank, maximum subject size
and concatenated label alphabet before checking; accepted subjects then
normalize in one finite carrier with exact original typing and every state
covered. Do not normalize arbitrary supplied conversion intermediates.

Compile the ACTUAL checker entries into finite Church tables. Generic table
correspondence and the general-judgment checker remain independent of Bottom
emptiness. Use normalization plus canonical-form exclusion externally to
certify the rejection branches. The internal proof is finite elimination
with an independent guard over ALL rank-two motives, not an assumed soundness
predicate: each branch is the literal identity on Bottom after conversion.
Every external bound gives an originally typed rank-four rejection term;
its arbitrary guarded inputs are not restricted to canonical quotations.
Source quotation remains beta-injective at each fixed bound.

This is a substantive bounded-consistency schema, but fixed rank does not
mean fixed type: arity, carrier, case telescope, table and proof vary externally.
No single represented-budget theorem or enumeration/generator cost bound is
claimed. Next internalize finite dictionaries and case evidence at one fixed
resource-relative interface. Do not assume full dependent typing reconstruction
is necessary, nor insert rejection/model validity into resource admission.
The full-ungraded native finite-model target is already refuted by the new
combinatory boundary theorem; it is not this guarded/growing fragment route.

Keep all prior proof sources unchanged. The focused audit checks every new
endpoint and its complete transitive closure; older unrelated branches retain
their prior full audits. The first integrated run's broad whitespace check
reported a pre-existing NamedTemplates EOF blank line; preserve that file and
record the failure. The final audit scopes whitespace to actual changed files,
while hash-checking all previous proofs unchanged. No existing CI stage changes.

## 2026-10-23 — quantified constructor search, internal proofs and native no-go

Replace the candidate-only interface by complete enumeration of every total
operation table at fixed finite cardinalities. Keys are operation symbols
paired with semantic argument vectors; completeness is pointwise, avoiding
functional extensionality. Every row is present, so total lookup never falls
back on an absent semantic tuple. Use separate copies of the same D for the
three MM0 sorts; do not silently claim completeness for unequal cardinalities.

Represent all nine constructors, eleven predicates and 55 literal universal
axioms as sorted expression trees. Selection retains entire named axioms.
Sorting is proved equivalent to an independent inductive judgment;
substitution preserves it and commutes with evaluation. Independent Type-valued
source proof trees compile to finite semantic Horn proofs, then original PTS
terms; no source tree contains a native typing or desired soundness premise.
Textually comparing both expanded source presentations is useful independent
test evidence, not a kernel-verified MM0 parser/native adequacy bridge.

The explicit projection model is intentionally a weaker test, not a nearly
complete PTS model. Removing sveq permits identity substitution; removing f0
permits empty form/ax, so every catalogue-introduction antecedent is false.
Both omitted axioms fail explicitly. Nonempty typing, enabled application and
universal Void exclusion are still real, all-valuations properties. Existence
implies successful two-element search analytically; do not execute or claim
execution of 2^28 constructor candidates. Full55 unit rejection is computed.

Internal semantic proof production uses independent Top/Void interpretations
of truth-table entries. Implication-chain proofs are composed structurally
with compiled subproofs. The finite universal-axiom package is the continuation
conjunction (C1 -> ... -> Cq -> Void) -> Void, with rank at most four. Its
inhabitability iff is externally exact; reverse exclusion explicitly uses
native canonicity. The forward proof generator does not. The actual projection
model discharges acceptance, yielding a closed native certificate. This is
not an unguarded Church-domain induction principle or one internal uniform
reflection theorem over represented fragments/proof codes.

Do not keep calling the full ungraded finite native-model interface open:
FiniteNativeModelBoundary disproves it, even for directed reduction. Apply
two collided Church selectors to a vector of same-sort U1 types containing
Void and inhabited E^0_1; conversion followed by type reduction sends an
inhabitant to Void. Therefore every Fin k selector family is injective.
The finite-test version needs only finitely many test facts and forces k
distinct values; it does not say each fixed guarded fragment is infinite.
Literal MM0 impossibility still needs a native/catalogue adequacy bridge.

A further constructive continuation must choose explicit size/proof-depth
guards or a graded interface and prove bounded original-source coverage.
Adding those guards changes universal axioms; neither that weakening nor the
two missing base axioms may be presented as unchanged full PTS-rk. No such
target switch was made in this checkpoint.

## 2026-10-23 — Void-denying Horn targets and exact finite candidate checking

Positive Horn satisfiability is insufficient: its all-true model populates
every alleged Void judgment. Retain GroundHorn as the positive kernel, but
use actual negative constraints (finite premises imply False) in the target.
Prove model existence iff no denied conjunction is derivable, least-model
reflection and constructive finite derivation support. Do not use an extra
positive 'false' atom, which arbitrary models could again declare true.

Discharge consistency for the explicit 65-shape Hilbert catalogue, rather
than taking it as an assumption. NativeCanonicity.v uses the ORIGINAL
normalizer and canonical-form inversion to exclude closed Void inhabitants;
HilbertGrounding independently reproduces the six rules and proves exact
grounding and soundness. Native substitution/conversion side conditions are
not the MM0 graph encoding, so MM0 adequacy and original-PTS-to-catalogue
completeness remain separate. No PTS typing rule or set-model premise changes.

FiniteHorn saturates a finite ground clause list in at most its clause count.
HilbertFiniteModels reuses shared DirectREval structural equality and proves
native typing and exclusion of ALL closed Void subjects, not merely selected
tests. The singleton first-order domain has distinct nullary predicates;
it is neither an all-true model nor a finite quotient of the syntax algebra.
Add a signed least-model diagram only for explicitly chosen observations.
This completion reflects every supported propositional formula but strengthens
the theory: its negative facts can disappear when more rules are admitted.
Do not treat nonderivability as negation in the uncompleted Horn theory.

FiniteHornChurch generates literal original-PTS truth-table terms, with exact
external true/false beta correspondence and nonempty-input map rank r+2.
Saturation and table generation occur externally. Canonical-query correctness
is not internal uniform reflection or a theorem about every Church inhabitant.

FiniteUniversalHorn enumerates all semantic vectors over a supplied complete
finite domain, including values not represented by chosen native terms.
Positive/negative schema satisfaction equals compiled-ground satisfaction;
the executable denial check decides whether predicate interpretations exist
for that candidate's already interpreted constructor functions. This is a
complete candidate-schema checker, not a proved MM0 compiler, constructor
algebra search completeness, or existence theorem for all PTS fragments.
If equality is encoded as a predicate, its actual finite diagram must be fixed.

FiniteModelBoundary proves the narrow obstruction: a finite total UNTYPED
applicative algebra satisfying (K x) y=x is singleton (K embeds the carrier
into itself; finite injectivity gives surjectivity and collapse). Thus such
equational models cannot also have a positive typing fact and empty Void.
Typed/rank-indexed, partial/guarded and directed-reduction semantics are NOT
covered by the hypothesis. Selinger's finite reduction models motivate a
remaining route, not an already proved PTS model. Next construct a successful
finite candidate for a precisely specified quantified typed/resource fragment,
prove template agreement and standard coverage, and then internalize soundness.

## 2026-10-23 — finite-fragment sufficiency versus uniform reflection

Analysis requested by the user; no target/checker switch or implementation
is authorized by this entry. The prior dependent-coherence gate was specific
to our selected direct invariant and must not be reported as a general
obstacle to bounded consistency.

Actual combinatory results: fixed_rank_peak_normalization retains original
typing and bounds every state; normalizer_in_finite_carrier supplies finite
coverage; ChurchFinite.map_typed/map_selector_beta and
repeat_map_typed/repeat_map_beta compile finite tables and iterations into
original PTS terms. FragmentModelSoundness.model-soundness is an external
Agda theorem on independently accepted complete contextual inputs. The note's
sec-internal-consistency explicitly distinguishes these from fixed finite
first-order models and internal reflection. A finite run envelope is not
closure under all operations/valuations: graded application enlarges the
carrier, and overflow fallbacks are justified only on bounded intended runs.

For each externally fixed finite domain of complete proof codes, finite
checker tabulation plus a genuinely independent finite-case guard provides
a different route: construct every rejection branch and combine them.
FiniteRejection.rejection_typed is an existing complete two-code pilot.
Its generalization would give an external family of internal proofs, not
one internal proof with a represented budget argument. General guards,
all-case rejection generation and exact acceptance correspondence remain
to be built. Bounding only the subject term does not bound its types,
conversion witnesses or proof tree. Neither a fixed rank for E_K/maps nor
canonical-input beta equations supply this uniform logical step; K, the
interface and emitted program size still depend on external budgets.

Re-read the original Downloads Zermelo revision, sec:internal-consistency
(lines 1068–2668), rather than assuming it merely asserts preservation.
Its relevant construction is genuinely weaker than full dependent semantic
preservation in original PTS:

- lem:ea-constant-separation transports non-idempotent resource typings along
  supplied untyped equations and separates inert constants, without normalizing
  arbitrary intermediates or constructing Church–Rosser joins.
- lem:tagged-projection uses auxiliary tagged Church tuples to recover product
  ranks and domain/codomain equations with polynomial overhead.
- sec:graded-calculus retains scope and declared grades, but not type-formation
  or context-validity proof requirements. Conversion has no target-formation
  premise. These are analysis rules, never changes to original PTS.
- lem:source-tag-coherence and lem:source-elaboration provide the one-way source
  lift via finite packets. Generated regularity witnesses are not recursively
  elaborated again. This is a substantial unformalized construction, not an
  evident assumption of the bounded-soundness conclusion.
- lem:aux-one-step preserves the weaker G certificate polynomially. Product
  projections supply the precise beta domain/codomain alignment that our
  current native-typing route still lacks. Active evaluation ignores annotation
  and product fields; substitution still updates/counts them.
- lem:aux-terminal only excludes a weak-head-normal grade-zero inhabitant of
  a fresh type. Full normal forms, canonical target certificates and a total
  internal normalizer are unnecessary.

For supplied tower B, thm:bs-proved uses K<=B and
s_(i+1)<=(s_i+B+2)^d to bound the whole proof history by a fixed elementary
function of B, then uses EA bounded induction. We found no concrete flaw in
the packet/transport construction in this review; this is not kernel or
independent peer verification of the paper. These lemmas remain proof tasks.

The final step is not computational representability: EA proves a uniformly
resource-relativized negative sentence; thm:conditional-self-consistency uses
Pakhomov Corollary 5.3 and J to obtain the specified translated PTS sentence.
The published Corollary was checked directly in arXiv:1907.00877v2, page22.
Histories may lie outside the interpreted cut; only source proof/checker
witnesses are relativized. Compiling a finite normalizer does not replace
that bounded-induction/transfer proof. An EA/H-free route still needs an
internal counterpart, but can use the weaker G invariant or proof-carrying
finite-table rejection instead of preserving full original derivations.

Also keep the predicates distinct: the draft fixes explicit typed-equality
T^e, whereas NativeProofCodes accepts raw conversion trees. The source lift
in the draft needs only T^e-to-analysis, not an internal converse. Our checked
non-normalizing conversion detour is not a T^e certificate. Retaining the
current exact consistency predicate adds a transfer/lift obligation; selecting
the draft's predicate is a different legitimate target only after that choice
is explicit. External equivalence of full PTS presentations does not identify
their internal arithmetic formulas. No switch was made in this analysis.

## 2026-10-23 — closed-template specialization without payload expansion

The new replacement graph and literal public constructor types stay unchanged.
Check binder/application templates with a PTS parameter for term_at, then
discharge it by original tApp and term_at_sorted. Public constructor TERMS
gain that outer application; no consumer inspects their old bodies. Native
NamedTemplates proves exact assembler/substitution and closed-fragment
congruence, so specialization has the literal original type without expanding
large closed payloads. Its native lemmas add no PTS primitive or typing rule.
All internal helper proofs remain checked; no target hypothesis survives.

This replaces an inlined check that timed out after2400s while checking
application. Its binder checking/Qed had already taken807/836s. Generic
binder/app checking takes about175/77s including Qed, with exact type
specialization under a second. Preserve the failed naive concrete-body
specialization attempts (cancelled143 due memory growth), isolated timeout124,
and deliberately superseded fresh audit130. Snapshot2 reuses the same fresh
Dune directory's unchanged dependencies; Audit.vo was absent, so all495reports
will genuinely rerun. Status/evidence, not the optimization alone, determines
whether the integrated development is verified.

## 2026-10-23 — exact invariant-rank and conversion restrictions

Refinement after challenging the stopping gate: a single WHOLE-HISTORY fold
can avoid the bare high-source/low-target iteration gap. With independent
H_b(t,history,u):U_j and low observation L(G,u,A):U_l, set
M_b(G,t,A)=forall history,u:C.H_b(t,history,u)->L(G,u,A), rankR=max(3,j+1,l).
The independently defined source acceptance can fold once at motiveU_R;
its own rank and the history length do not occur in M. This is a rank-feasible
candidate, not an available soundness theorem or a same-index no-go target.
The genuine next gate is hereditary/dependent application beta-splicing:
combine function/argument invariants, lambda exposure and a continuation
through annotated substitution, also respecting arbitrary supplied conversion.
LookupHistory is only structural lookup iteration; InternalReplacement proves
Scope, not this closure. Construct L and the independent actual reduction graph
and prove all six laws; do not postulate the beta law as a new target premise.

Choosing L=low typing does not give this beta law: the function IH returns
only low typing of the exposed lambda. Its high original derivation is gone;
recovering body typing and substituting the argument require low-graph
inversion/substitution with their local motive-rank problem. LookupInversion
offers high-source to low-child extraction, not low-to-high promotion.
A possible hereditary alternative quantifies first-order codes for environment,
elimination stack and whole execution, returns low head separation, and uses
independent fixed-rank query guards. The concrete open obligation is validating
images/frames plus beta-splicing/query composition and standard coverage.
Scope alone is insufficient; low typing returns the inversion issue; a guard
containing the hereditary predicate itself can reintroduce the rank cycle.
OccurrenceSafety only transports structural Ext-absence, not typed-head
incompatibility under beta replacement. None of these observations is a
no-go theorem against all hereditary interpretations.

A further candidate avoids reconstructing target typing proofs: a
derivation-directed closure/stack machine whose closures pair original
source-proof nodes with raw environments. A fixed finite source-node table
checks local syntactic rule equations and acyclic premise links; it does not
assume hereditary validity. Beta extends the environment and follows the
lambda-body node. The first concrete proof is the environment-extension/type-
closure square: the body context/type interpreted in the extended environment
must agree with the application codomain after annotated substitution, while
retaining arbitrary supplied conversion certificates. Then establish machine
closure/resource laws and terminal head separation. Scope-only replacement
and structural lookup histories do not supply this coherence. This is an
unimplemented alternative that may weaken the required invariant, not a
proved impossibility or an available theorem being withheld.

First constructor target for that alternative: a function certificate can end
in ConversionRule, expect Pi A.B, and expose a lambda whose body node carries
Pi a.B'. Beta must transport the argument from A to a and align B[u] with
B'[u]. Thus realize product-conversion injectivity and conversion preservation
under represented environments, without normalizing arbitrary zigzag nodes.
Native DefEq.equiv_Π_inversion and replace_equiv specify these laws but are
not internal PTS inhabitants. This gives a concrete independent syntactic
coherence target before selecting a hereditary semantics; it does not assume
bounded soundness as a premise.

InvariantObstructions proves in original typing that implication from rank r
to rank s has the UNIQUE rank max(r+1,s). In particular a homogeneous P->P
clause cannot inhabit P's own rank. An opened-algebra callback E->P fits the
rank-r motive iff rank(E)<r. The numerical graph-premise cycle is separate
from these typing theorems and is NOT an impossibility result for every
encoding. A same-index typing-preservation induction mentioning its own
Church judgment or an operation graph that must eliminate into that judgment
cannot be repaired by increasing the common index. Generalizing over a
same-rank environment contract has the same problem even after opening the
target algebra.

One-step finite stratification remains viable: low target judgment of rank l,
independent operation graph of rank o able to eliminate at l, source acceptance
with motive o+1. Its low result does not automatically feed the next high
source. The still-missing history-stable invariant/synchronized transformer
must be constructed before asserting repeated dependent soundness. Current
TermAt/Replace exact motive12 scope folds intentionally do not claim this.
Do not add arbitrary rank lifting, successful normalization, or model validity
as a hidden resource premise. An actual fixed transformation with pointwise
algebra homomorphism could avoid the all-output operation premise, but it
must be constructed and proved sufficient, not postulated.

Checked the fuelled-machine escape against actual APIs. For a fixed state
type S:U_s, the monomorphic iterator (S->S)->S->S has rank s+2, so internal
fuel itself is not the obstacle. We still need an actual step:S->S, guarded
raw initialization and every-state transition/closure laws. NormalizationComplexity
supplies native Rocq algorithms/bounds; the self-interpreter README explicitly
marks the general elementary-function compiler as unformalized. ChurchFinite
uses externally selected tables/dimensions/iteration counts. None is the
missing homogeneous raw-code machine. Current C:U2 folds only into X:U0,
so using X=C for a direct destructor is ill-typed; fused maps do not supply
that destructor. Higher generation guards or a different state encoding
remain possible new constructions, not a proved impossibility. Resource-
certified finite semantic tables are another option, but their validity
must be constructed, not assumed by the envelope.

The same module gives an accepted ConversionRule proving U1:U0 with equality
U0 <- (lambda z:U0.U0) Omega -> U0, Omega=(lambda x:U0.x x)^2. It proves the
middle term has an original beta self-loop, is not sn, and is untypable in
the empty context. Hence normalizing/typing ALL raw equality intermediates
is a false bridge, not just an unfinished lemma. Preserve the independent
checker and use arbitrary-term conversion transport. These results constrain
milestones 2–4 but do not refute the direct relational consistency programme.

## 2026-10-23 — weak finite satisfiability and Willard: goal 5 preparation

Working hypothesis requested by the user: the weak local finite satisfiability
in CombinatoryPTS-rk.tex, sec-ground-horn, is probably highly relevant to a
non-Gödelian consistency interpretation. Preserve it as a research direction,
not a theorem about PTS-rk. GroundHorn.singleton_model is generic for ANY
rule relation, including one with an axiom deriving the contradiction atom.
Its all-true valuation therefore gives no negative-query separation. Positive
ground-consequence equivalence is not preservation of falsity or of arbitrary
quantified formulas. The vocabulary is recursive, infinite and nullary.

Primary reference: Dan E. Willard, https://arxiv.org/pdf/1108.6330v8,
Definitions 3.4, 4.2–4.4, 5.10 and Theorem 5.11. A configuration fixes language,
bounded formulas, standard-true Sigma1-complete base, deduction and proof coding.
0-stability requires every bounded consequence of B union theta with proof
length Log(p) <= #theta+1 to be standard-true, for every r.e. Pi1 theta,
including false theta. Here #theta measures truth under quantifier bounds
2^N. The conclusion concerns B + SelfCons^0(B,d), not unchanged B.
Definitions 5.1/5.3 and Theorem 5.9 give stronger stability variants.

Second primary reference: https://arxiv.org/pdf/1307.0150v2, Definition 3.2,
Theorem 4.1 and following discussion. Its consistency-preserving construction
requires standard-true source axioms and the specified tableaux/Tab-1 deduction;
the analogous construction fails for Hilbert/Tab-2. This is not a prohibition
on every Hilbert-based self-justifying theory, nor a classification of our PTS.

Concrete next checks (our proposed application, not claims from those papers):

- Specify the exact represented deduction/acceptance predicate and quantify
  over its actual proof resources. A finite catalogue named Hilbert does not
  identify Willard's deduction system or coding.
- Refine the local models to make the translated contradiction false while
  validating used rules. Do not insert that separation as an unexplained
  hypothesis: for a whole system it is the consistency problem itself.
- Define independent bounded truth and prove resource-sensitive preservation.
  Rank compression/finite packing may control the construction; neither
  implies the stability law or internal all-budget soundness.
- Realize the preservation argument internally and connect its domain and
  proof predicate to Cons_dir. Standard-code coverage is not this transfer.
- No new axiom is authorized: prove an original PTS inhabitant, or prove an
  interpretation transferring an applicable result to the exact target.
- Identify the actual diagonalization/derivability/domain-closure boundary.
  Do not infer its failure merely from a relational presentation, pointwise
  admission, or the existence of finite models.

The roadmap now records this preparation. It is independent of progress on
milestones 1–4 and does not discharge their normalization/soundness gates.

## 2026-10-23 — standard realization before term-valued binder lifting

RenamingLookupRealization constructs the pointwise fixed-environment lookup
family under weak rho. RenamingRealization reuses original tApp/substitution
proofs to apply each already typed constructor, then recursively generates
the graph witness for every original annotated term. Its standard shift
specialization supplies the entire family itself. Exact raw/decoded endpoints
come from existing codec/operation equations; the output-scope witness actually
applies renaming_scope, not a native scope theorem. These are executable
external witness generators, not an internal uniform renamer or arbitrary-
inhabitant reflection. Interface ranks do not grow with binder nesting.

Use the minimal nonrecursive single-substitution environment first: zero maps
to the supplied image, successors to old variables from independent Index/Succ
evidence. The graph has exact motive12 and rank13; no rank14 padding or general
finite-environment decoder is needed. Its rank14 TermFBound theorem assumes
only scope of the supplied image, independently constructed for every original
term. Neither environment clause assumes its output-scope conclusion.

Next keep this term-valued environment fixed under binders. A successor lookup
clause may carry the existing Rename(ShiftEnv n,n',n,n',0,u,v) graph directly;
avoid another Church wrapper. Derive its scope using bounded_shift_bound and
renaming_scope with the SAME successor edge. This suggests exact motive12 and
lookup rank18 (Rename has rank16), but this lifted graph is not yet implemented.
Preserve its recursive lookup premise for standard operational coverage even
if the scope fold does not need that induction hypothesis. Dependent typing
requires its own stronger invariant; scope preservation alone is insufficient.

Independent recursive verification may use supported -bytecode-compiler yes.
Pinned checker sources confirm that it still traverses and checks all proof
bodies; it changes VM conversion, not admission of modules. It uses serialized
VM bytecode and is therefore distinct from the VM-disabled reduction path.
Record the flag, source manifest, complete inventory and actual exit status;
never hide the earlier timeout or use -admit/-norec. This does not alter project
proofs, kernel rules, checker definitions or repository CI settings.

## 2026-10-23 — source-directed scope and one environment across binders

Keep native correctness distinct from internal realization. CodeSubstitution
implements raw annotated renaming/replacement/substitution and proves exact
Syntax agreement, independent Replaced/computation agreement, scope preservation
and scoped totality. InternalBinary and InternalScope instead construct actual
PTS relations/terms. Their independent binary successor/index/scope rules do
not mention typing, normalization or the preservation target. Standard witnesses
cover every bounded index and original annotated term, including untyped terms.

Avoid repeated Church re-encoding of a lifted environment: this naive design
raises the environment rank with binder depth. Keep a fixed F:C²->U12 and
represent depth/current bound explicitly in RenAt:U14. Its exact motive10
fold proves Index(currentTarget,output) under FBound(base,F). The source-bounded
successor graph independently supplies this premise; do not assert it of an
unrestricted successor graph. RenAt does not assert currentTarget=base+depth.
Its all-output bound is proved, not an exact arbitrary-inhabitant decoder.
Restoring that global equation is not a prerequisite: standard witness
generation can thread the coherent canonical states needed by weakening.
No impossibility claim is made about other fixed-rank encodings.

Source-directed Rename carries local source Num/Index guards, independent
RenAt evidence and successor edges, with recursive annotation/body operations.
The annotation stays at the current depth; only the body uses successor depths.
The environment/base never change. No graph clause contains output Scope or
FBound. Fold with exact Scope motive12, obtaining relation rank16 and preservation
type rank17. This avoids inversion of a separate scope proof and needs neither
environment functionality nor global lookup inversion. Compilation status is in
STATE/BUILD, not inferred from this design record.

Next prove exact forward standard realization of the existing bounded-shift
graph on every original t -> shift t. Then term-valued lookup can lift images
using that witnessed weakening. Begin with the single-substitution environment
(zero maps to the supplied term, successors to old variables), deriving its
local scope contract independently. General environment reflection, global
functionality and complete certificate reconstruction are not prerequisites.
Native substitution correctness plus internal scope coverage does NOT itself
realize internal renaming/replacement. Dependent typing/conversion preservation,
operation sufficiency, resource admission and consistency remain separate.

A concrete realization plan avoids arithmetic casts for n+depth: parameterize
the native term induction by rho:Fin m->Fin n and a supplied family of actual
RenAt witnesses for its points, keeping F/base fixed. Under a binder, build
the lifted family with ren_at_zero/ren_at_step and standard successor witnesses.
Instantiate the family at depth zero with bounded_shift_intro, index_witness
and natural_successor_witness to cover original shift. The final shift theorem
must CONSTRUCT this family, not retain it as an assumption. This is a plan,
not an already checked bridge or a requirement of global state coherence.

Verification is a documented delta audit: all public endpoints are rebuilt in
a fresh absolute Dune directory; recursive kernel checking covers every new
module and its complete dependency closure, compared with fresh pristine
upstream. Old optional modules outside that closure retain their preceding
full recursive audit and must match its source hashes. No CI checks/settings
are removed or weakened; neither this nor earlier focused runs is full CI.

The 811-second isolated renaming compilation exposes a proof-engineering cost:
recertifying expanded closed graph terms repeatedly normalizes nested dependent
types. Higher layers should prefer compositional original-typing/application
proofs that reuse established lower-layer typings, or a genuinely proved open
algebra interface followed by original substitution. Do not hide a typing
assumption in an interface, disable conversion checks, or alter the shared
checker to obtain a faster green result. This is an optimization opportunity,
not an additional mathematical prerequisite or a weaker verification contract.

## 2026-10-23 — consumer-directed preservation instead of global decoding laws

Dependency review finds no implemented consumer of arbitrary-path Eq_0
functionality or matching-constructor inversion. Keep their statements and
partial infrastructure, but remove them as mandatory prerequisites. Use
independent constructor-indexed operation/checker relations and preserve an
explicit consumer invariant for EVERY related output. Thread the same output
through dependent uses; do not identify independently obtained outputs
without the coherence theorem actually needed. Actual forward realization
of general accepted standard judgments and all six original rule clauses
remain obligatory. Reverse canonical agreement identifies the EXACT checker,
but is stronger than the negative implication needs: an independently defined
overapproximation is safe only if soundness handles EVERY acceptance proof.
Keep exactness as the stronger specification, not a logical prerequisite.
Pointwise realization is not an internal consistency-sentence implication;
that additionally requires uniform internal acceptance/domain translation.

RelationalTransport proves positive descent for exact rank-4 predicates and
dual negative safety for upward-closed predicates, with explicit local laws.
OccurrenceSafety supplies a nontrivial negative example, Absent(seed,a) =
Ext(seed,a) -> Bottom. Its rank-7 family propagates through Look_5 by factoring
through lookup-to-extension and transitivity, not by illegal rank-7 elimination.
The Stop observation and positive rank-3 padding construct absence of every
nonzero leaf and every pair from stop. This is represented Ext-absence, not
a complete native absence characterization or the target consistency claim.
Tag-erasing Cap cannot substitute for label-sensitive Ext here.

LookupHomomorphisms opens target lookup/history before folding the source.
Actual shape and generated filling preserve Look_5, Look_6 and Hist at the
unchanged motive ranks, preserving the path and mapping root/value. Native
specifications are separate from original PTS application/realization in
SimulationRealization: apply the literal internal maps to prior witnesses,
then convert endpoints by proved beta equations. Filling may introduce new
successful paths; only forward preservation is claimed. These operations
are not dependent source substitution. All previous proof modules unchanged.

Fixed-rank histories already bypass same-rank composition. Structural
operation closure and independently constructed standard resources may
replace internal numerical capacity comparison; this is a prospective
soundness design, not a proved sufficiency result. The final resource CPS
package needs no internal selector. Preserve a sufficient independently
defined invariant rather than reifying complete transported derivations if
possible, but charge all represented data and derive normalization/history
existence or its negative continuation internally. Actual binder/substitution/
conversion laws, terminal source separation, full resource sufficiency and
standard raw-input admission remain mandatory. No impossibility claim.

## 2026-10-23 — fixed-rank histories, stratified cases and structural capacity

Preserve C, Good_1, Look_5, Look_6 and every earlier proof module. A history
has independent root and segment rules: each segment supplies Look_6 and
the recursive history, never the final Look_5 conclusion. Folding its exact
rank-7 invariant with the existing root/composition terms proves Hist ->
Look_5 at rank 11; Hist itself has rank 10. This supports arbitrary finite
length at one interface, not same-rank Look_6 closure or an arbitrary lift.
An executable history generator has exact sequential-lookup erasure and
original typing; the integrated theorem applies internal soundness.

One-step case elimination separately uses Look_9, defined by the same local
rules. A rank-9 continuation pair retains a low lookup and a rank-5 motive
result; projecting gives case handlers with ACTUAL Look_5 child witnesses.
The relation, view and inversion theorem have ranks 11, 9 and 12. Standard
Look_9 coverage is independently computed, not assumed from Look_5.
This is stratified case elimination, NOT matching-pair injectivity/inversion.
The exact full functionality target is only formed at U8, with no inhabitant
or hypothesis. Its direct induction motive exceeds Look_5's motive rank;
Eq_0 does not automatically transport higher-rank predicates. Do not confuse
native syntax injection with internal pair/path injection. No impossibility
theorem is claimed; alternatives using weaker sufficient invariants remain.

Capacity is Ext(shape a, shape b), where the literal Church fold erases leaf
tags and preserves pairs. Its rank is 6. Internal laws include generation,
reflexivity/transitivity, extension/join and lookup/history capacity. This
has native subtree-capacity semantics, stronger than numerical size order, not a resource
sufficiency oracle. Prove exact beta correspondence on ALL raw trees and
realize every native shape-subtree inclusion in original PTS. Finite-family
packing supplies one explicit common budget; it does not supply missing
normalizer/checker intermediate data. Packing/fill and flattened-path/result
size estimates remain external arithmetic, not bounds on complete written proof
histories. No source acceptance, normalization,
consistency, axiom or stronger carrier guard enters these definitions.
The size implication concerns native shape-subtree inclusion; do not infer
native size bounds from arbitrary Cap inhabitants without a converse theorem.

## 2026-10-22 — structural substitution and stratified lookup composition

Retain the original C : U2, Good_1 guard and Look_5 relation unchanged.
Define plug by replacing NZero leaves via the existing Church fold. It is
total structural substitution, not a partial path parser; on standard paths
it is beta-exact concatenation. Prove generation, associativity and guarded
units internally. Preserve quotation's syntax injection; never equate beta
correspondence with literal syntax equality or add eta conversion.

Define Look_6 independently with the SAME root/left/right rules and motive
rank 6. The new relation has rank 8. Opening the target Look_5 first exposes
a rank-6 continuation motive; this yields an actual rank-9 composition term
Look_6(a,p,b) -> Look_5(b,q,c) -> Look_5(a,plug(p,q),c). No composition clause
or soundness assumption is added to the relation. An executable external
generator proves all standard successful lookups have Look_6 witnesses.
The composed standard theorem applies the actual internal term, then uses
the independently proved beta equation for concatenated paths.

Do not call this same-rank composition or infer a lift of arbitrary Look_5
proofs. This technique consumes a higher motive level; it does not prove
that all alternative fixed-rank approaches are impossible. Uniform iteration
at one interface still needs its own argument.

For the first inversion/functionality laws, fold the carrier into U1:U0 to
define independent Atom and Stop observations. Their literal leaf/pair cases
are Top or Bottom. Internal laws yield Atom(root) -> Stop(path) and, under
Stop(path), both directions of rank-0 Leibniz equality of root/value. Derive
root functionality and step rejection from leaf-like resources, for arbitrary
represented arguments. Eq_0 has rank 4 and is NOT native syntax equality.
Positive rank-4 padding gives exact rank-5 lookup motives. No normalization,
parametricity, resource sufficiency or target consistency hypothesis is used.
Full arbitrary-path inversion/functionality and size/capacity remain open.

## 2026-10-22 — fixed-rank structural resource graphs

Keep the ORIGINAL carrier C : U2 and Good_1 guard unchanged. Resources
are binary trees; structural paths use an empty tag and left/right tagged
pairs, without Church numeral conversion. Distinguish append-only left-spine
prefix from two-sided subresource extension. Pairing joins resources; it
does not pretend to be flat-list concatenation.

Define prefix/extension by transport of rank-4 predicates closed under local
pair growth with independently generated siblings. Both relations have
rank 6. Reflexivity and transitivity follow by identity/composition at the
same predicate; transitivity is not an added rule or hypothesis. Generation
preservation instantiates the predicate with the ORIGINAL Good_1 family.
The join inclusions require generation of the respective other sibling.

Define lookup independently by root/left/right rules at exact motive rank 5.
The root rule requires a generated value; steps require a generated sibling.
Lookup has rank 7. Original PTS terms prove step laws, root/path/value
generation and lookup-to-extension, with fully quantified types of rank 8.
The transport motive P(value) -> P(root) has exactly rank 5. Guard extraction
uses the inhabited rank-4 type I = Good_1(atom NZero): I -> Good_1(x) has
rank 5 and applies back to the existing inhabitant of I. This is explicit
positive rank padding, not cumulativity or a new premise.

An independent external algorithm finds the selected subtree. Executable
witness generation erases exactly to that algorithm and returns literal
original-PTS proof terms for every successful standard lookup. All standard
prefixes/extensions also have realizations. External size bounds count the
entire structural path and selected value; they are not internal arithmetic
or operation-cost results.

Do NOT infer a converse/parametricity theorem for arbitrary Church-relation
inhabitants. No internal total decoder, arbitrary-input lookup functionality,
path-composition graph or size/capacity comparison is yet established. Ext
transports rank-4 constructor-closed predicates only; it does not automatically
transport rank-7 lookup claims. Concrete join steps have explicit path/witness
updates. Audit any further higher-rank interface rather than silently raising
the existing guard. None of these definitions includes source acceptance,
normalization, budget sufficiency or the target consistency theorem.

## 2026-10-22 — literal PTS carrier and guarded finite-table witnesses

Realize the homogeneous serialized alphabet directly as 29 Church leaf
arguments plus binary pairing at one original PTS type C : U2. Keep
certificates structural; this adds no raw HOAS envelope to the interpreter.
The meta-level tag positions are a fixed finite telescope, not runtime
Church numerals. Executable quotation and generation cover every raw tree,
and quotation remains syntactically injective.

Use an independently specified constructor guard Good_1(x) : U4, with
exact rank-1 motives. Pair generation has type rank 5. Do not identify
generation with parsing, acceptance or resource admission, or assert that
all Church inhabitants satisfy it. Future graph/induction motives still
require their own exact-rank guard design; no cumulativity is available.

Reuse the unchanged shared annotated assembler and sound native successful-
run checker, rather than duplicate them. Original PTS typing is every witness
endpoint. Neither arithmetic interpretation, a set model nor an EA/H transfer
is imported. Retain the seven prior certificate/serialization files unchanged.

For the internal finite pilot use Boolean selectors E : U1. Can_1 and Can_2
both have rank 3 but eliminate at DIFFERENT exact motive ranks. Open output
guards/equality predicates before input elimination. The binary laws then
use rank-1 motives and have fully quantified type rank 4. Tables and four
entries are ordinary fixed-type arguments. Selector dispatch yields explicit
expansion, not beta equality to an arbitrary entry: prove guarded expansion
closure/equality and never invoke eta conversion.

Close a small complete rejection gate: all closed height-zero certificates
with recorded labels <= 1, independently classified as the two sort rules.
Generate the finite PTS table from the native raw checker and prove its
computation/coverage. Refute its acceptance on ALL Can_2 inputs using a
rank-2 implication motive; the two branches are identity on Bottom after
local syntax checking. This is not global normalization or external
Bottom emptiness, and the bound is not silently generalized. Next construct
variable-size resource graphs and guarded closure/joining at a fixed carrier.

## 2026-10-22 — homogeneous binary certificates with exact decoding

Use one external code tree, Atom over a fixed finite tag type plus binary
Pair. Encode every natural label/index by canonical positive bits with a
separate zero. No unbounded natural occurs as an Atom payload. Complete inputs
carry the scope index and both context and typing certificates, including all
annotations and equality instructions. The decoder reconstructs ORIGINAL
scoped syntax; acceptance is the existing independent native Boolean checker.

Require both inverse laws. Re-encoding every successful decode gives the
literal input tree, so missing/extra fields, wrong tags and noncanonical bits
are rejected instead of repaired. Encoding is injective, including complete
inputs across scope indices. Use shared proof tactics for the repeated parser
fields while retaining each explicit grammar clause.

Raw compression is partial only at the structural decoding boundary and
preserves acceptance. A well-scoped rejected input can still be compressed;
the domain theorem contains no acceptance/soundness condition. Malformed trees
remain raw carrier values, rejected by the checker; eventual resource admission
must include them too. Successful parsing is not the final admitted-domain guard.

Charge all nodes in the serialized tree, including binary labels and repeated
fields. Prove the whole-input support bound and every compressed label bounded
by that node count, plus the exact positive-bit encoding size. This settles a
representation-size obligation, not a binary machine cost or proof-transport
bound. The new fixed homogeneous carrier is still Rocq data; its PTS realization
and guarded internal finite elimination are the next construction.

## 2026-10-22 — native certificate adequacy and complete-input compression

Start the direct consistency library with the explicit-location Agda certificate
format, using ORIGINAL scoped Term nat, Ctx, Typing.typ and RankSorts. Keep the
six-rule grammar and executable Boolean acceptance free of native typing and
normalization premises. Context declaration proofs are separate checked inputs;
original sort/variable typing alone does not certify context well-formedness.
Completeness from Prop-valued typing is an existential Rocq theorem, not an
extracted derivation-directed program or an original PTS inhabitant.

Count distinct support labels below each source label. Preserve successor at
supported predecessors, monotonicity everywhere, and hence each used max(S a,b)
product equation. Include context PROOFS, annotations, conversion instructions,
explicit rule ranks and computed product ranks. Compression preserves checking,
original typing, term node counts and Bottom; support labels remain distinct.
Charge repeated data on expansion. The proved bound is on label occurrences;
binary serialization cost, checker/substitution output size and transported
proof/history size are separate obligations. Raw beta intermediates are never
required to be typed or normalizing.

Use only PTSrk/Stdlib/Equations dependencies. Neither arithmetic interpretation,
the set model nor an Agda axiom is imported. Intrinsic scoping simplifies this
first external interface, but does not replace the next homogeneous structural
serialization/decoder and fixed-carrier guarded finite-elimination construction.
Do not present this external milestone as the roadmap's internal compression
gate, all-budget soundness or consistency proof.

## 2026-10-22 — direct resource-relativized internal consistency

Prefer proof-local syntactic soundness and normal-Bottom separation to full
fixed finite logical models. Existing Agda contextual soundness and finite
packages are external specifications; they are not internal PTS proofs.
Use the complete native certificate grammar, including annotated raw beta
witnesses, rather than silently identify it with the draft's typed-equality
T^e. Put all checker traces into the chosen quantified package or prove
resource joining explicitly for separate variables.

Fix homogeneous code/resource carriers and independently specified guards.
Resource validity must not contain acceptance, successful normalization or
semantic soundness; every standard raw input, including rejected inputs,
must have admission evidence at the SAME fixed type. Good/finite-case
guards supply exactly the induction ranks used, not all-code parametricity.
Distinguish compression of source labels from fixed-rank target uniformity.

Aim for one original PTS term BS(q,b): Res(q,b) -> AccBottom(q) -> Bottom.
Adm(q) := Pi Z:U1. (Pi b:B. Res(q,b) -> Z) -> Z then allows direct negative
assembly without choosing budgets or returning normalized outputs inside
Adm. This is the new relational consistency interpretation, not an
unproved identification with the old finite-ordinal sentence. No H/EA
derivation or unverified Pakhomov transfer enters its proposed dependency
graph. Replay the needed proof-local/relational devices directly instead.

Keep internal history existence, arbitrary conversion witnesses, full proof
transport costs, normal-head separation and the Gödel-condition audit as
explicit gates. Do not require full dependent CPS, intrinsic tag-free
fidelity, rank-only full-PHOAS signature or native combinatory completeness
unless a chosen alternative actually uses them. The present change is a
reviewed roadmap only; do not manufacture proof modules or axioms for its
unproved obligations.

## 2026-10-22 — shared algebra folds without mandatory syntax tags

Use one `Algebra` interface: an ORIGINAL typed finite-telescope filling,
with one actual object-language application-spine fold for both type and
term programs. Exact adapters share it with existing STLC PHOAS and new
finite-dictionary combinatory codes; do not recode their payloads or add
numeral conversion. `UnifiedAlgebra` exposes all-source dependent programs
and identity unquotation without the raw envelope. This unifies the API,
not the varying plan-indexed signatures or their law realizations.

`GenericFold` supplies an actual normal head per signature,
`lambda P. lambda Q. lambda Sig. Q Sig`. No selected filling occurs in
the head: fields are ordinary remaining arguments. Explicit expansion
is not eta conversion. Its composition law is syntactic beta computation,
not semantic fusion or typing compatibility of unrelated interfaces.

Preserve the old faithful API: generic recovery gives conversion reflection
through a common algebra and literal injection for normal sources, not
all unreduced syntax or cross-plan fidelity. A structural parser invariant
through constructors, casts and signature growth is the next intrinsic
proof; external QuotationTree metadata is not that parser. Keep the proved
obstruction to conflating faithful code with a conversion-preserving index.

Require concrete nonidentity fillings, not just a generic fold theorem.
The STLC observer runs unchanged intrinsically faithful codes; its distinct
normal sort tokens are not eliminable Booleans. Its typed beta example
proves non-invariance under source conversion. Local CBN handlers and
literal CPS-type rank proofs are separate from complete dependent CPS.
Their rank-one-source/unbounded-target counterexample limits that specific
translation, not all continuation encodings.

Combinatory codes use a finite external atom dictionary and no binders in
their represented tree. Their Church implementation has actual PTS binders,
normal intrinsic tree fidelity and type rank r+2. Same-code CBV continuation
and finite-selector observation use exact compatible ranks, never cumulativity.
The concrete 65-shape Hilbert bridge is extraction/coding, not native source
completeness or internal dependent evaluation of heterogeneous expansions.
Keep dictionaries fixed when stating fidelity; finitise may vary them.

Numeral adapters are optional interface layers. Removing serialization does
not remove external resource indices, the literal-alphabet obstruction or
universal accepted-certificate soundness. Keep the self_consistency target
and its required arithmetic/structural-code bridge independent of soundness.
Keep compatibility proofs, streamline the public README/exposition, and
audit the new surface separately while retaining the full audit alias.

## 2026-10-22 — independent contextual certificates and joint finite carriers

Use an independent raw proof-tree grammar for all six original rules and
explicit beta steps. Acceptance checks recursive subtrees and syntax equations;
native Typ, WellFormed and TypedSub are conclusions, not input fields or
acceptance premises. Prove both soundness and certificate completeness.
Compute a sufficient semantic redex-rank bound from original typing by
structural inversion; never equate that bound with the subject's outer rank.

ModelInput contains independent source/target context, environment and
derivation certificates. Normalize instantiated subject and type together,
retaining exact substituted source typing by preservation. Output grades
and finite prefix alphabets are computed; prefix size may exceed nodes and
must enter the seed. Proof/budget independence concerns decoded normal forms,
not equality of the entire grade-dependent record.

Count contexts/types/values and both-context substitution packages jointly,
with propositional semantic fibres and actual finite injections. Cover raw
valuation images without assuming independent normalization of dependent
tuple components preserves their exact typing. Prove alphabet and valuation
composition coherence separately. External Void exclusion follows by normal
form inversion and computed-bound normalization, not a new axiom.

These results give all-six-rule contextual graded syntactic soundness, NOT
fixed finite first-order models. Rank-one normal products already have
unbounded lengths at a single label. A faithful size-bounded type carrier
cannot be closed under all such constructors; this does not prohibit
nonfaithful finite models. Next construct total finite semantics for an
explicitly specified logical fragment, with coherent dependent fibres and
all axioms under every semantic valuation. Do not confuse this with syntactic
typed substitutions, internal reflection, or an internal consistency proof.

## 2026-10-22 — total Agda normalization and graded soundness

Prove the original six-rule annotated metatheory rather than adding
normalization/output typing as API premises. Computed inversion families
and generic Fin elimination avoid unsupported Cubical indexed matches.
Parallel reduction gives confluence/product injectivity; typed substitution
and context conversion then give preservation, enabling semantic rank
safety and strict greedy descent. The dependency chain is noncircular.

Keep normal input syntax intrinsic and typing certificates propositionally
truncated. applyTypedWithin returns the exact Y[y] fibre and bounded trace;
the raw untyped bounded attempt remains separate. Generic normalize takes
the semantic redex-rank bound, not an insufficient outer-type-rank bound.
Prove native equality/normalization adequacy and budget coherence explicitly.

Model ingredients are finite fibres per fixed type and fixed alphabet,
coherent size embeddings, graded application and finite-state typed
execution. Duplicate labels mean native equality need not imply raw code
equality. The current application alphabet premise is a≤1+|f|+|y|; extending
alphabets and bounding type/universe carriers are genuine next obligations.
No fixed carrier closure, arbitrary-valuation model, accepted-certificate
soundness or internal consistency follows just from this milestone.

Keep source-derived highlighted excerpts and proof links in the note;
replace obsolete totality gaps with exact remaining model/compiler gaps.

## 2026-10-22 — future objective type theory and partial-function arithmetic

Record the user's three linked research directions before the references:
an objective PTS-rk variant with quadratic checking (van den Berg/den Besten,
arXiv:2102.00905, Theorem 7); a finite-basis logic-free partial-function
arithmetic using graph-extension judgments, finite core axioms plus exists_n,
partiality-compatible induction, finite models for every schema truncation,
and quadratic derivation checking; and an effective interpretation of the
variant into that arithmetic. These are goals, not established theorems or
changes to the original kernel. Count all encoded annotations/certificates.
Preserve the collapse disjunct; distinguish the requested finite satisfiability
from the stronger noncollapsed-model goal. The schema's intended disjunction
is to be encoded in the extension calculus, not added as full first-order logic.

## 2026-10-22 — explicit finite Church compilation and consistency boundary

Use nonempty polymorphic finite choice E_m^r = Pi X:U_r. X^m -> X.
It has original formation rank r+1, and its canonical selectors/types have
exactly 2m+3 annotated nodes. A map Fin m -> Fin n reindexes continuations
at the SAME X, so its type has rank r+2 rather than requiring elimination
at the whole output selector type. The r=0 encodings already suffice for
all fixed finite carriers; syntax/type size, not these ranks, grows with m.

Compile the single greedy-pass and application-constructor finite tables,
not precomputed final answers. Clip out-of-budget transitions to the input
state, proving clipping cannot occur on legitimate tower-bounded runs.
Emit exactly d nested PTS applications; add no object-language recursion
primitive. The generated values are literal original annotated Term syntax.
FiniteMachine proves raw decoded execution; ChurchFinite.v proves original
typing/beta for arbitrary unary maps/iterations. Keep binary all-index
correctness and the cross-language Agda/Rocq correspondence explicit gaps.
Agda's selector typing/normality/size are independent checked proofs.

Do not identify canonical code subsets with all inhabitants, finite execution
with semantic models, or source node bounds with generated PTS program bounds.
Keep the fixed alphabet restriction and distinguish source redex rank d from
the encoding's chosen answer rank r. The prior total typed Agda output remains
open; code-to-code computation is not a semantic Y[y] inhabitant.

Relate the proposed internal consistency endpoint to the existing predicate-
only self_consistency plan and Pakhomov's resource-cut transfer, not a blanket
Goedel objection or an unsupported self-consistency claim. Graded model
closure/embeddings, independent certificate soundness, internal finite-case
principles and the exact interpretation J must still be constructed. The
all-true grounded-Horn models do not exclude Void.

## 2026-10-22 — finite normal representatives and exact Agda proof boundary

Length is not invariant under the QIIRT beta quotient, so measure length on
explicit annotated normal representatives. Define Nf, NonLamNf and erase
inductive-inductive-recursively: the head guard uses computed erase.
Prove erasure injective and complete for normal raw syntax. Exact/bounded
length fibres use genuine normal representatives, not an opaque raw tag.

Use the original six PTS rules and annotated beta closure, not a checker.
Count syntax through proposition-valued/truncated typing, rank and reduction
certificates. Prove AtMost by actual injection into Fin, not only a recurrence
estimate. Fix a finite label dictionary with a≤N; rank/length alone cannot be
finite because every U_i:U_0 is a one-node normal term. Count annotations in N.
A normal family's d bounds its type rank; the typed application API supplies
the function product's exact sort rank. Its N is 1+|f|+|y|.

Separate unconditional raw size/peak theorems from typed normalization.
FiniteTrace represents the actual deterministic beta path with Fin states,
not arbitrary uninterpreted edges; edge evidence is truncated. Whole walks,
proof objects and host allocations have no claimed cardinal bound.
applyTypedWithin returns Maybe(Result), while TypedResult names the exact
Y[y] goal separately. Do not hide missing subject reduction/rank descent in
inputs, axioms, pragmas, target-shaped certificates, or a replacement typing
relation. The total typed Agda interface remains open.

Place the finite-normalization section immediately after QIIRT. Extract all
Agda snippets literally from checked modules with exact marker matching.
Use a local math-font fallback for the truncation delimiter; keep glyph and
layout validation enabled. Proof badges distinguish Agda from Rocq.

## 2026-10-22 — conventional BCKW arithmetic and honest basis separation

Use W for contraction and B for composition. Treat I as a counted atom.
For the fixed carrier U_i use H=C(BB(CB))B, numeral0=KI and
numeral(n+1)=W(H numeral(n)); this gives exactly n W and 7n+2 atoms.
Successor=BWH, addition=B(B(BW)(BBC))(BB), multiplication=B.
Prove arithmetic over original annotated expansions, with fixed simple-type
index shapes independent of n; do not hide arbitrary type payload in atom size.

Use a separate independent BCKW(I)+P QIIRT, not an alias for dependent S.
Its structural diagonal is derived from comprehension. Shared-context
application and type-level substitution are not a binder-elimination theorem.
Keep the full dependent Hilbert/MM0 catalogue until an annotation-preserving
BCKW completeness translation is supplied. Positive simple-type macro tests
and negative dependent scope tests justify this boundary, not impossibility.
The user made wholesale basis removal conditional on the replacement working.

Use standard Knuth tetration as a convenient upper bound, not as an incorrect
identity with a seeded binary tower. Add tower_le_knuth; keep the tighter
executable normalizer bounds unchanged. State closedness in the finite-carrier
cardinality theorem and keep the input-label restriction.

Put concise BCKW exposition in section 2; remove the affine-generator section,
redundant independent-core exposition and development-history phrasing.
Read highlighted QIIRT excerpts from BCKW.agda. Preserve the exact quotient,
full MM0 source appendix and proof badges, distinguishing verified fragments
from external completeness and still-open native adequacy.

## 2026-10-22 — contraction/affine numerals and finite computation carriers

Use B for the user's duplication combinator (usual W), distinguishing it
from composition. Preserve the original annotated calculus. A fixed carrier
U_i permits checked B/J0/J1 numeral codes with n duplications and 2n+1 atoms.
Give the universal untyped affine packaging J=lambda z.z C0 C1 K explicitly;
its J-only trees yield n B and 49n+7 atoms, but do not claim this is an original-
typed dependent compiler. Retain the established Hilbert basis under the
user's complexity proviso: splitting S's argument changes dependent fibres,
and even polymorphic zero duplicates its type variable in annotations.

Reuse original normalization/rank/cost proofs, adding single-beta peak bounds
and rank preservation. State the parameter as the global redex-head bound,
not outer type rank; include a checked separation example. Apply this directly
to normal dependent application, whose only possible redex is at the root.
Count annotations in size. Distinguish normal original expansions from normal
binder-free output codes, and operation-cost accounting from bit complexity.

Replace the false rank/length-only finiteness claim by a finite input-label
alphabet. Prove beta never introduces labels, enumerate bounded raw/normal
syntax, and bound its capacity by a linear-height tower. Typed normal families
are predicate fibres, not collections of arbitrary proof witnesses. Do not
count arbitrary supplied convertible types in a subject-only size theorem.

State local finite satisfiability as an effective GROUND-QUERY Horn reduction
using countably many nullary predicates. Least-model reflection and all-true
singleton satisfiability are checked generically; the Hilbert instantiation
is a mathematical argument with finite conversion certificates. It does not
use the quantitative bounds and is not a finite-signature interpretation or
finite faithful syntax semantics. Preserve the separate MM0/native boundary.
Remove only the requested substitution-index prose, not its checked API/view.

## 2026-10-22 — linear exposition and executable safe Cubical syntax

Order the note as calculus/logical reading, finite-basis obstruction, four
core schemes, complete Hilbert presentation (literal catalogue followed by
MM0), independent core, QIIRT and exact relative quotient. Preserve the
external completeness argument and proof boundary, but remove progress
history from the exposition. Read highlighted Agda excerpts directly from
source; use a Unicode-capable local minted font. Keep the full MM0 appendix.

Declare Con/Sub before Ty/Tm, rename AnyTy to RankedTy, and document the
direction of substitution. Retain Sub Gamma Delta after checking a source-only
Sigma view with computed ctxOf and both round trips: argument reordering
makes composition/reindexing guard-free, but fixed extended-target projections
require equality and transport. A new recursive-target QIIRT would also add
target-path clauses. The view is a comparison, not a second QIIRT definition.

Use original Agda 2.8.0 and pinned Cubical v0.9 with --safe throughout the
import closure. Source pragmas select Cubical mode; a global --cubical option
caused incompatible primitive-module modes. Keep compiler data/configuration
isolated and recheck copied sources with --ignore-interfaces. Do not import
the paper artifact's unchecked eliminators or postulated model principles.
Ford guards and explicit type-path clauses preserve intrinsic typing;
successful syntax checking is not an interpretation, equality reflection or
source-completeness theorem. Keep the exact native-data-relative quotient
separate from the independently presented algebraic syntax.

Construct S's literal six-binder type with a finite bundle of seven annotation
equalities, not an arbitrary type/body parameter. Store the proofs as nested
built-in Sigma pairs; fresh dependent record/data bundles caused pathological
elaboration. Prove their canonical inhabitants and proof irrelevance outside
the mutual definition, yielding only the three numeric public S indices.
Keep the fixed-head I/K/S contractions, P decoding law and application
naturality guarded by their actual type equalities. Uniform annotation-guard
construction does not prove general logical-coherence guard admissibility.
No opaque or optimization-flag workaround is retained.

## 2026-10-22 — an explicit first-order MM0 Hilbert theory

Use MM0's own many-sorted Horn declarations, with raw de Bruijn syntax and
explicit numerical, shift, substitution and annotated-beta graph rules.
Read these by syntactic derivability, not a first-order categoricity claim.
Encode the 65-shape catalogue by fixed ranked telescopes and a syntax fold
with bounded prefix/exposure counts. Its body/type pair is fixed in every
catalogue row; there is no general fold-to-Hilbert typing axiom. Preserve
the native rank max(a+1,b), conversion's sorted target, annotations and no eta.
Distinguish MM0 rule axioms from new assumptions in the Rocq development.

Keep the complete theory in one 156-line .mm0 file. Include it directly as
a three-page appendix and extract the six Hilbert rules into Section 4.
Use a local listings language for MM0, whose lexer is absent from installed
Pygments; preserve minted Agda and restricted shell escape. Do not install
a custom-lexer security allowlist or duplicate code inside the note.

Compile the theory AND ten actual local .mm1 proofs, checking both against
the same public .mm0 specification with the independent reference verifier.
Pin tool provenance, retain a rejected capture bug, and state that examples
and declaration checks are not adequacy/consistency/completeness proofs.
No Rocq sources or CI rules change; retain previous fresh assumption evidence
with byte-identical source checks rather than calling cached builds fresh.

## 2026-10-22 — independent contextual Hilbert proofs and natural-model QIIRT

Keep contextual H+ independent: empty-context axioms, sorted start/weakening,
application, conversion and reductions; no lambda/product constructor and no
native typing premise. Derivation data live in Type, with inhabited data as
the Prop interface. This permits real proof measures without eliminating
original Prop typing into computational data. Prove internal context/start,
simultaneous substitution and empty-context 65/66 equivalence first.

Separate syntactic exposure simulation, its exact schema-type prefix, and
typed arbitrary-derivation exposure. Only the first two are now proved. Exact
I/K/S/P assembly retains its needed family derivations as honest local inputs,
not a theorem that assumes general deduction. Classify the seven long-head
cases, then model shared applications as finite acyclic reference programs.
The checked S six-to-three step is local. Neither ordinary tree size nor
maximum proof height supplies the general shared-measure invariant; do not
relabel it completeness. The note's explicit symbolic-template inclusion plus
Bunder–Dekkers 9.4 gives an EXTERNAL mathematical corollary for the literal
catalogue, distinct from an unproved Rocq original-PTS-to-Hilbert theorem.

Recast the intrinsic algebraic signature using unindexed-in-type Tm and a
recursive tyOf into Sigma Nat (Ty Gamma), retaining rank bookkeeping. Follow
the CPP 2026 natural-model/Ford pattern: explicit equality guards, interleaved
recursive clauses for term paths, and set-truncation coherence. Ordinary Agda
needs explicit typed setoids, not deletion of the quotient. Keep the weak GAT
and exact native-expansion quotient separate; no lambda, eta, quotation or
unchecked artifact eliminators. Available Agda 2.6.0.1 cannot validate the
unchanged 2.8.0 artifact, so label all snippets specifications. Enable actual
minted/Pygments Agda highlighting only in this note's local preamble/build.

## 2026-10-22 — typed algebraic quotients and an explicit 65-shape economy

Specify a genuinely first-order GAT using contextual families, not meta-level
functions Tm A -> Ty. Separate the independently specified weak I/K/S/P
equations from the exact typed-image quotient by original beta equality.
The relative quotient uses original typing at BOTH endpoints and transports
over type equality. Untyped quotienting can mix typable/untypable raw terms;
substituting current HasType for original typing also needs a conversion-
closure proof. Add neither arbitrary Ty-to-Tm quotation nor function eta.
QIIT pseudocode is a mathematical specification, not new Rocq axioms or a
claim of executable Agda. Keep the exact signature together in the PDF.

Check numerical I7/K18/S30 shape catalogues explicitly. Do not omit a closure
case merely to match Bunder–Dekkers' unlisted K17 count. Instead retain the
conservative 66-shape catalogue and PROVE an economical 65-shape calculus:
local K13 is derived by K00 U1 Ua P5(b,c). Substitute its independent Hilbert
derivation for source leaves to obtain exact judgment equivalence. Use a
17-constructor constant datatype, not a proof-bearing exclusion filter.
This reduction does not assert paper numbering or preserve shortness measures.

Catalogue-atom type/exposure closure is now internal and verified. Full
completeness next needs contextual derivations and length-controlled exposure
of arbitrary derived products; do not mistake the atom closure result or
native type correctness for that missing proof. Keep old audits unchanged
and extend the existing CI alias, with fresh assumption output separately.

## 2026-10-22 — concrete Hilbert inference before full completeness

Rename the physical development to CombinatoryLogic-rk as requested, preserving
the stable PTSrk.Combinatory library name. Put the concise LaTeX–Markdown note
and PDF alongside its proofs. Formalization badges use local source links
while the files are unpublished; external Bunder–Dekkers completeness has no
badge and is not made a Rocq axiom. Keep the detailed telescope proposal as
historical research, with a pointer to current status.

Define Hilbert derivations independently of original target typing. Catalogue
soundness is an explicit metatheorem premise, discharged in the concrete
numerical I/K/S plus eleven-product instance. Extract only universe/scheme/
application codes; prove their original typings and forward beta recovery,
including the dependent application type-conversion step. Do not present this
as a new independent typing calculus for the whole extracted-code language.

Represent the product catalogue by eleven fixed shapes with numerical
parameters, not source-term or typing-derivation indices. Verify declared-type
and product-exposure maps literally. Exposure is not eta conversion; general
symbolic fresh-sort replacement is not claimed formalized. P4/P5 also compile
into the existing four-family HasType calculus. Keep complete catalogue
formalization, completeness and further economy as separate obligations.

Add the renamed audit to staged CI without removing stages. Keep fresh
assumption/kernel evidence distinct from cached full-driver coverage, and
preserve historical paths in earlier logs rather than rewriting provenance.

## 2026-10-22 — distinguish an indexed combinatory core from completeness

Use original annotated macro expansions and beta equality. Fixed closed typed
atoms plus application have a uniform type-rank bound, even with all U_i;
FiniteBasis now proves the finite-basis obstruction. Index combinator families
by numbers, with actual type/family syntax passed as ordinary arguments.

The first positive library checks I/K/S/P, a separate optional dependent K,
and an independent mixed typing relation for binder-free subjects. Keep the
type-language and expansion-defined equality boundary explicit. Weak saturated
I/K/S rewriting is only proved sound, not complete or internally type preserving.
No eta, annotation erasure, new source constants or checker replacement.

Separate the external complete supersorted Hilbert catalogue from the proposed
smaller telescope basis. A naive application compiler needs representations of
inferred domain/codomain families that are not guaranteed smaller inputs; do
not conceal this recursion gap in indices or premises. The next constructive
route is explicit uniform compilation of the finite auxiliary catalogue.
The independent library depends on the kernel and normalization rank theory,
not on arithmetic, self-interpretation or set semantics. Preserve those ongoing
developments and their CI work; keep focused audit evidence distinct from full CI.

## 2026-10-22 — move varying runners into a fixed closure interface

Distinguish a common execution head from a common PHOAS constructor algebra.
Package the actual normal faithful program together with its normal executor,
using an existential-style Church closure. Exact-rank function padding bridges
the non-cumulative sort bounds. For fragment k the common head has type-sort
k+10 and takes a padded normal result type, closure code and fixed forcing
argument. The full spine is originally typed after type instantiation; do not
claim a forcing eliminator for arbitrary R:U_(k+1). Normalize only source type
annotations needed by this wrapper, never source t or its execution. Retain
the underlying capped theorem's separate literal type-program recovery.

Internal certificate reification is not obtained by wrapping the external
quoter. The closure code type is inhabited iff its result type, by explicit
original terms with a beta roundtrip. Hence accepted-code reification into
Code(Bottom) contains soundness, and cannot be taken as its own premise.
Keep independent code/domain/trace predicates and all admitted witnesses.
Prove the exact impossibility for unbounded literal recovery from fixed
bounded-literal numeric data; do not conflate it with Bottom-only internal
consistency. Use a finite bank of actual sort literals for bounded reification
leaves. External bank selection and internal numeric selection are distinct.

## 2026-10-22 — specify internal consistency before formalizing it

Keep the self_consistency directory documentation-only until independent
source calculi and actual proof modules exist. Its target includes the exact
certificate checker, trace predicate, arithmetic domain and interpretation;
external PTS normalization is not itself a derivation of that sentence.
Retain the draft's resource-separation/tagged-active-evaluation route to EA
bounded soundness, with explicit certificate-size and proof-history bounds.

Distinguish higher-order H^omega interpretation plus external Lemma 3.11
from the draft's first-order H plus Corollary 5.3. Do not infer a direct
higher-order interpretation from the existing R interpretation. Keep the
external transfer boundary visible without new axioms; a concrete transferred
source proof could instead be checked independently.

For the direct route, admission of codes must be defined independently of
checker rejection or the desired theorem. Internal reification must connect
the actual trace predicate to codes decoded at Bottom. A common numerical
rank bound, one head per fragment, and internal quantification over budgets
are separate obligations. Consistency needs no raw fidelity tag or whole-source
literal recovery. Test comprehension and internal reification early, alongside
the shared certificate/arithmetic work; no CPS formalization is required.

## 2026-10-21 — port full quotation at a caller-fixed budget

Keep the verified uncapped quoter/cost and extraction endpoints unchanged.
The capped port reuses the original local state, independent derivation data,
typed views/substitution and package theorems; separate plan/alignment/recursion
modules instantiate actual capped allocation. The bound on local binder ranks
is an execution invariant discharged by initial state, renaming and bounded
source-domain pushes, never a target-quotation premise.

State fragment coverage with k fixed before choosing the source. Membership
requires independent original derivation data whose pruned formation/literal
quotation budget is <=k; it does not mention target programs. quote_at runs
at that supplied k, and every_bounded_original combines full recovery/fidelity
with the common rank bound. Do not substitute each term's computed budget for
the fragment parameter in a purported uniformity theorem. Open coverage uses
annotated closure and its budget. Do not identify this budget with a semantic
redex bound, or bounded actual sort indices with cumulativity or one fixed head.

Large exported Rocq module aliases duplicate compiled environments. Expand
aliases into qualified references in the new fragment/capped modules; retain
the mathematical definitions and proof contracts. No CPS work in this port.

## 2026-10-21 — distinguish bounded interpreter ranks from one fixed head

Investigate genuine bounded-rank fragments with unbounded syntax size. A bound
on conservativeRank includes node count and therefore reduces to finite syntax;
that observation does not solve the intended problem. Nor does encoding a plan
as one natural-number index supply uniformity.

Keep the published full-source quoter unchanged while developing the capped
allocator independently. Its exact acceptance predicate adds a formation-rank
guard; it preserves original realized equalities within that cap. Local alignment
carriers have rank zero, so actual requests under bounded source-directed
telescopes have a size-independent field-rank bound. Prove the actual base bound,
arbitrary capped-layer preservation, typed normal interpreters and a common
type-sort bound. Do not claim source coverage before porting recursive quotation,
or use cumulativity to equate distinct actual sort indices.

Scope the negative result to finite LITERAL catalogues of fields. Arbitrarily
long rank-zero telescopes already produce infinitely many accepted normal
rank-two fields. Finite polymorphic coherence schemes, ordinary represented
environments and other rank-uniform interpretations remain possible routes.
The next mathematical interface must address varying signatures, not only rank
arithmetic. No CPS translation is part of this work.

## 2026-10-21 — optimize enumeration and distinguish plan bounds from uniformity

Preserve the full original-source theorem while improving its executable inputs
and allocation. Replace depth-sized syntax followed by node filtering with
direct exact-node generation; prove complete membership agreement. Reject
ill-typed carrier/operand/telescope candidates before expanding their Cartesian
products, while retaining original typing and actual filled-endpoint conversion
as acceptance criteria. Changed enumeration order may change slot numbers;
old byte-identical quotes are not a compatibility contract.

Prune conversions only when endpoint types are literally equal. Preserve the
annotated source judgment and prove idempotence and final quotation invariance
under arbitrary redundant wrappers. Do not describe this partial normalization
as full derivation-independent quotation. Prove costs of the ACTUAL output plan,
not just a free-standing numerical recurrence. Infinite identity-application and
conversion-detour families show unbounded current plan lengths at fixed ranks
and even fixed final judgment. Scope those negative results to this algorithm;
they do not prove impossibility for alternative rank-only interpreters.

Maintain a separate obligation ledger instead of reintroducing the historical
development narrative into the concise paper. The elementary compiler/numeric
reifier is an independent route, not an unfinished premise of the completed
PHOAS theorem. Runtime timeouts are evidence of the implementation's current
limits, not failures of the kernel-checked existence/recovery theorem. CPS
formalization is explicitly excluded from this continuation.

## 2026-10-21 — present the final interpreter without development history

The research note is an exposition of the completed numerical-plan family,
not a chronological proof log. State the full theorem early and explain only
the code interface, equality repairs, syntax tag, evaluator and six-rule
quotation argument needed for it. Retain the complexity motivation briefly,
the fixed-head obstruction with its exact scope, and the substantive
Brown--Palsberg/CPS comparison. Intermediate encodings, canonicalization and
auxiliary-law investigations remain available in source/history and the
development README; they need not be reproduced in the paper. Preserve
annotation normality, independent source data, original typing, numerical-plan
non-uniformity and the boundary between proved interpretation and open CPS.
No formalization change accompanies the editorial reorganization.

## 2026-10-21 — distinguish indexed unquotation from the deep CPS benchmark

Call the completed result a Brown--Palsberg-style numerical-plan-indexed
strong unquoter. Do not identify the varying family head with the paper's
fixed polymorphic unquote, or cross-index self-interpretation with same-index
self-application. Raw annotated fidelity is not canonical derivation-independent
quotation. The full-dependent identity interpretation does not already supply
the paper's alternative algebras. Its CPS operation returns a CPS program,
not necessarily a new syntax code, and its semantic correctness is explicitly
left unproved in the paper despite implementation/type-checking/tests.

CPS feasibility needs original rank calculations AND dependent algebra laws.
Continuation types inhabit computably higher ranks, and simple-type CBN clauses
are available on paper; their ranks can grow with arity at fixed source type
rank. A direct substitution fails the present decoder sorts and product laws.
Checked equality layers are realized at identity, not universally valid under
arbitrary interpretations. Non-convertible endpoints alone do not prove their
internal equality type uninhabited. The displayed CBV example rejects a naive
beta-conversion-preserving recipe only. Do not turn any of these observations
into a universal no-CPS theorem. Keep external derivation-directed translation
plus re-quotation separate from an actual internal PHOAS fold. No proof code or
PTS rule changes are made for this discussion; new calculations are paper-level.

## 2026-10-21 — full-source numerical-plan interpretation constructed

The completed structural source quoter, not a general no-go, is the positive
outcome. RecursiveQuotation handles every original rule without a target
quotation/coherence hypothesis. Its decisive separation is the literal typed
constructor view from a possibly coerced root cache. Actual application repairs
both independently recovered roots with exactly two complete checked numeric
layers, then structurally substitutes the codomain view. Conversion quotes its
already supplied formation child, not arbitrary untyped zigzag intermediates.
Terminal sort-to-code repair is nonrecursive, avoiding the U0:U0 cycle.

FullDependentInterpreter computes the initial budget and state from independent
Type-valued derivation data. Original Prop typing is used only to prove inhabited
data/coverage in Prop, never as a computational source. All-source theorem
contracts include original typing, full normality (annotations included),
literal source/type recovery and faithful program injection across derivation
choices/signatures. SourceClosure covers open inputs by original annotated
closure and ordinary variable application; open fidelity has a common source
scope. Arbitrary originally typed contexts require original wf, as before.

The external family indices are tag rank, source-interface budget, finite
numeric plan and result rank. The represented type is ordinary P; the term
program is ordinary Q. No source type, syntax or typing derivation is an
interpreter-family parameter. Numeric plans contain only length/node/literal
budgets, and their actual signatures enumerate all independently accepted
equality fields at those budgets. Nevertheless the plan may grow with source
syntax: do NOT call this rank-only fragment uniformity or assert efficient
enumeration. Each typed family member is itself within closed source coverage
at some possibly different numerical index, not necessarily its own index.

Proof-erased OCaml execution of the ACTUAL closed U0 path succeeded, including
the plan and normal raw/closed type/faithful programs. It is one leaf regression,
not all-source experimental evidence or a direct Rocq vm_compute guarantee.
Standard extraction's opaque-body warnings and dependent erasure are retained
in evidence; no new Rocq source axiom/unsafe cast was introduced. Final fresh
audit and full CI now pass:2229closed self-interpreter reports plus unchanged
upstream normalization, recursive kernel/pristine/frozen-source checks,
110stable manifest entries and226/226CI stages. The completed positive result
does not settle rank-only uniformity. The user subsequently authorized commit
and push; the newest STATE entry records the selected publication scope.

## 2026-10-21 — faithful actual programs and literal local scopes

FaithfulProgramDecoder packages the actual dependent PHOAS program together
with a normal raw HOAS annotation tag. The interpreter selects the PHOAS
program and then executes it using the original dependent decoder; it never
selects a precomputed semantic source value. This differs materially from
the earlier weak full interpretation. Generic selector/package lemmas are
reused, not its normalization-based payload construction. The tag proves
literal annotated syntax injectivity even across different signatures;
normality gives conversion injectivity. It does not supply source coverage.

LocalQuotationSpine uses snoc scopes n+base, so a local binder has literally
the original source scope S n. Growing the global signature preserves the
same literal source context, not its normalized or filled approximation.
The existing cons telescope is an allocation adapter only. LocalSpineNaturality
compares closed Pi syntax to prove its renaming agreement; proof-only scope
casts never become object-language primitives.

SourceQuotationBudget traverses the supplied Type-valued original derivation
and context data, bounding every recursive child and explicit/literal rank.
Original Prop typing has coverage, not forbidden elimination to executable
data. FullQuotation's numeric plan is idle/request/compose, evaluated with
literal intermediate realized signatures. Flattening recovers a vector of
numeric budgets. This avoids equality casts between dependent list-fold
states. No rank-only quotation-family or elementary cost bound is claimed.

Practical proof engineering: exported module aliases duplicate large Rocq
environments. Mechanical expansion of qualified names is permitted after
checking no consumers use the nested alias API; refresh hashes and checks.
This changes no original theorem or proof obligation. FullQuotation's first
successful alias-free artifact is21KiB, versus184MiB for the earlier aliased
QuotationJudgment environment. Local Module is rejected by Rocq9.2, so is not
a supported alternative. Completed caches may be cleaned only with exact
validated paths and separately retained verification logs.

## 2026-10-21 — executable quotation views and equality-only realized layers

The active user request is to reach a full dependent PHOAS interpreter or a
genuine impossibility result. Neither is proved. Existing uniform-head,
literal-ceiling and homomorphic-conversion obstructions remain restricted.

Arbitrary open-body recovery and concrete uniform-field application now use
literal source annotations and independent original typing. Their forward
recovery and guarded normality are separate. SourceValidity computes actual
result-type formation from supplied original derivation/context data, but a
quoter must NOT recurse naively on its generated result-type derivation:
application substitution can enlarge it, and U0:U0 gives a terminal-sort
cycle unless sorts are handled directly.

Retain literal source constructor views separately from target caches.
QuotationTree performs actual dual-scope substitution: a variable hit takes
the replacement tree's source shape but preserves the literal substitution
of the old target cache. Its Pi view gives children, NOT an equation between
the cache and their product code. NormalNeutralSubstitution proves exact
full-normality preservation by normal non-lambda replacements, annotations
included. Typed child/view compatibility is now constructed by QuotationCache,
QuotationViewRenaming and QuotationViewSubstitution. A term shape retains
Pi children independently of whether the root is used as a type. Variable
substitution may expose a Pi; original sort uniqueness aligns its rank with
the independently substituted cache. Direct codomain instantiation returns
literal B[u] and literal cache Bc[q], without quotation re-entry.

Investigate an acyclic equality-only signature extension as an alternative
to generating all coherence from a small fixed vocabulary. An equality may
be allocated only AFTER both endpoints have independently proved original
typing and their actual identity fillings are already convertible. Never
allocate an arbitrary semantic-value field. RealizedEquality constructs a
normal reflexivity realizer; ContextualEqualityRealizer closes it over a
dependent telescope and normalizes only this eraser program. A proved
lambda-spine invariant shows that full application returns the literal
payload unchanged, even with nonnormal domain annotations. This is not
external normalization of the quoted semantic payload. The global allocator
abstracts local dependencies back to the preceding closed signature.

Uniformization must enumerate independently checkable bounded syntax, not
"fields which make the desired quotation succeed." OriginalTypecheck is a
total metalevel computation with soundness AND completeness for unchanged
Typing.typ in original well-formed contexts; it does not replace that
judgment. BoundedSyntaxEnumeration enumerates original annotated terms with
explicit node/literal bounds. A layer may refer only to its preceding base
context, enabling an acyclic finite-DAG embedding. Thread a single realized
signature sequentially through source recursion: each repair appends the
WHOLE checked layer at computed numeric length/node/literal budgets. An
external finite vector of those numeric triples determines the signature;
no source syntax or derivation occurs in that index. This avoids merging
separately constructed signatures. The effective recursive coverage theorem
remains to prove. This candidate introduces
syntax/layer bounds; it is NOT yet a decoder uniform on a rank-only fragment.

The ordinary dependent P/Q decoder is now implemented in
DependentProgramDecoder, using TelescopeInstantiation to retain ambient
P/Q variables beneath the filled signature. It is originally typed at
Pi P:TyProg. TmProg(P)->Result(P), with a computed exact formation rank,
normality from normal signature/fill guards and literal closure recovery.
Its represented type is an ordinary argument; the external signature's C/E
must still be selected uniformly by the numerical family. This generic
packaging theorem is not an all-source quoter and does not hide one in its
premises. Fixed-signature closure injectivity does not prove full quotation
injectivity; that must track the finite source-constructor tree separately.

For the eventual closed interface, prefer an ordinary represented-type
program parameter P : Pi Sig.C_s and term program Q : Pi Sig.El_s(P Sig).
The fixed indexed decoder applies the actual identity fill to Q; its result
type El_id(P id) recovers the original source type. This avoids silently
indexing the decoder by a full source derivation or assuming that all
derivation-specific type caches coincide. P must itself be constructed as
a normal code program, not supplied as an unquoted semantic type/value.

These decisions do not assert global quotation, injectivity or full original
coverage. Original calculus, frozen libraries and prior results are unchanged.

## 2026-10-21 — contextual beta families with syntax-free finite indices

Realize the SPECIFIC cast-beta equation over an entire dependent telescope,
not a rule lifting arbitrary pointwise equality. ContextualTelescope retains
literal annotated lambdas/products and independent original formation.
ContextualBeta forms equality of the complete lambda closures. Its identity
witness is independently typed reflexivity; only its TYPE is converted using
proved endpoint reductions. No subject expansion, eta, cumulativity or
function-extensionality assumption is introduced.

TelescopeBetaFamily quantifies A, B, f and u over any supplied telescope.
Its identity program uses plain reduced annotations, with direct typing and
full normality proved separately. An extra abstraction over actual normal
domain-family parameters makes UniformContextualBeta depend externally only
on the rank vector and a,b,d. Do not index the finite field list by concrete
domain syntax. UniformTelescope generates neutral domains Xi applied to the
previous variables, with actual original formation, normality and exact
substitution naturality. UniformTelescopeRecovery computes lambda-closed
parameter values from every independently formed concrete telescope and
proves their TypedSub plus annotation-wise recovery. The exact exported
closure corollary ends in U_s; arbitrary open-body/lambda transport through
the accumulated scope remains a separate integration task.

Keep LENGTH and RANK bounds distinct. ContextualBudgets proves that closure
rank1 permits arbitrarily long zero-rank vectors. Enumerate all vectors of
length <=L and entries <=k, then triples a,b,d<=k. TelescopeBetaSignature adds
exactly (sum j=0..L (k+1)^j)*(k+1)^3 genuinely polymorphic fields over the
unchanged finite local-beta signature. Original wf/normality, exact lookup,
actual closed normal identity values, TypedSub and closed package/run are
proved, with declaration formation rank <=k+3. This numerical upper bound
does not assert a cumulative typing rule or a sufficient translated-source
budget. Descriptor coverage is not full source quotation coverage.

Retain the explicit one-binder ContextualBetaFamily/Signature specialization
and its local input-syntax/conversion injectivity. RealizedSignature separately
packages independently supplied closed typed implementations, without
assuming the desired source quoter. The global context/type/term translation,
source-substitution/conversion coherence and strong full-PTS quotation remain
open; existing raw-HOAS/STLC fidelity is unchanged.

## 2026-10-21 — predicative graph evidence and restricted binder congruence

Keep equality predicate levels explicit. IndexedEqualityLevels lowers/reverses
Eq_(max(a+2,d+1)) on A:U_a to Eq_d using originally typed equality motives;
join lowers one forward witness and reverses the other. For type equality
on U_c, the carrier sort is ZERO, giving input c+2 and output c+1. These
constructions are not cumulativity, arbitrary-level lowering or same-level
symmetry. Guarded normality must retain non-lambda evidence hypotheses.

Use synchronized graph equality for dependent application: quantify over
P : Pi x:A. B x -> U_d and relate P u y to P v z. Its original sort is
max(a+2,b+2,d+1), and dependent congruence needs input equality at the SAME
predicate level d. This does not establish equality with an independently
chosen transport. TarskiGraphBeta uses the actual finite beta field through
fixed-fiber congruence. The decoded-family beta reduction converts the
predicate application's type; no endpoint typing is extracted from Eq.
Actual identity filling recovers literal graph reflexivity, retaining the
substituted domain and lambda-valued fiber. Do not eta-contract that fiber
or assert normality of its graph certificate.

BinderCongruence deliberately uses a single common map and an equality
outside the binder. The map body may depend on both parameters, but its
binder domain/codomain are fixed with respect to the outer parameter.
Product-code congruence uses the actual constructor and keeps annotations.
This supplies a useful restricted case, not arbitrary lifting of pointwise
evidence to function equality; its administrative beta redexes are not hidden.

SourceSubstitution transforms supplied Type-valued derivations by structural
replacement and renaming, including annotations and exact result types.
Variable evidence is independently supplied derivation data. Its equivalence
with original TypedSub is propositional inhabitation, not Prop-to-Type
extraction. It constructs literal beta-contractum derivations without a new
wf restriction; arbitrary-step computational inversion/preservation and
target quotation-substitution coherence remain separate obligations.

For the next binder step, investigate the SPECIFIC cast-beta equation under
a full dependent telescope, rather than assuming arbitrary function
extensionality. Literal identity endpoints suggest reflexivity as a candidate
implementation. This is a proposal only: prove original formation, annotation
normality, contextual closure and sufficient telescope-length/rank-vector
budgets before advertising a finite interface. Rank alone has not been shown
to suffice. Full dependent quotation/recovery/fidelity remain open. No original
kernel, NormalizationComplexity or frozen ZFC source was changed; this
continuation performs no commit/push/index mutation.

## 2026-10-21 — executable source joins and finite internal beta fields

Keep source evidence separate from target quotation. FullSource gives
Type-valued data for EXACT original steps, forward reductions, unrestricted
conversion zigzags and all six typing rules. Its inhabitation iff original
relations is propositional, including typing in arbitrary original contexts;
do not extract data from opaque Prop proofs. Literal/rule ceilings are
computable but do not yet bound every inferred semantic rank or establish
an adequate target palette.

Do not attempt to translate arbitrary untyped zigzag intermediates.
FullConversion computes structural forward traces for the existing greedy
normalizer and compares annotated endpoints. Success is always sound;
normality/completeness and every-stage original typing use original wf and
typed endpoints. CanonicalSource traverses SUPPLIED derivation data, replacing
conversion fields by computed forward joins without changing literal source
indices or annotations. Its failure branch uses original validity only to
derive False, never to select computational ranks from Prop. Certification
is an output theorem, not a strengthened source-domain premise. Every original
typing in a well-formed context has certified canonical data. This still does
not generate internal equality evidence or a target quotation.

ScopedTarski lifts smart Abs/App, dependent binders, sort quotation and
code/term views to arbitrary independently typed signature embeddings. For
concrete spines, extend_code constructs the child context/environment and
lifted identity fill; nested_binder_typed uses precisely this child. Original
typing, normality, exact renaming/weakening and local fidelity are retained.
Literal substituted-annotation recovery and a separate decoder-contraction
corollary remain distinct. These interfaces now compose at arbitrary depth,
but represented domain/family/body inputs are still independently supplied.

Add finite beta-law ARGUMENTS, not a new conversion rule. TarskiBeta's
four-argument field states Eq_d(El_b(Bu),App_e(Abs_e f,u),fu) with the actual
old casts. Its formation rank is max(c+1,max(b+2,d+1)), c=max(a+1,b).
Construct the closed normal identity witness independently and prove typing
at the literal specialized field type and four-application reflexivity
recovery. The old product law alone is not claimed to produce this evidence.
TarskiBetaSignature adds (k+1)^3 declarations to the unchanged TS signature;
wf/normal context, bounded lookups and actual TypedSub are constructed.
Its inherited environment admits scoped smart typing/normality. Its own
fill equations do not automatically instantiate concrete-spine recovery.

Next prove INTERNAL reduction/substitution coherence under dependent binders,
not merely local beta at applications. Pointwise family evidence is not
function equality; neutral casts still do not beta-cancel, and there is no
eta or cumulativity. Preserve existing raw-HOAS/STLC syntax injectivity and
prove a separate full translated-source fidelity theorem when the translation
exists. No original kernel, normalization or frozen ZFC source was changed.
No commit/push/index mutation is part of this continuation.

## 2026-10-20 — smart dependent binders and an explicit cast boundary

Keep universe codes and represented terms distinct. The finite universe law
points from El0(u_r) to C_r; code-to-term uses its backward cast and term-to-code
its forward cast. In particular, representing the original U_r:U0 uses law ZERO
on u_r:C0. TarskiSorts proves actual normal closed sort quotations, direct
identity-application typing and literal recovery, uniformly over bounded labels.

Carry the finite signature through independent original dependent extensions
using a typed variable renaming. TarskiContext's concrete spine computes both
the instantiated context and the actual identity substitution, lifted at every
binder to retain fresh variables. It derives wf and TypedSub; neither is a
target premise. Generic operations accept arbitrary terms in the new scope,
not just renamed signature-scope inputs. Abstract declaration normality is
separate, and identity specialization need not preserve context normality.

Repair the local annotation problem by smart application to the fresh variable:
bound_apply(lambda D.b)=b, otherwise bound_apply(B)=(shift B) var0. This is
actual beta contraction, not eta or annotation erasure. TarskiBinders proves
normality, exact renaming and ONE-WAY substitution reduction. Do not assert
literal substitution naturality: replacement may turn a variable into a lambda.
The smart decoded product reuses the same actual finite law field by original
conversion. Abs/App typing and normality no longer require a separately normal
decoded annotation. Identity recovery eliminates the whole cast, so it does
not depend on the false literal smart-substitution law.

The concrete lambda-family binder takes independently typed family/body inputs
in the original extended context. Its local typing, full normality and recovery
are checked. The recovery endpoint retains the literal substituted decoded
domain annotation. Fixed-index local input/conversion injectivity follows
because the full family remains in the neutral law application. Do not extend
this to an unconstructed full source-derivation quoter.

TarskiRoundtrip proves a precise boundary for every external c: in an actual
wf context S,T:Uc,e:Eq_(c+1)(Uc,S,T),x:S, the neutral cast roundtrip and x
are typed, normal, distinct and nonconvertible. Adding K:S->U0 gives the same
failure at actual dependent type indices. Reflexivity-specialized roundtrips
still recover x. This refutes silent beta-cancellation of these casts, NOT
all object equality witnesses or full dependent PHOAS. A future finite beta-law
extension must independently construct its identity witnesses and still solve
binder/family congruence; merely raising predicate ranks does not add cumulativity.

The four modules pass the fresh 646-report aggregate, recursive kernel/pristine
checks and all 226 full local CI stages. Continue with generated source conversion
and substitution coherence; the smart local binder resolves one normality gap,
not the full derivation-directed translation. Preserve existing raw-HOAS and
STLC source-syntax injectivity. Keep this continuation uncommitted absent a new
publication request; no index, commit, remote or unrelated development was changed.

## 2026-10-20 — finite dependent signature with actual typed identity fill

Assemble six finite original context layers: carriers, decoders, universe
codes, universe laws, product constructors, product-law families. Each
layer's signatures live at a fixed EARLIER base scope; generic block/fill
helpers perform explicit weakening and typed instantiation. This avoids
postulating an algebra record or infinitely many fields. Use r<=k+1 for
carriers and a,b<=k for product pairs; c=max(a+1,b)<=k+1 then suffices.
Do not require closure under products for every available carrier rank.
Row-major pair enumeration gives exact width 4(k+2)+2(k+1)^2. Keep an
independent sufficient literal ceiling for intended source universes.

One law family Pi A:Ca.Pi B:(El_a A->Cb).product_law A B covers all
represented families for that rank pair. Its sort is c+2, absorbed after
the two binders. Construct its actual closed normal identity inhabitant
as lambda A:Ua.lambda B:A->Ub.reflexivity at Pi x:A.Bx, using proved
original conversion to the abstract-signature instance. Prove fill_typed
by actual field inhabitants, not a premise that the desired substitution
exists. This is now checked, including all inherited universe fields.

Applied operations obtain evidence from their finite law field rather than
a new law premise at each use. Actual identity substitution beta-recovers
literal replaced inputs and preserves existing redexes. For normality,
retain the NORMAL DECODED ANNOTATION premise: normal B alone need not make
B x normal. Generic telescope close/run preserves typing/normality/syntax
and provides administrative computation, not a quotation for every source.

IndexedCoherence supplies homogeneous composition and ordinary NONDEPENDENT
map congruence without raising predicate rank. Reflexivity equations are
literal beta reductions; arbitrary-evidence identities hold after motive
and argument application, not eta contraction. Do not mistake these laws
for dependent function extensionality or generated source-conversion
coherence. The latter, particularly under binders, is the next construction.

The five new modules pass a fresh 527-report aggregate and full 226-stage
CI, with unchanged upstream inventory/core/ZFC and no unsafe checks. Keep
this continuation and the preceding local Tarski milestone uncommitted
unless publication is requested; no new Git mutation is authorized here.

## 2026-10-20 — actual Tarski identity laws and closed transport programs

The proposed local route is now implemented, not assumed. Keep semantic code
carriers C_a:U0 and El_a:C_a->U_a separate from faithful homogeneous HOAS
syntax. The product interface Pi A:C_a.(El_a A->C_b)->C_c has rank a+2;
the decoded dependent product has rank c=max(a+1,b). Use an actual Leibniz
law Eq_(c+1)(U_c,X,Y):U_(c+2). Both arrow motives X->T and T->X have the
required rank, and id_X constructs forward/backward casts directly. Close
these into normal original PTS programs with type sort c+3. Never infer
application typing by subject expansion.

Construct the identity law itself as reflexivity at the common product
reduct, using proved original beta conversion. The identity constructor and
universe witnesses are originally typed normal terms at every external rank.
Specialized Abs/App return the LITERAL f/f u; this avoids an eta-expanded
result without introducing eta conversion. Generic laws remain explicitly
typed inputs; their independent identity realization is not a global
quotation-coherence assumption. No semantic payload or assumed normalizer
is smuggled into these operations.

Retain the precise limitation: local normality of neutral casts assumes
normal annotations and does not normalize every represented dependent
family. Arbitrary proof-headed casts do not definitionally cancel. The
checked EtaBoundary shows pointwise beta agreement need not give beta
conversion even at dependent indices in a valid context; it is not a
general nonexistence result for internal equality witnesses or PHOAS.
Next assemble a finite palette and derive actual coherence from source
derivations, preserving separate raw syntax injectivity. The local milestone
is verified with 418 closed reports and full 226-stage CI, not a completed
full-dependent evaluator. Its seven sources are frozen during the audit.

The pending ordinary publication completed at e822cd6 before proof edits
resumed; local and origin/main agree. Keep this subsequent continuation
uncommitted unless publication is separately requested. Preserve all
unrelated existing changes and historical evidence.

## 2026-10-20 — next PHOAS direction: Tarski codes and explicit transport

Following canonical publication, investigate finite rank-indexed code carriers
C_a:U0, El_a:C_a->U_a, universe codes and dependent product codes. Supply
actual object-language Leibniz transport laws, with closed identity-specialized
inhabitants, rather than assuming definitional equations for arbitrary abstract
families. Product constructor type has rank a+2; its decoded product rank is
c=max(a+1,b). A product equality at predicate level c+1 supports both cast
directions using arrow motives and id, with law-type rank c+2.

Predicative same-level Leibniz symmetry is not silently available. Likewise,
pointwise propositional equality of family outputs is not host-function
equality, and generic casts do not definitionally cancel. These are remaining
global coherence questions, not local operation impossibility. No eta,
extensionality axiom, semantic-payload projection or assumed quotation theorem
may be introduced to solve them. Implement the actual local terms and identity
beta laws first. Source implementation waits for the user's requested push;
at this checkpoint it is blocked in macOS Keychain, with no new proof edits.

## 2026-10-20 — full-PTS canonical contexts and hereditary type indices

Use full-PTS normalization constructively to separate faithful syntax from
conversion-canonical type codes. Extend the automatic bound to open contexts
by scanning maximum declaration literal labels and node counts. The resulting
normalizer consumes syntax only; original wf/typing prove correctness rather
than being strengthened with a promised normalization result. Instantiate the
existing normalization-stage cost account without inventing scan/code costs.

Use HEREDITARY substitution: normalize after replacing variables. Ordinary
substitution of normal entries into a normal source type can create a redex;
the concrete f U0 / f:=lambda X:U0.X regression is checked. Prove normalized
entries remain actual original TypedSub, converting their dependent lookup
types as well. Derive identity/composition and normalized term/result-type
typing using original validity's exact sort, never cumulativity.

Normalize original context declarations while retaining literal term/type
syntax in the typing-transport theorem. Construct original wf and identity
TypedSub in both directions from the Type-valued original wf witness, rather
than extracting computational ranks from Prop. Prove normal declarations,
idempotence and actual original context/index reductions.

CanonicalTypeIndex produces closed homogeneous HOAS C(nf A), not a source type
or an internal El operation. Its equality is scoped-syntax beta conversion,
not denotational equality across arbitrary environments. Keep faithful C(t)
separate: concrete convertible types have distinct C and identical J, and C
need not be convertible to J. This evades the limited shared-map obstruction
but does not provide an object dependent interpreter by itself. The remaining
step is actual typed reification and represented-family construction/coherence
inside PTS. Do not claim full strong PHOAS from metalevel canonicalization.

Publish the prior snapshot and requested finished-doc merge in an isolated
checkout, excluding unrelated BZC sources/logs. Real merge 64864e3 and verified
publication b6c81d1 are pushed to main. Preserve the dirty original worktree
byte-for-byte when synchronizing branch/index; do not stash/reset its files.
Keep the new canonical continuation uncommitted unless separately requested.

## 2026-10-20 — finite indexed PHOAS and explicit dependent coherence boundary

Close the independent STLC prequotation over a finite actual original PTS
telescope. Use one ground variable, families F_0 through F_(k+1), and Abs/App
handlers for all a,b <= k. The extra family is needed for the unused boundary
pairs whose arrow rank is k+1. Polymorphic handlers cover infinitely many
source type shapes without an infinite context. Define an executable quote
from independent Type-valued derivations and prove coverage from the separate
source relation. Do not replace original typing by that relation.

Realize the finite identity substitution by an actual closed PTS decoder,
with its ground-type abstraction inside its body. Prove direct typing of
all sequential applications from original typed substitutions, not by subject
expansion. Strong recovery returns the unreduced source, including annotations;
no normalized semantic payload is attached. Retain normality and syntax-level
injectivity of the code separately, including comparison by beta conversion.
The decoder indices are k AND the full external simple type A. State this
explicitly rather than calling it rank-only. Code/decoder sort existence is
checked, but do not advertise an unproved exact numeric sort formula.

Construct genuinely dependent local handlers independently. Their codomain
family is B:F_a(A)->U_b, not an untranslated B_0:A->U_b. Original typing and
identity recovery of these operations do not solve recursive translation of
that family. Under the candidate literal-sort convention, bind a separate
El_b:F_0(U_b)->U_b; prove its formation and identity instance, but never assume
the abstract operation has the definitional conversion laws a quoter needs.

Record a precise, limited no-go theorem: a normal syntax-injective map cannot
also preserve source beta conversion on a domain containing the two explicit
small convertible types. A second conversion-preserving index map does not
help if it is required to agree pointwise up to beta with the syntax code.
This is NOT an impossibility theorem for arbitrary dependent indexed PHOAS.
Distinct semantic indices and faithful syntax codes remain a live direction.
Do not conflate Church-style algebra-parametric object syntax with a native
Rocq PHOAS datatype or assume parametricity/no-junk for arbitrary inhabitants.

Keep all changes in the separate SelfInterpreter library and exposition.
Original PTS rules, normalization infrastructure, arithmetic/set models and
CI stages need no change. Complete the finite STLC result and report the
remaining full-dependent obligation honestly; preserve the separate full-PTS
weak semantic-payload construction without presenting it as pure evaluation.

## 2026-10-20 — complexity route and full-PTS weak interpretation

Make the user's positive complexity argument the introduction of the
self-interpreter note. The checked fixed-redex-bound normalizer is elementary
for each external budget and covers all original typed syntax; the automatic
closed bound includes literal labels and node count. The manuscript's
non-uniform elementary representability theorem is not yet a checked Rocq
compiler. State numeric self-reduction conditionally on that theorem and
elementary serialization, without adding an axiom. Its rank cost comes from
an explicit elementary program, not merely extensional classification. Record
the manuscript modulus callback correction r f x (not r X f x); do not
silently certify the rest of the displayed informal construction.

Implement full-PTS normalization-to-HOAS externally first. Canonical codes
identify beta conversion, not literal source syntax; preserve the raw-HOAS
quoter and its exact fidelity independently. Normalization-stage cost and
HOAS output-size bounds are different measures, not a complete serialization
runtime. A native syntax transformation is not an object-language program.

Prove the independent literal-generation obstruction: raw quote r t has
maximum literal r, beta cannot manufacture larger sort labels, and all U_k
are normal of redex bound/type rank zero. Thus those two indices alone
cannot support unquotation of current raw codes. A source literal ceiling,
the conservative bound containing it, or literal-bearing semantic arguments
are outside the obstruction; their sufficiency is not thereby proved.

Construct a full closed WEAK interpretation by pairing nf(t) with the
faithful raw HOAS tag in a normal Church-style packet, at normalized type
nf(A). The actual indexed closed decoder projects the payload in five beta
steps. Original validity supplies the exact A:U_s; no cumulativity or
elimination of an erased Prop witness into a computable rank is asserted.
Normalizing the type is essential to full annotation normality. Retain
syntax-level injectivity by the original tag, even across differing supplied
source types; do not claim fidelity of those supplied types/derivations.

This endpoint covers every closed original dependent typing derivation but
does NOT evaluate the HOAS tag and recovers only nf(t), convertible to t.
Describe it as normalization-assisted weak semantic-payload interpretation,
not Brown--Palsberg strong unquotation or pure HOAS evaluation. Internal
elementary compilation, typed adapters and dependent reification remain
open, as does the separate finite closed source-indexed PHOAS package.
No core PTS rule, arithmetic/set development or CI stage changes are needed.

## 2026-10-20 — expositions for completed development groups

Provide one native LaTeX–Markdown exposition per finished AI-assisted
development group, including shared arithmetic infrastructure. Retain useful
Markdown navigation READMEs and link source/PDF. The handwritten kernel and
ongoing BZC/self-interpreter research are not newly finished work. Preserve
the entire frozen PR #1 ZFC_model directory: its new exposition lives at
docs/developments/ZFC_model. No Rocq proof sources or rules are changed.

Use a shared minimal development preamble and the existing Markdown runtime.
Build all five documents in fresh temporary directories, validate every log,
and publish PDFs only after all pass. Compilation cannot detect every
malformed math fence: inspect PDF text and representative pages too.
Describe actual public statements and explicit premise boundaries, especially
effective witness search, supplied-model soundness and external STLC hardness.

Cleanup removes only disposable bytecode, solver cache and parser sidecars,
with an ignored local recovery copy and ignore rules for regeneration.
Preserve tests, historical proof evidence, provenance archives and unrelated
user work. New bulky raw logs stay under _build; a concise tracked command
report and hashes provide continuity. Record the concurrent excluded
self-interpreter CI failure separately from successful finished-library audits.

## 2026-10-16 — dated title, optional author lines and float-local math layout

Keep authorsonlines opt-in and default false. Apply protected line-break
separators to structured authblk metadata before emitting authors, retaining
email/ORCID/affiliation association. Explicit YAML dates use the existing
metadata mechanism after the entire author block. Test class defaults as
well as true/false, scalar authors and empty dates; restore internal catcodes
after external preambles and protect moving email URLs.

Within figures only, typeset mathpar using its public line-spacing/binding
macros inside a vbox, without the display wrapper. Keep normal external float
and caption skips; do not tighten every display or use arbitrary negative
vspace. The isolated actual-preamble regression measures 21pt less padding.
Expand Unicode source aliases without font/semantic changes; retain all TeX
macros needed for formatting, binding and scalable delimiters. Commit the
pinned runtime with its local changes/provenance, not a dependency on MLTT-S.


## 2026-10-14 — consolidate physical source layout, preserve logical interfaces

Move Interpretation_of_R and ZFC_model into theories as explicitly requested;
do not use the superseded models destination. Preserve every .v source and
all Rocq library names, so downstream imports and theorem types are unchanged.
The original kernel keeps its existing explicitly enumerated Dune theory.

Update current build scripts, CI descriptions, navigation, and guidance.
Keep raw historical logs/packages unchanged rather than rewriting their
recorded commands to imply newer verification. Root and folder READMEs
separate checked public results from material-foundation and external-hardness
obligations. Replace the obsolete arithmetic-only AGENTS scope with current
repo-wide proof integrity, verification, and durable-handoff instructions.
Keep existing CI coverage, timeouts, failure propagation, and pristine baseline.

Verification completed: fresh full build, both original public interpretation
interfaces, model/normalization endpoints, recursive kernel checks, all audit
aliases, and complete 171-stage local CI passed. Record the initial rejected
audit output-basename command as well as its corrected successful invocation.
This is a source-layout change, not a new theorem or a weaker-foundation proof.

## 2026-10-14 — scope the BZC/GCH foundation claim precisely

Audit the actual no-intermediate-cardinal (injection-gap) GCH principle;
do not add initial-ordinal representatives or successor-cardinal existence
silently. A relative V_(omega+omega) countermodel shows that this BZC + GCH
does not itself supply the collected envelope of the current construction.
Existence of the full hierarchy is a sufficient source of the required
rank bounds; its minimality among possible extra axioms is not established.

Global decoder/selector data may live in fixed finite powersets above H;
the set-sized model does not require them to be members of H. This uses
only the ordinary finite set operations once H is available.

Keep the BZC derivability claim OPEN: denotation_family_choice and
paired_relation_choice still use arbitrary-predicate separation. A proposed
bounded material encoding uses a least closed relation over a fixed set J,
quantifying over Power J, but its rule formula and agreement with original
typed denotation must be proved before claiming the full foundation reduction.
The complete audit and exact source references are in ZFC_model/BZC_AUDIT.md.

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
