# Live proof-development state — 2026-10-14

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
