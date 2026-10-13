# Live proof-development state — 2026-10-13

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
