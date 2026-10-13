# Decisions and proof-engineering history

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
