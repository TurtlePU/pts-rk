# Decisions and proof-engineering history

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
