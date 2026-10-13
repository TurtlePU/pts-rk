# Decisions and proof-engineering history

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
