(** The canonical application rule for a normal inferred product and a
    normal, non-lambda argument. Canonical coherence transports membership
    without a semantic-conversion assumption. The argument restriction is
    precisely the proved substitution base case, not an unrestricted
    soundness theorem. The non-lambda condition follows for typed rank-zero
    arguments; their normality remains an explicit premise.

    All source annotations, set operations, and original typing premises
    are retained. Ordinary family choice assembles the codomain witnesses;
    this alone does not certify bounded first-order definability. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Preservation.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations CanonicalTypeWitnesses
  CanonicalDenotation CanonicalRenaming CanonicalRealization CanonicalSubstitution.
Import CodeUniverses.CodeUniverses.

Module CanonicalApplication.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module CR := CanonicalRealization.CanonicalRealization.
Module CS := CanonicalSubstitution.CanonicalSubstitution.

Section Application.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

Theorem application_realization_from_witnesses
  n (G : Ctx nat n) rho A B t u a b f x m k :
  @typ nat RankSorts n G t (Π A B) -> @typ nat RankSorts n G u A ->
  beta_normal (Π A B) -> beta_normal u -> not_lambda u ->
  CD.denotes H s n G rho A a ->
  (forall y, IN y (decode a) ->
    CD.denotes H s (S n) (G & A) (fin_match y rho) B (b y)) ->
  family_extensional (fun y => decode (b y)) ->
  CD.denotes H s n G rho t f -> CD.denotes H s n G rho u x ->
  IN a (U m) -> (forall y, IN y (decode a) -> IN (b y) (U k)) ->
  IN f (decode (semantic_product H s a b)) -> IN x (decode a) ->
  CR.realizes H s G rho (app t u) (B ◁ u).
Proof.
  intros Tt Tu NP Nu Lu DA DB EB Dt Du Ha Hb Hf Hx.
  exists (semantic_application H s a b f x), (b x).
  split; [eapply CD.denotes_application; eassumption |]. split.
  - eapply CS.denotes_subst_nonlambda; [exact Tu | exact Nu | exact Lu | apply DB; exact Hx | exact Du].
  - exact (semantic_application_typed W H s HW HO HH classical_logic comparison gap choice HS
      m k a b f x Ha Hb Hf Hx).
Qed.

Theorem application_realization_from_induction
  n (G : Ctx nat n) rho A B t u m k :
  @typ nat RankSorts n G t (Π A B) -> @typ nat RankSorts n G u A ->
  beta_normal (Π A B) -> beta_normal u -> not_lambda u ->
  CR.valid_valuation H s G rho ->
  CR.realizes H s G rho t (Π A B) -> CR.realizes H s G rho u A ->
  CR.realizes H s G rho A (𝓤 m) ->
  (forall rho', CR.valid_valuation H s (G & A) rho' ->
    CR.realizes H s (G & A) rho' B (𝓤 k)) ->
  CR.realizes H s G rho (app t u) (B ◁ u).
Proof.
  intros Tt Tu NP Nu Lu HV RF RX RA RB.
  destruct (CR.realizes_sort_witness H s n G rho A m RA) as [a [Ha DA]].
  assert (HT : forall y, IN y (decode a) -> exists c, IN c (U k) /\
    CD.denotes H s (S n) (G & A) (fin_match y rho) B c).
  { intros y Hy. apply CR.realizes_sort_witness, RB.
    eapply CR.valid_valuation_extend; eassumption. }
  destruct (CR.denotation_family_choice H s choice n G rho A B (decode a) (U k) HT)
    as [b [Eb Hb]].
  assert (EB : family_extensional (fun y => decode (b y))).
  { intros y z E; apply decoding_extensional, Eb; exact E. }
  assert (DB : forall y, IN y (decode a) ->
    CD.denotes H s (S n) (G & A) (fin_match y rho) B (b y)).
  { intros y Hy; exact (proj2 (Hb y Hy)). }
  assert (DP : CD.denotes H s n G rho (Π A B) (semantic_product H s a b)).
  { eapply CD.denotes_product; eassumption. }
  destruct RF as [f [p [Dt [Dp Hfp]]]].
  destruct RX as [x [a' [Du [DA' Hxa']]]].
  assert (Hf : IN f (decode (semantic_product H s a b))).
  { apply (CR.realizes_membership H s n G rho t (Π A B) f
      (semantic_product H s a b)); [exists f, p; auto | exact Dt | exact DP]. }
  assert (Hx : IN x (decode a)).
  { apply (CR.realizes_membership H s n G rho u A x a);
      [exists x, a'; auto | exact Du | exact DA]. }
  eapply application_realization_from_witnesses; try eassumption.
  intros y Hy; exact (proj1 (Hb y Hy)).
Qed.

Corollary rank_zero_application_realization
  n (G : Ctx nat n) rho A B t u k :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 0) ->
  @typ nat RankSorts n G t (Π A B) -> @typ nat RankSorts n G u A ->
  beta_normal (Π A B) -> beta_normal u ->
  CR.valid_valuation H s G rho ->
  CR.realizes H s G rho t (Π A B) -> CR.realizes H s G rho u A ->
  CR.realizes H s G rho A (𝓤 0) ->
  (forall rho', CR.valid_valuation H s (G & A) rho' ->
    CR.realizes H s (G & A) rho' B (𝓤 k)) ->
  CR.realizes H s G rho (app t u) (B ◁ u).
Proof.
  intros HG TA Tt Tu NP Nu HV RF RX RA RB.
  eapply application_realization_from_induction; try eassumption.
  eapply rank_zero_argument_not_lambda; eassumption.
Qed.
End Application.
End CanonicalApplication.

Print Assumptions CanonicalApplication.application_realization_from_witnesses.
Print Assumptions CanonicalApplication.application_realization_from_induction.
Print Assumptions CanonicalApplication.rank_zero_application_realization.
Check CanonicalApplication.application_realization_from_induction.
Check CanonicalApplication.rank_zero_application_realization.
