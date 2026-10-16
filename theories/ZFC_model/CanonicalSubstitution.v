(** A genuine base case of semantic hereditary substitution. Normal,
    non-lambda substitution images cannot create a beta redex in a normal
    implicit type witness. Thus the SAME canonical denotation survives raw
    substitution, without a semantic-conversion premise. In original PTS-rk,
    normal arguments whose type has rank zero satisfy this condition.
    Higher-rank lambda arguments still require semantic normalization. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  Inversions Preservation.
From PTSrkModel Require Import SyntaxSubstitution Denotation
  CanonicalTypeWitnesses CanonicalDenotation CanonicalRenaming.

Definition normal_nonlambda_substitution {n m} (sigma : Fin n -> Term nat m) :=
  forall i, beta_normal (sigma i) /\ not_lambda (sigma i).

Lemma normal_nonlambda_transpose {n m} (sigma : Fin n -> Term nat m) :
  normal_nonlambda_substitution sigma ->
  normal_nonlambda_substitution (transpose sigma).
Proof.
  intros HS i; dependent elimination i as [fzero | fsucc j]; cbn [transpose fin_match].
  - split; [intros v R; inversion R | intros A b E; discriminate].
  - destruct (HS j) as [HN HL]. unfold shift; split.
    + apply beta_normal_rename; exact HN.
    + apply not_lambda_rename; exact HL.
Qed.

Lemma not_lambda_replace n (t : Term nat n) : not_lambda t ->
  forall m (sigma : Fin n -> Term nat m),
    (forall i, not_lambda (sigma i)) -> not_lambda (replace sigma t).
Proof.
  intros H m sigma HS A b E; destruct t; cbn [replace] in E; try discriminate.
  - eapply HS; exact E.
  - eapply H; reflexivity.
Qed.

Theorem beta_normal_replace_nonlambda n (t : Term nat n) :
  beta_normal t -> forall m (sigma : Fin n -> Term nat m),
    normal_nonlambda_substitution sigma -> beta_normal (replace sigma t).
Proof.
  induction t as [n i | n A IHA B IHB | n i | n A IHA t IHt | n t IHt u IHu];
    intros HN m sigma HS; cbn [replace].
  - intros v R; inversion R.
  - destruct (proj1 (beta_normal_product A B) HN) as [HA HB].
    apply beta_normal_product; split.
    + apply IHA; assumption.
    + apply IHB; [exact HB | apply normal_nonlambda_transpose; exact HS].
  - exact (proj1 (HS i)).
  - apply beta_normal_lambda.
    + apply IHA; [| exact HS]. intros A' R; eapply HN; apply step_lam_left; exact R.
    + apply IHt; [| apply normal_nonlambda_transpose; exact HS].
      intros t' R; eapply HN; apply step_lam_right; exact R.
  - destruct (proj1 (beta_normal_application t u) HN) as [Ht [Hu HL]].
    apply beta_normal_application; split; [apply IHt; assumption |].
    split; [apply IHu; assumption |]. apply not_lambda_replace; [exact HL |].
    intro i; exact (proj2 (HS i)).
Qed.

Lemma rank_zero_argument_not_lambda n (G : Ctx nat n) u A :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 0) ->
  @typ nat RankSorts n G u A -> not_lambda u.
Proof.
  intros HG TA Tu D t E; subst u.
  destruct (λ_inversion RankSorts D A t Tu) as [m [B [TD [Tt ET]]]].
  assert (HGD : @wf nat RankSorts (S n) (G & D)) by (eapply wf_cons; eassumption).
  destruct (type_is_correct t B Tt HGD) as [k TB].
  assert (TP : @typ nat RankSorts n G (Π D B) (𝓤 (Nat.max (S m) k))).
  { eapply typ_Π; [exact TD | exact TB | reflexivity]. }
  assert (EU : (𝓤 0 : Term nat n) =ᵝ 𝓤 (Nat.max (S m) k)).
  { eapply type_stability; [exact TA | exact TP | exact HG | exact ET]. }
  apply equiv_𝓤_inversion in EU. pose proof (Nat.le_max_l (S m) k). lia.
Qed.

Module CanonicalSubstitution.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module CR := CanonicalRenaming.CanonicalRenaming.
Section Substitution.
Variables H s : Ens.

Definition denoting_substitution {n m} (D : Ctx nat m)
  (rho : Fin n -> Ens) (rho' : Fin m -> Ens) (sigma : Fin n -> Term nat m) :=
  forall i, CD.denotes H s m D rho' (sigma i) (rho i).

Lemma denoting_substitution_extend {n m} (D : Ctx nat m)
  (rho : Fin n -> Ens) rho' sigma A x :
  denoting_substitution D rho rho' sigma ->
  denoting_substitution (D & A) (fin_match x rho) (fin_match x rho') (transpose sigma).
Proof.
  intros HS i; dependent elimination i; cbn [transpose fin_match].
  - apply CD.denotes_var.
  - apply CR.denotes_shift, HS.
Qed.

Theorem denotes_replace n G rho t v : CD.denotes H s n G rho t v ->
  forall m D (sigma : Fin n -> Term nat m) rho',
    typed_substitution G D sigma -> normal_nonlambda_substitution sigma ->
    denoting_substitution D rho rho' sigma ->
    CD.denotes H s m D rho' (replace sigma t) v.
Proof.
  intro HD; induction HD; intros m D sigma rho' ET EN ES; cbn [replace].
  - apply CD.denotes_sort.
  - apply ES.
  - eapply CD.denotes_product; eauto using typed_substitution_extend,
      normal_nonlambda_transpose, denoting_substitution_extend.
  - eapply CD.denotes_lambda with (B := replace (transpose sigma) B).
    + eapply rank_typing_replace; eauto using typed_substitution_extend.
    + apply beta_normal_replace_nonlambda; [assumption | apply normal_nonlambda_transpose; exact EN].
    + eauto.
    + eauto using typed_substitution_extend, normal_nonlambda_transpose, denoting_substitution_extend.
    + eauto using typed_substitution_extend, normal_nonlambda_transpose, denoting_substitution_extend.
    + assumption.
    + assumption.
  - eapply CD.denotes_application with (A := replace sigma A) (B := replace (transpose sigma) B).
    + change (@typ nat RankSorts m D (replace sigma t) (replace sigma (Π A B))).
      eapply rank_typing_replace; eauto.
    + change (beta_normal (replace sigma (Π A B))).
      apply beta_normal_replace_nonlambda; assumption.
    + eauto.
    + eauto using typed_substitution_extend, normal_nonlambda_transpose, denoting_substitution_extend.
    + assumption.
    + eauto.
    + eauto.
  - eapply CD.denotes_equal; eauto.
Qed.

Corollary denotes_subst_nonlambda n G rho A t u v x :
  @typ nat RankSorts n G u A -> beta_normal u -> not_lambda u ->
  CD.denotes H s (S n) (G & A) (fin_match x rho) t v ->
  CD.denotes H s n G rho u x -> CD.denotes H s n G rho (t ◁ u) v.
Proof.
  intros Tu HN HL Dt Du. unfold subst. eapply denotes_replace; [exact Dt | | |].
  - apply typed_single_substitution; exact Tu.
  - intro i; dependent elimination i; cbn [fin_match].
    + split; assumption.
    + split; [intros z R; inversion R | intros B b E; discriminate].
  - intro i; dependent elimination i; cbn [fin_match]; [exact Du | apply CD.denotes_var].
Qed.

Theorem denotes_rank_zero_substitution n (G : Ctx nat n) rho A t u v x :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 0) ->
  @typ nat RankSorts n G u A -> beta_normal u ->
  CD.denotes H s (S n) (G & A) (fin_match x rho) t v ->
  CD.denotes H s n G rho u x -> CD.denotes H s n G rho (t ◁ u) v.
Proof.
  intros HG TA Tu HN Dt Du. eapply denotes_subst_nonlambda; try eassumption.
  eapply rank_zero_argument_not_lambda; eassumption.
Qed.
End Substitution.
End CanonicalSubstitution.

Print Assumptions normal_nonlambda_transpose.
Print Assumptions not_lambda_replace.
Print Assumptions beta_normal_replace_nonlambda.
Print Assumptions rank_zero_argument_not_lambda.
Print Assumptions CanonicalSubstitution.denotes_replace.
Print Assumptions CanonicalSubstitution.denotes_subst_nonlambda.
Print Assumptions CanonicalSubstitution.denotes_rank_zero_substitution.
Check CanonicalSubstitution.denotes_rank_zero_substitution.
