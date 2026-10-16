(** Normalized witnesses for ORIGINAL typing. No semantic assumption,
    changed typing rule, or added normalization axiom is used. *)
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction SN
  AbstractRewriting DefEq Inversions Preservation.

Definition beta_normal {n} (t : Term nat n) := forall u, ~ (t →ᵝ u).

Lemma normal_reductions_equal {n} (t u : Term nat n) :
  beta_normal t -> t ↠ᵝ u -> t = u.
Proof.
  intros HN HR. destruct HR; [reflexivity |].
  exfalso; eapply HN; eassumption.
Qed.

Lemma normal_convertible_equal {n} (A B : Term nat n) :
  beta_normal A -> beta_normal B -> A =ᵝ B -> A = B.
Proof.
  intros HA HB E. apply def_equiv_prop in E as [N [RA RB]].
  pose proof (normal_reductions_equal A N HA RA).
  pose proof (normal_reductions_equal B N HB RB). congruence.
Qed.

Theorem normal_types_unique {n} (G : Ctx nat n) t A B :
  @typ nat RankSorts n G t A -> @typ nat RankSorts n G t B ->
  beta_normal A -> beta_normal B -> A = B.
Proof.
  intros TA TB HA HB. apply normal_convertible_equal; [exact HA | exact HB |].
  eapply uniqueness_of_typing; eassumption.
Qed.

Print Assumptions normal_reductions_equal.
Print Assumptions normal_convertible_equal.
Print Assumptions normal_types_unique.

Lemma beta_normal_product {n} (A : Term nat n) B :
  beta_normal (Π A B) <-> beta_normal A /\ beta_normal B.
Proof.
  split.
  - intro H; split; intros u HU; eapply H; constructor; exact HU.
  - intros [HA HB] u HU; inversion HU; subst;
      first [eapply HA; eassumption | eapply HB; eassumption].
Qed.

Lemma beta_normal_lambda {n} (A : Term nat n) t :
  beta_normal A -> beta_normal t -> beta_normal (lam A t).
Proof.
  intros HA Ht u HU; inversion HU; subst;
    first [eapply HA; eassumption | eapply Ht; eassumption].
Qed.

(** Constructive one-step decision suffices to extract a normal form from
    the upstream accessibility proof. No excluded-middle premise is used. *)
Lemma beta_normal_or_step {n} (t : Term nat n) :
  beta_normal t \/ exists u, t →ᵝ u.
Proof.
  induction t as [n i | n A IHA B IHB | n i | n A IHA t IHt | n t IHt u IHu].
  - left; intros u H; inversion H.
  - destruct IHA as [HA | [A' RA]].
    + destruct IHB as [HB | [B' RB]].
      * left; apply beta_normal_product; auto.
      * right; exists (Π A B'); constructor; exact RB.
    + right; exists (Π A' B); constructor; exact RA.
  - left; intros u H; inversion H.
  - destruct IHA as [HA | [A' RA]].
    + destruct IHt as [Ht | [t' Rt]].
      * left; apply beta_normal_lambda; assumption.
      * right; exists (lam A t'); constructor; exact Rt.
    + right; exists (lam A' t); constructor; exact RA.
  - destruct IHt as [Ht | [t' Rt]].
    + destruct IHu as [Hu | [u' Ru]].
      * destruct t.
        -- left; intros v Hv; inversion Hv; subst;
             first [eapply Ht; eassumption | eapply Hu; eassumption].
        -- left; intros v Hv; inversion Hv; subst;
             first [eapply Ht; eassumption | eapply Hu; eassumption].
        -- left; intros v Hv; inversion Hv; subst;
             first [eapply Ht; eassumption | eapply Hu; eassumption].
        -- right; eexists; apply step_beta.
        -- left; intros v Hv; inversion Hv; subst;
             first [eapply Ht; eassumption | eapply Hu; eassumption].
      * right; exists (app t u'); constructor; exact Ru.
    + right; exists (app t' u); constructor; exact Rt.
Qed.

Lemma accessible_normal_form {n} (t : Term nat n) : sn t ->
  exists N, t ↠ᵝ N /\ beta_normal N.
Proof.
  intro H; induction H as [t HA IH].
  destruct (beta_normal_or_step t) as [HN | [u RU]].
  - exists t; split; [reflexivity | exact HN].
  - destruct (IH u RU) as [N [RN HN]]. exists N; split; [| exact HN].
    eapply rtc_step; eassumption.
Qed.

Theorem typed_normal_form {n} (G : Ctx nat n) t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  exists N, t ↠ᵝ N /\ beta_normal N /\ @typ nat RankSorts n G N T.
Proof.
  intros HG HT.
  destruct (accessible_normal_form t (strong_normalization G t T HG HT)) as [N [RN HN]].
  exists N; split; [exact RN |]. split; [exact HN |].
  eapply subject_reduction'; eassumption.
Qed.

Theorem normal_type_witness {n} (G : Ctx nat n) t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  exists N, beta_normal N /\ @typ nat RankSorts n G t N /\ T ↠ᵝ N.
Proof.
  intros HG HT. destruct (type_is_correct t T HT HG) as [k TK].
  destruct (typed_normal_form G T (𝓤 k) HG TK) as [N [RN [HN TN]]].
  exists N; split; [exact HN |]. split; [| exact RN].
  eapply typ_conv; [exact HT | exact TN |].
  apply def_equiv_prop. exists N; split; [exact RN | reflexivity].
Qed.

Theorem normal_lambda_witness {n} (G : Ctx nat n) A t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G (lam A t) T ->
  exists B, beta_normal B /\ @typ nat RankSorts (S n) (G & A) t B.
Proof.
  intros HG HT. destruct (λ_inversion RankSorts A T t HT) as [m [B [TA [TB E]]]].
  assert (HGA : @wf nat RankSorts (S n) (G & A)) by (eapply wf_cons; eassumption).
  destruct (normal_type_witness (G & A) t B HGA TB) as [N [HN [TN RN]]].
  exists N; auto.
Qed.

Theorem normal_application_witness {n} (G : Ctx nat n) t u T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G (app t u) T ->
  exists A B, beta_normal A /\ beta_normal B /\
    @typ nat RankSorts n G t (Π A B) /\ @typ nat RankSorts n G u A /\
    T =ᵝ B ◁ u.
Proof.
  intros HG HT. destruct (app_inversion RankSorts t u T HT) as [A [B [Tt [Tu ET]]]].
  destruct (type_is_correct t (Π A B) Tt HG) as [k TP].
  destruct (typed_normal_form G (Π A B) (𝓤 k) HG TP) as [N [RN [HN TN]]].
  destruct (rtc_Π_repr A N B RN) as [A' [B' EN]]; subst N.
  destruct (proj1 (beta_normal_product A' B') HN) as [HA HB].
  destruct (rtc_Π_inversion A A' B B' RN) as [RA RB].
  destruct (Π_inversion RankSorts A' (𝓤 k) B' TN) as [m [q [l [R [TA [TB E]]]]]].
  exists A', B'; split; [exact HA |]. split; [exact HB |]. split.
  - eapply typ_conv; [exact Tt | exact TN |].
    apply def_equiv_prop. exists (Π A' B'); split; [exact RN | reflexivity].
  - split.
    + eapply typ_conv; [exact Tu | exact TA |].
      apply def_equiv_prop. exists A'; split; [exact RA | reflexivity].
    + etransitivity; [exact ET |]. apply def_equiv_prop. exists (B' ◁ u); split; [| reflexivity].
      unfold subst; apply replace_rtc; exact RB.
Qed.

Print Assumptions beta_normal_product.
Print Assumptions beta_normal_or_step.
Print Assumptions accessible_normal_form.
Print Assumptions typed_normal_form.
Print Assumptions normal_type_witness.
Print Assumptions normal_lambda_witness.
Print Assumptions normal_application_witness.
Check normal_lambda_witness.
Check normal_application_witness.
