From Stdlib Require PeanoNat.
Require Import Stdlib.Program.Equality.
Require Import Levels.
Require Import Typing.
Require Import Syntax.
Require Import Context.
Require Import SN.
Require Import Preservation.
Require Import Reduction.
Require Import Inversions.
Require Import DefEq.

Instance RankLevels : Levels_sig nat :=
  { axiom := fun x y => y = 0
  ; rule := fun x y z => z = max (S x) y
  }.

#[refine]
Instance RankLevels_fun :
  Levels_functional_sig nat := {}.
Proof. all: intros; rewrite H0; assumption. Qed.

#[refine]
Instance RankLevels_total : Levels_total_sig nat := {}.
Proof. all: intros; eexists; reflexivity. Qed.

Definition AL r := (* Application lemma *)
  forall n (Γ: Ctx nat n) f t T U,
  Γ ⊢ f ⇐ Π T U -> Γ ⊢ t ⇐ T -> Γ ⊢ Π T U ⇐ 𝓤 r ->
  wf Γ -> SN f -> SN t -> SN (f $ t).

Definition SL r := (* Substitution lemma *)
  forall m n (Γ: Ctx nat (S m + n)) t u T,
  shrink Γ ⊢ u ⇐ squeeze Γ ->
  shrink Γ ⊢ squeeze Γ ⇐ 𝓤 r -> Γ ⊢ t ⇐ T -> wf Γ ->
  SN t -> SN u -> SN (t ◁ᵢ u).

Lemma SL_to_AL:
  forall r, (forall j, j < r -> SL j) -> AL r.
Proof. unfold AL. intros. induction H4.
- constructor. constructor; auto.
- eapply SN_WHR. constructor; auto.
  apply Π_inversion in H2.
  destruct H2 as [ℓₜ [ℓᵤ [ℓ [HR [HT [HU HE]]]]]].
  change (ℓ = max (S ℓₜ) ℓᵤ) in HR.
  apply equiv_𝓤_inversion in HE. subst.
  apply λ_inversion in H0.
  destruct H0 as [ℓ₀ [U0 [HT0 [HF HE']]]].
  apply equiv_Π_inversion in HE'. destruct HE'.
  apply H with (m := 0) (j := ℓₜ) (Γ := Γ & T0)
               (T := U0); auto.
  + apply PeanoNat.Nat.le_max_l.
  + simpl. apply typ_conv with (T := T) (ℓ := ℓ₀); auto.
  + simpl. replace ℓₜ with ℓ₀. auto.
    symmetry. eapply equiv_𝓤_inversion.
    apply type_stability with (t := T) (t' := T0)
                              (Γ := Γ); auto.
  + apply wf_cons with (ℓ := ℓ₀); auto.
- eapply SN_WHR. constructor. apply H4.
  apply IHSN with (Γ := Γ) (T := T) (U := U); auto.
  apply subject_reduction with (t := t0); auto.
  apply reduction_weakening. auto.
Qed.

Lemma AL_to_SL: forall r, AL r -> SL r.
Proof. unfold SL. intros. dependent induction H2.
- constructor. constructor.
- constructor. constructor.
  + apply IHtyp1 with (Γ := Γ) (T := 𝓤 ℓₜ); auto.
    apply dom_SN with (U := U). auto.
  + change (SN (U ◁ᵢ u)).
    apply IHtyp2 with (Γ := Γ & T0) (T := 𝓤 ℓᵤ); auto.
    * apply wf_cons with (ℓ := ℓₜ); auto.
    * apply codom_SN with (T := T0). auto.
- destruct (subst_at_var i u); destruct H2.
  + rewrite H6. apply rename_SN. auto.
  + rewrite H2. constructor. constructor.
- apply SN_λ.
  + apply IHtyp1 with (Γ := Γ) (T := 𝓤 ℓ); auto.
    apply arg_SN with (t := t0). auto.
  + change (SN (t0 ◁ᵢ u)).
    apply IHtyp2 with (Γ := Γ & U) (T := T0); auto.
    * apply wf_cons with (ℓ := ℓ); auto.
    * apply body_SN with (T := U). auto.
- change (SN ((t0 ◁ᵢ u) $ (u0 ◁ᵢ u))).
  destruct (decide_atomic (t0 ◁ᵢ u)).
  + apply atomic_app_SN; auto.
    * apply IHtyp1 with (Γ := Γ) (T := Π U T0);
      auto; intros.
      apply head_SN with (u := u0), H4, step_app_left.
      auto. apply head_SN with (u := u0 ◁ᵢ u),
      H6 with (y := y $ u0). apply step_app_left. auto.
      apply subject_reduction with (t := t $ u0); auto.
      apply typ_app with (U := U); auto.
      apply step_app_left. auto.
    * apply IHtyp2 with (Γ := Γ) (T := U); auto; intros.
      apply tail_SN with (t := t), H4, step_app_right.
      auto. apply tail_SN with (t := t ◁ᵢ u),
      H6 with (y := t $ y). apply step_app_right. auto.
      apply subject_reduction with (t := t $ u0); auto.
      apply typ_app with (U := U); auto.
      apply step_app_right. auto.
  + destruct (decide_atomic t).
    * induction H7; try (inversion H2; fail).
      { destruct (subst_at_var i u); destruct H7.
        - rewrite H8. unfold AL in H.
          apply H with (Γ := Γ ◁ⁱ u) (T := U ◁ᵢ u)
                       (U := T0 ◁ᵢ u).
          + rewrite <- H8.
            apply substitution_lemma_strong with
              (T := Π U T0); auto.
          + apply substitution_lemma_strong; auto.
          + apply substitution_lemma_strong with
              (t := Π U T0) (T := 𝓤 r); auto.
            pose proof H2_.
            apply type_is_correct in H2_; auto.
            destruct H2_. replace r with x. auto.
            eapply equiv_𝓤_inversion.
            apply type_stability with (Γ := Γ)
            (t := Π U T0) (t' := rename up (squeeze Γ));
            auto. apply unshrink_lemma with (T := 𝓤 r).
            auto. rewrite squeeze_prop, <- H7.
            apply var_inversion
            with (sig := RankLevels). auto.
          + apply wf_subst_at; auto.
          + apply rename_SN. auto.
          + apply IHtyp2 with (Γ := Γ) (T := U);
            auto; intros.
            * apply tail_SN with (t := var i), H4,
              step_app_right, H9.
            * apply tail_SN with (t := var i ◁ᵢ u),
              H6 with (y := var i $ y).
              apply step_app_right. auto.
              apply subject_reduction
              with (t := var i $ u0); auto.
              apply typ_app with (U := U); auto.
              apply step_app_right. auto.
        - rewrite H7 in H2. inversion H2.
      }
