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
  Levels_functional_sig RankLevels := {}.
Proof. all: intros; rewrite H0; assumption. Qed.

#[refine]
Instance RankLevels_total :
  Levels_total_sig RankLevels := {}.
Proof. all: intros; eexists; reflexivity. Qed.

Definition AL r := (* Application lemma *)
  forall n (Γ: Ctx nat n) f t T U,
  Γ ⊢ f ⇐ Π T U -> Γ ⊢ t ⇐ T -> Γ ⊢ Π T U ⇐ 𝓤 r ->
  wf Γ -> SN f -> SN t -> SN (f $ t).

Definition SL r := (* Substitution lemma *)
  forall m n (Γ: Ctx nat (S m + n)) t u T U,
  shrink Γ ⊢ u ⇐ U -> shrink Γ ⊢ U ⇐ 𝓤 r ->
  Γ ⊢ t ⇐ T -> wf Γ -> SN t -> SN u -> SN (t ◁ᵢ u).

Lemma SL_to_AL:
  forall r, (forall j, j < r -> SL j) -> AL r.
Proof. unfold SL, AL. intros.
induction H4. induction H5. constructor. intros.
inversion H8; subst.
- apply H6. auto.
  apply subject_reduction with (t := x); auto.
- apply H7. auto.
  apply subject_reduction with (t := x0); auto.
  intros. assert (H' : SN (y $ x0)). { apply H6; auto. }
  destruct H'. apply H11, step_app_right. auto.
- apply Π_inversion in H2.
  destruct H2 as [ℓₜ [ℓᵤ [ℓ [HR [HT [HU HE]]]]]].
  change (ℓ = max (S ℓₜ) ℓᵤ) in HR.
  apply equiv_𝓤_inversion in HE. subst.
  apply λ_inversion in H0.
  destruct H0 as [ℓ₀ [U0 [HT0 [HF HE']]]].
  apply H with (j := ℓₜ) (m := 0) (Γ := Γ & T0)
               (T := U0) (U := T); auto.
  + apply PeanoNat.Nat.le_max_l.
  + apply wf_cons with (ℓ := ℓ₀); auto.
  + apply body_SN with (T := T0). constructor. auto.
  + constructor. auto.
Qed.

Lemma AL_to_SL: forall r, AL r -> SL r.
Proof.
unfold SL. intros. induction H4. dependent induction H2.
- apply sort_SN.
- apply Π_SN.
  + apply IHtyp1 with (Γ := Γ) (T := 𝓤 ℓₜ) (U := U);
    auto; intros.
    * apply dom_SN with (U := U0), H4, step_pi_left.
      auto.
    * apply dom_SN with (U := U0 ◁ᵢ u),
      H6 with (y := Π y U0). apply step_pi_left. auto.
      apply subject_reduction with (t := Π T0 U0); auto.
      apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ); auto.
      apply step_pi_left. auto.
  + change (SN (U0 ◁ᵢ u)).
    apply IHtyp2 with (Γ := Γ & T0) (T := 𝓤 ℓᵤ)
                      (U := U); auto; intros.
    * apply wf_cons with (ℓ := ℓₜ); auto.
    * apply codom_SN with (T := T0), H4, step_pi_right.
      auto.
    * apply codom_SN with (T := T0 ◁ᵢ u),
      H6 with (y := Π T0 y). apply step_pi_right. auto.
      apply subject_reduction with (t := Π T0 U0); auto.
      apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ); auto.
      apply step_pi_right. auto.
- destruct (subst_at_var i u).
  + rewrite H2. apply rename_SN. auto.
  + destruct H2. rewrite H2. apply var_SN.
- apply λ_SN.
  + apply IHtyp1 with (Γ := Γ) (T := 𝓤 ℓ) (U := U);
      auto; intros.
    * apply arg_SN with (t := t), H4, step_lam_left.
      auto.
    * apply arg_SN with (t := t ◁ᵢ u),
      H6 with (y := λ y t). apply step_lam_left. auto.
      apply subject_reduction with (t := λ U0 t); auto.
      apply typ_λ with (ℓ := ℓ); auto.
      apply step_lam_left. auto.
  + change (SN (t ◁ᵢ u)).
    apply IHtyp2 with (Γ := Γ & U0) (T := T0) (U := U);
      auto; intros.
    * apply wf_cons with (ℓ := ℓ); auto.
    * apply body_SN with (T := U0), H4, step_lam_right.
      auto.
    * apply body_SN with (T := U0 ◁ᵢ u),
      H6 with (y := λ U0 y). apply step_lam_right. auto.
      apply subject_reduction with (t := λ U0 t); auto.
      apply typ_λ with (ℓ := ℓ); auto.
      apply step_lam_right. auto.
- change (SN ((t ◁ᵢ u) $ (u0 ◁ᵢ u))).
  destruct (decide_atomic (t ◁ᵢ u)).
  + apply atomic_app_SN; auto.
    * apply IHtyp1 with (Γ := Γ) (T := Π U0 T0)
                        (U := U); auto; intros.
      apply head_SN with (u := u0), H4, step_app_left.
      auto. apply head_SN with (u := u0 ◁ᵢ u),
      H6 with (y := y $ u0). apply step_app_left. auto.
      apply subject_reduction with (t := t $ u0); auto.
      apply typ_app with (U := U0); auto.
      apply step_app_left. auto.
    * apply IHtyp2 with (Γ := Γ) (T := U0) (U := U);
        auto; intros.
      apply tail_SN with (t := t), H4, step_app_right.
      auto. apply tail_SN with (t := t ◁ᵢ u),
      H6 with (y := t $ y). apply step_app_right. auto.
      apply subject_reduction with (t := t $ u0); auto.
      apply typ_app with (U := U0); auto.
      apply step_app_right. auto.
  + destruct (decide_atomic t).
    * induction H7; try (inversion H2; fail).
      { destruct (subst_at_var i u).
        - rewrite H7. unfold AL in H.
          apply H with (Γ := Γ ◁ⁱ u) (T := U0 ◁ᵢ u)
                       (U := T0 ◁ᵢ u).
