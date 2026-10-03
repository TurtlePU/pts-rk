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
unfold SL. intros. induction H4. dependent induction x.
- unfold subst. simpl. constructor. intros.
  inversion H7.
- change (Term nat (S (S m + n))) in x2. apply Π_SN.
  + apply IHx1 with (Γ := Γ) (T := T) (U := U); auto;
    intros.
    * apply dom_SN with (U := x2), H4, step_pi_left.
      auto.
    * apply dom_SN with (U := x2 ◁ᵢ u),
      H5 with (y := Π y x2), step_pi_left. auto.
  + change (SN (x2 ◁ᵢ u)).
    apply IHx2 with (Γ := Γ) (U := U); auto; intros.
    * apply codom_SN with (T := x1), H3, step_pi_right.
      auto.
    * apply codom_SN with (T := x1 ◁ᵢ u),
      H5 with (y := Π x1 y), step_pi_right. auto.
- destruct (subst_at_var f u).
  + apply eq_rect with (x := rename up u).
    * apply rename_SN. auto.
    * symmetry. exact H6.
  + destruct H6. apply eq_rect with (x := var x).
    * constructor. intros. inversion H7.
    * symmetry. exact H6.
- change (Term nat (S (S m + n))) in x2. apply λ_SN.
  + apply IHx1 with (Γ := Γ) (U := U); auto; intros.
    * apply arg_SN with (t := x2), H3, step_lam_left.
      auto.
    * apply arg_SN with (t := x2 ◁ᵢ u),
      H5 with (y := λ y x2), step_lam_left. auto.
  + change (SN (x2 ◁ᵢ u)).
    apply IHx2 with (Γ := Γ) (U := U); auto; intros.
    * apply body_SN with (T := x1), H3, step_lam_right.
      auto.
    * apply body_SN with (T := x1 ◁ᵢ u),
      H5 with (y := λ x1 y), step_lam_right. auto.
- change (SN ((x1 ◁ᵢ u) $ (x2 ◁ᵢ u))).
  destruct (decide_atomic (x1 ◁ᵢ u)).
  + apply atomic_app_SN; auto.
    * apply IHx1 with (Γ := Γ) (U := U); auto; intros.
      apply head_SN with (u := x2), H3, step_app_left.
      auto. apply head_SN with (u := x2 ◁ᵢ u),
      H5 with (y := y $ x2), step_app_left. auto.
    * apply IHx2 with (Γ := Γ) (U := U); auto; intros.
      apply tail_SN with (t := x1), H3, step_app_right.
      auto. apply tail_SN with (t := x1 ◁ᵢ u),
      H5 with (y := x1 $ y), step_app_right. auto.
  + destruct (decide_atomic x1).
    * induction H7; try (inversion H6; fail).
      { destruct (subst_at_var i u).
        - apply eq_rect with (x := rename up u)
               (P := fun t => SN (t $ (x2 ◁ᵢ u))).
          +
