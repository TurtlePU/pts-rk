From Stdlib Require Import PeanoNat.
From Stdlib.Arith Require Import Wf_nat.
From Equations Require Import Equations.
Require Import Levels Typing Syntax Context SN Preservation Reduction Inversions DefEq.

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

Definition SL_skel m n r (t: Term nat (S m + n)) P
  : Prop :=
  forall Γ: Ctx nat (S m + n),
  shrink Γ ⊢ squeeze Γ ⇐ 𝓤 r -> wf Γ ->
  forall T: Term nat (S m + n), Γ ⊢ t ⇐ T ->
  forall u: Term nat n, shrink Γ ⊢ u ⇐ squeeze Γ ->
  SN u -> P Γ T u.

Definition SL r := (* Substitution lemma *)
  forall m n t, SN t ->
  SL_skel m n r t (fun _ _ u => SN (t ◁ᵢ u)).

Lemma SL_to_AL:
  forall r, (forall j, j < r -> SL j) -> AL r.
Proof. unfold AL. intros r X. intros. induction H2.
- constructor. constructor; auto.
- eapply SN_WHR. constructor; auto.
  typ_inversion H1.
  change (ℓ = max (S ℓₜ) ℓᵤ) in H1.
  apply equiv_𝓤_inversion in H6. subst.
  typ_inversion H.
  apply equiv_Π_inversion in H6. destruct H6.
  apply X with (m := 0) (j := ℓₜ) (Γ := Γ & T0)
               (T := U0); auto.
  + apply Nat.le_max_l.
  + simpl. replace ℓₜ with ℓ. auto.
    symmetry. eapply equiv_𝓤_inversion.
    apply type_stability with (t := T) (t' := T0)
                              (Γ := Γ); auto.
  + apply wf_cons with (ℓ := ℓ); auto.
  + simpl. apply typ_conv with (T := T) (ℓ := ℓ); auto.
- eapply SN_WHR. constructor. apply H2.
  apply IHSN with (Γ := Γ) (T := T) (U := U); auto.
  apply subject_reduction with (t := t0); auto.
  apply reduction_weakening. auto.
Qed.

Definition SL_ind_hyp
  r (P: forall m n, Term nat (S m + n) ->
    Ctx nat (S m + n) -> Term nat (S m + n) ->
    Term nat n -> Prop)
  k (t: Term nat k) :=
  forall m n t' (H: k = S m + n),
  eq_rect _ _ t _ H = t' ->
  SL_skel m n r t' (P m n t').

Definition SL_SN_Ind_hyp r :=
  SL_ind_hyp r (fun _ _ t _ _ u => SN (t ◁ᵢ u)).

Lemma AL_to_SL:
  forall r, (forall s, s <= r -> AL s) -> SL r.
Proof. unfold SL, SL_skel. intros.
enough (HH: SL_SN_Ind_hyp r (S m + n) t).
unfold SL_SN_Ind_hyp, SL_ind_hyp, SL_skel in HH.
apply HH with (Γ := Γ) (T := T) (H := eq_refl); auto.
clear dependent Γ. clear dependent u.
pose proof H0 as HEND. clear H0 T.
apply sn_whr_snx with (P := SL_ind_hyp r
  (fun _ _ t Γ T u => SNx (t ◁ᵢ u) \/ SN (t ◁ᵢ u)
    /\ exists s, s <= r /\ Γ ⊢ T ⇐ 𝓤 s))
(P0 := SL_SN_Ind_hyp r)
(P1 := fun k t1 t2 =>
  forall m n (t1' t2': Term nat (S m + n))
  (H: k = S m + n), eq_rect _ _ t1 _ H = t1' ->
  eq_rect _ _ t2 _ H = t2' ->
  forall Γ, shrink Γ ⊢ squeeze Γ ⇐ 𝓤 r -> wf Γ ->
  forall T, Γ ⊢ t1' ⇐ T -> forall u: Term nat n,
  shrink Γ ⊢ u ⇐ squeeze Γ -> SN u ->
  WHR_SN (t1' ◁ᵢ u) (t2' ◁ᵢ u)
  /\ (SN (t2' ◁ᵢ u) -> SN (t1' ◁ᵢ u))
); unfold SL_SN_Ind_hyp, SL_ind_hyp, SL_skel;
auto; clear HEND; intros; subst; simpl;
try (simpl in H7).
- left. constructor.
- left. change (SNx (Π (T ◁ᵢ u) (U ◁ᵢ u))).
  typ_inversion H7. constructor.
  + apply H1 with (Γ := Γ) (T := 𝓤 ℓₜ) (H := eq_refl);
    auto.
  + apply (H3 (S m0) n1) with (Γ := Γ & T) (T := 𝓤 ℓᵤ)
    (H := eq_refl); auto.
    apply wf_cons with (ℓ := ℓₜ); auto.
- destruct (subst_at_var i u); destruct H0.
  + right. constructor.
    apply eq_rect with (rename up u). apply rename_SN.
    1-2: auto. exists r. constructor. reflexivity.
    pose proof H3. apply type_is_correct in H3; auto.
    destruct H3. replace r with x. auto.
    eapply equiv_𝓤_inversion.
    apply type_stability with (Γ := Γ) (t := T)
    (t' := rename up (squeeze Γ)); auto.
    * apply unshrink_lemma with (T := 𝓤 r). auto.
    * rewrite squeeze_prop, <- H0.
      apply var_inversion with (sig := RankLevels).
      auto.
  + left. apply eq_rect with (var x). constructor. auto.
- pose proof H7 as HT. typ_inversion H7.
  assert (H3': SN (u ◁ᵢ u0)).
    { apply H3 with (Γ := Γ) (T := U) (H := eq_refl);
      auto. }
  assert (HH: SNx (t0 ◁ᵢ u0) \/ SN (t0 ◁ᵢ u0)
              /\ exists s, s <= r /\ Γ ⊢ Π U T0 ⇐ 𝓤 s).
  { apply H1 with (H := eq_refl); auto. } destruct HH.
  + left. constructor; auto.
  + right. unpack H7. split.
    * unfold AL in H. apply H with (s := s)
      (Γ := Γ ◁ⁱ u0) (T := U ◁ᵢ u0)
      (U := (T0: Term nat (S (S m0 + n1))) ◁ᵢ u0);
      auto.
      { change (Γ ◁ⁱ u0 ⊢ t0 ◁ᵢ u0 ⇐ Π U T0 ◁ᵢ u0).
        apply substitution_lemma_strong; auto. }
      { change (Γ ◁ⁱ u0 ⊢ u ◁ᵢ u0 ⇐ U ◁ᵢ u0).
        apply substitution_lemma_strong; auto. }
      { change (Γ ◁ⁱ u0 ⊢ Π U T0 ◁ᵢ u0 ⇐ 𝓤 s ◁ᵢ u0).
        apply substitution_lemma_strong; auto. }
      { apply wf_subst_at; auto. }
    * typ_inversion H13.
      change (ℓ = max (S ℓₜ) ℓᵤ) in H13. subst.
      exists ℓᵤ. split.
      { transitivity s. replace s with (max (S ℓₜ) ℓᵤ).
        apply Nat.le_max_r. symmetry.
        eapply equiv_𝓤_inversion, H16. auto. }
      { apply type_is_correct in HT; auto. destruct HT.
        replace ℓᵤ with x. auto.
        eapply equiv_𝓤_inversion.
        apply type_stability
        with (Γ := Γ) (t := T) (t' := T0 ◁ u); auto.
        apply substitution_lemma
        with (T := 𝓤 ℓᵤ) (U := U); auto.
      }
- assert (HH: SNx (t0 ◁ᵢ u) \/ SN (t0 ◁ᵢ u)
              /\ exists s, s <= r /\ Γ ⊢ T ⇐ 𝓤 s).
              { apply H1 with (H := eq_refl); auto. }
  destruct HH; [ constructor | destruct H2 ]; auto.
- typ_inversion H7. apply SN_λ.
  + apply H1 with (Γ := Γ) (T := 𝓤 ℓ) (H := eq_refl);
    auto.
  + change (SN (t0 ◁ᵢ u)).
    apply H3 with (Γ := Γ & T) (T := U) (H := eq_refl);
    auto. apply wf_cons with (ℓ := ℓ); auto.
- apply H1 with (t2' := u) (Γ := Γ) (T := T)
  (H := eq_refl); auto.
  apply H3 with (Γ := Γ) (T := T) (H := eq_refl); auto.
  apply subject_reduction with (t := t0); auto.
  apply reduction_weakening. auto.
- simpl in H8. typ_inversion H8. typ_inversion H4.
  assert (wh: WHR_SN
    ([U ◁ᵢ u0] (t0 ◁ᵢ u0) $ (u ◁ᵢ u0))
    (t0 ◁ u ◁ᵢ u0)
  ). { unfold subst_at. rewrite replace_subst.
       apply WHR_SN_here.
       - apply H1 with (Γ := Γ) (T := 𝓤 ℓ)
         (H := eq_refl); auto.
       - apply H3 with (Γ := Γ) (T := U0)
         (H := eq_refl); auto.
     }
  split. auto. intros. eapply SN_WHR. apply wh. auto.
- simpl in H6. typ_inversion H6.
  assert (HH: WHR_SN (t0 ◁ᵢ u0) (t' ◁ᵢ u0)
          /\ (SN (t' ◁ᵢ u0) -> SN (t0 ◁ᵢ u0))).
        { apply H1 with (Γ := Γ) (T := Π U T0)
          (H := eq_refl); auto. }
  destruct HH.
  assert (wh: WHR_SN (t0 $ u ◁ᵢ u0) (t' $ u ◁ᵢ u0)).
    { apply WHR_SN_there; auto. }
  split. auto. intros. eapply SN_WHR. apply wh. auto.
Qed.

Lemma AL_holds: forall r, AL r.
Proof.
enough (H: forall r, AL r /\ SL r).
  { intro. destruct (H r). auto. }
induction r using (well_founded_induction lt_wf).
assert (HAL: AL r). apply SL_to_AL.
- intros. specialize (H j). intuition.
- split. auto. apply AL_to_SL. intros. inversion H0.
  auto. subst. apply le_n_S in H1. specialize (H s).
  intuition.
Qed.

Lemma main_lemma {n} Γ (t T: Term nat n):
  wf Γ -> Γ ⊢ t ⇐ T -> SN t.
Proof. intros. induction H;
try solve [constructor; constructor]; auto.
- constructor. constructor. auto.
  apply IHtyp2, wf_cons with (ℓ := ℓₜ); auto.
- apply SN_λ. auto.
  apply IHtyp2, wf_cons with (ℓ := ℓ); auto.
- pose proof H. apply type_is_correct in H; auto.
  destruct H. pose proof (AL_holds x). unfold AL in H2.
  apply H2 with (Γ := Γ) (T := U) (U := T); auto.
Qed.

Theorem strong_normalization {n} Γ (t T: Term nat n):
  wf Γ -> Γ ⊢ t ⇐ T -> sn t.
Proof.
intros.
apply SN_soundness, main_lemma with (Γ := Γ) (T := T);
auto.
Qed.

Print Assumptions strong_normalization.
