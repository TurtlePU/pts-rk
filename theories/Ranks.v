From Stdlib Require Import PeanoNat.
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
  apply Π_inversion in H1.
  destruct H1 as [ℓₜ [ℓᵤ [ℓ [HR [HT [HU HE]]]]]].
  change (ℓ = max (S ℓₜ) ℓᵤ) in HR.
  apply equiv_𝓤_inversion in HE. subst.
  apply λ_inversion in H.
  destruct H as [ℓ₀ [U0 [HT0 [HF HE']]]].
  apply equiv_Π_inversion in HE'. destruct HE'.
  apply X with (m := 0) (j := ℓₜ) (Γ := Γ & T0)
               (T := U0); auto.
  + apply Nat.le_max_l.
  + simpl. replace ℓₜ with ℓ₀. auto.
    symmetry. eapply equiv_𝓤_inversion.
    apply type_stability with (t := T) (t' := T0)
                              (Γ := Γ); auto.
  + apply wf_cons with (ℓ := ℓ₀); auto.
  + simpl. apply typ_conv with (T := T) (ℓ := ℓ₀); auto.
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
auto; clear HEND; intros; subst; simpl.
- left. constructor.
- left. change (SNx (Π (T ◁ᵢ u) (U ◁ᵢ u))).
  apply Π_inversion in H7.
  destruct H7 as [ℓₜ [ℓᵤ [ℓ [eq [typT [typU beq]]]]]].
  constructor.
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
- pose proof H7 as HT. apply app_inversion in H7.
  destruct H7 as [U [V [typt [typu beq]]]].
  assert (H3': SN (u ◁ᵢ u0)).
    { apply H3 with (Γ := Γ) (T := U) (H := eq_refl);
      auto. }
  assert (HH: SNx (t0 ◁ᵢ u0) \/ SN (t0 ◁ᵢ u0)
              /\ exists s, s <= r /\ Γ ⊢ Π U V ⇐ 𝓤 s).
  { apply H1 with (H := eq_refl); auto. } destruct HH.
  + left. constructor; auto.
  + right. destruct H4 as [snt [s [sler typs]]]. split.
    * unfold AL in H. apply H with (s := s)
      (Γ := Γ ◁ⁱ u0) (T := U ◁ᵢ u0) (U := V ◁ᵢ u0);
      auto.
      { change (Γ ◁ⁱ u0 ⊢ t0 ◁ᵢ u0 ⇐ Π U V ◁ᵢ u0).
        apply substitution_lemma_strong; auto. }
      { change (Γ ◁ⁱ u0 ⊢ u ◁ᵢ u0 ⇐ U ◁ᵢ u0).
        apply substitution_lemma_strong; auto. }
      { change (Γ ◁ⁱ u0 ⊢ Π U V ◁ᵢ u0 ⇐ 𝓤 s ◁ᵢ u0).
        apply substitution_lemma_strong; auto. }
      { apply wf_subst_at; auto. }
    * apply Π_inversion in typs.
      destruct typs as [ℓᵤ [ℓᵥ [ℓᵤᵥ [lq [_ [tv bq]]]]]].
      change (ℓᵤᵥ = max (S ℓᵤ) ℓᵥ) in lq. subst.
      exists ℓᵥ. split.
      { transitivity s. replace s with (max (S ℓᵤ) ℓᵥ).
        apply Nat.le_max_r. symmetry.
        eapply equiv_𝓤_inversion, bq. auto. }
      { apply type_is_correct in HT; auto. destruct HT.
        replace ℓᵥ with x. auto.
        eapply equiv_𝓤_inversion.
        apply type_stability
        with (Γ := Γ) (t := T) (t' := V ◁ u); auto.
        apply substitution_lemma
        with (T := 𝓤 ℓᵥ) (U := U); auto.
      }
- assert (HH: SNx (t0 ◁ᵢ u) \/ SN (t0 ◁ᵢ u)
              /\ exists s, s <= r /\ Γ ⊢ T ⇐ 𝓤 s).
              { apply H1 with (H := eq_refl); auto. }
  destruct HH; [ constructor | destruct H2 ]; auto.
- apply λ_inversion in H7.
  destruct H7 as [ℓ [U [tT [tt beq]]]]. apply SN_λ.
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
- apply app_inversion in H8.
  destruct H8 as [U0 [T0 [tl [tu beq]]]].
  apply λ_inversion in tl.
  destruct tl as [ℓ [U1 [tU [tt beq']]]].
  assert (wh: WHR_SN
    ([U ◁ᵢ u0] (t0 ◁ᵢ u0) $ (u ◁ᵢ u0))
    (t0 ◁ u ◁ᵢ u0)
  ). { rewrite subst_at_subst. apply WHR_SN_here.
       - apply H1 with (Γ := Γ) (T := 𝓤 ℓ)
         (H := eq_refl); auto.
       - apply H3 with (Γ := Γ) (T := U0)
         (H := eq_refl); auto.
     }
  split. auto. intros. eapply SN_WHR. apply wh. auto.
- apply app_inversion in H6.
  destruct H6 as [U [T0 [tt [tu beq]]]].
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
enough (H: forall r s, s <= r -> AL s /\ SL s). {
  intro. assert (H': AL r /\ SL r).
  { apply H with (r := r). reflexivity. }
  destruct H'. auto.
}
induction r; intros.
- inversion H. subst. assert (H': AL 0).
  { apply SL_to_AL. intros. inversion H0. }
  split. auto. apply AL_to_SL.
  intros. inversion H0. auto.
- inversion H.
  + assert (H': AL (S r)). {
      apply SL_to_AL. intros. assert (H': AL j /\ SL j);
      [ apply IHr, le_S_n | destruct H' ]; auto.
    }
    split. auto. apply AL_to_SL. intros. inversion H1.
    auto. assert (H'': AL s0 /\ SL s0);
    [ apply IHr | destruct H'' ]; auto.
  + apply IHr. auto.
Qed.

Lemma main_lemma {n} Γ (t T: Term nat n):
  wf Γ -> Γ ⊢ t ⇐ T -> SN t.
Proof. intros. induction H.
- constructor. constructor.
- constructor. constructor.
  + apply IHtyp1. auto.
  + apply IHtyp2, wf_cons with (ℓ := ℓₜ); auto.
- constructor. constructor.
- apply SN_λ.
  + apply IHtyp1. auto.
  + apply IHtyp2, wf_cons with (ℓ := ℓ); auto.
- pose proof H. apply type_is_correct in H; auto.
  destruct H. pose proof (AL_holds x). unfold AL in H2.
  apply H2 with (Γ := Γ) (T := U) (U := T); auto.
- auto.
Qed.

Theorem strong_normalization {n} Γ (t T: Term nat n):
  wf Γ -> Γ ⊢ t ⇐ T -> sn t.
Proof. intros.
apply SN_soundness, main_lemma with (Γ := Γ) (T := T);
auto.
Qed.

Print Assumptions strong_normalization.
