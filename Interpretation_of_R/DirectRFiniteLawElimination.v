(** Exact rank-three lifting for eliminating positive finite membership into
    negative arithmetic laws. This does not add cumulativity to PTS-rk. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural
  DirectRLogic DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp DirectRPositive.
Import ListNotations.
Module FiniteLawElimination.
Import CommonCodes Core Structural NegativeLogic FiniteTables FiniteObservations.
Import Positive.
Definition J2 : closed_term := Arrow Top Top.
Lemma J2_formation : Typed ε J2 (𝓤 2).
Proof. exact (arrow_formation ε Top Top 1 1 top_formation top_formation). Qed.
Lemma J2_inhabited {n} (Γ : Ctx nat n) : inhabited Γ (lift_closed J2).
Proof.
  change (inhabited Γ (Arrow (lift_closed Top) (lift_closed Top))).
  apply FiniteUp.identity_inhabited. exists 1. exact (lift_closed_typed Γ _ _ top_formation).
Qed.
Definition lifted_family {n} (A P : Term nat n) :=
  lam A (Arrow (lift_closed J2) (app (shift P) V0)).
Lemma lifted_family_typed {n} (Γ : Ctx nat n) A P r :
  r <= 3 -> Typed Γ A (𝓤 1) -> Typed Γ P (Arrow A (𝓤 r)) ->
  Typed Γ (lifted_family A P) (Arrow A (𝓤 3)).
Proof.
  intros Hr HA HP. unfold lifted_family. apply (tLam HA).
  replace 3 with (Nat.max 3 r) by lia. apply arrow_formation.
  - exact (lift_closed_typed (Γ & A) _ _ J2_formation).
  - pose proof (weakening RankSorts _ _ A HP) as HP'. rewrite shift_arrow in HP'.
    eapply arrow_application; [exact HP' |exact (tV (Γ & A) fzero)].
Qed.
Lemma lifted_family_beta {n} (A P u : Term nat n) :
  app (lifted_family A P) u =ᵝ Arrow (lift_closed J2) (app P u).
Proof.
  unfold lifted_family. eapply beta_trans; [apply beta_contract |].
  rewrite subst_arrow, subst_closed, subst_app, substitute_shift, subst_V0. reflexivity.
Qed.
Theorem delta_eliminate_lower {n} (Γ : Ctx nat n) q u P r :
  0 < q -> r <= 3 -> Typed Γ u (selector_type q) ->
  inhabited Γ (delta q u) -> Typed Γ P (Arrow (selector_type q) (𝓤 r)) ->
  (forall i, i < q -> inhabited Γ (app P (lift_closed (point q i)))) ->
  inhabited Γ (app P u).
Proof.
  intros Hq Hr Hu Hd HP Hpoints.
  assert (HA : Typed Γ (selector_type q) (𝓤 1)).
  { destruct q; [lia |apply selector_type_formation]. }
  pose proof (lifted_family_typed Γ _ _ r Hr HA HP) as HQ.
  assert (HB : forall i, i < q -> inhabited Γ
    (app (lifted_family (selector_type q) P) (lift_closed (point q i)))).
  { intros i Hi. eapply FiniteUp.inhabited_conversion.
    - apply (arrow_intro Γ (lift_closed J2) (app P (lift_closed (point q i)))).
      + exists 2. exact (lift_closed_typed Γ _ _ J2_formation).
      + apply inhabited_shift, Hpoints. exact Hi.
    - eapply arrow_application; [exact HQ |apply point_in_context].
    - symmetry. apply lifted_family_beta. }
  pose proof (delta_eliminate Γ q u _ Hd HQ HB) as Hlifted.
  assert (HF : inhabited Γ (Arrow (lift_closed J2) (app P u))).
  { eapply FiniteUp.inhabited_conversion; [exact Hlifted | |apply lifted_family_beta].
    eapply arrow_formation; [exact (lift_closed_typed Γ _ _ J2_formation) |].
    eapply arrow_application; eassumption. }
  eapply arrow_elim; [exact HF |apply J2_inhabited].
Qed.
Lemma apply_terms_typed {n} (Γ : Ctx nat n) A xs f B :
  Forall (fun x => Typed Γ x A) xs ->
  Typed Γ f (Arrows (repeat A (length xs)) B) -> Typed Γ (table_apply f xs) B.
Proof.
  intro Hxs. revert f. induction Hxs; intros f Hf; cbn [table_apply fold_left]; [exact Hf |].
  apply IHHxs. eapply arrow_application; [exact Hf |exact H].
Qed.
Definition applied_family {n} (A P : Term nat n) (xs : list (Term nat n)) :=
  lam A (table_apply (app (shift P) V0) (map shift xs)).
Lemma applied_family_typed {n} (Γ : Ctx nat n) A P xs r :
  Typed Γ A (𝓤 1) -> Forall (fun x => Typed Γ x A) xs ->
  Typed Γ P (Arrow A (Arrows (repeat A (length xs)) (𝓤 r))) ->
  Typed Γ (applied_family A P xs) (Arrow A (𝓤 r)).
Proof.
  intros HA Hxs HP. unfold applied_family. apply (tLam HA).
  eapply apply_terms_typed.
  - apply Forall_map. eapply Forall_impl; [|exact Hxs].
    intros x Hx. exact (weakening RankSorts _ _ A Hx).
  - pose proof (weakening RankSorts _ _ A HP) as H.
    rewrite shift_arrow, shift_arrows, map_repeat in H.
    rewrite length_map. eapply arrow_application; [exact H |exact (tV (Γ & A) fzero)].
Qed.
Lemma applied_family_beta {n} (A P u : Term nat n) xs :
  app (applied_family A P xs) u =ᵝ table_apply (app P u) xs.
Proof.
  unfold applied_family. eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_table_apply, replace_application, replace_shift_substitution.
  cbn [replace V0 fin_match]. rewrite map_map.
  assert (HE : map (fun x => replace (fin_match u (fun i => var i)) (shift x)) xs = xs).
  { rewrite <- (map_id xs) at 2. apply map_ext. intro x. apply replace_shift_substitution. }
  rewrite HE. reflexivity.
Qed.
(** The branch premise is over every finite tuple of the given length, not
    merely over finitely many examples checked by an external evaluator. *)
Theorem delta_eliminate_arguments {n} (Γ : Ctx nat n) q xs P r :
  0 < q -> r <= 3 ->
  Forall (fun x => Typed Γ x (selector_type q)) xs ->
  Forall (fun x => inhabited Γ (delta q x)) xs ->
  Typed Γ P (Arrows (repeat (selector_type q) (length xs)) (𝓤 r)) ->
  (forall indices, length indices = length xs -> Forall (fun i => i < q) indices ->
    inhabited Γ (table_apply P (map (fun i => lift_closed (point q i)) indices))) ->
  inhabited Γ (table_apply P xs).
Proof.
  intros Hq Hr. revert P. induction xs as [|u xs IH]; intros P Htypes Hdelta HP Hbranches.
  - exact (Hbranches [] eq_refl (Forall_nil _)).
  - inversion Htypes as [|? ? Hu Hxs]; subst.
    inversion Hdelta as [|? ? Hdu Hdxs]; subst.
    assert (HA : Typed Γ (selector_type q) (𝓤 1)).
    { destruct q; [lia |apply selector_type_formation]. }
    pose proof (applied_family_typed Γ _ _ _ r HA Hxs HP) as HQ.
    assert (HB : forall i, i < q -> inhabited Γ
      (app (applied_family (selector_type q) P xs) (lift_closed (point q i)))).
    { intros i Hi. eapply FiniteUp.inhabited_conversion.
      - apply IH; [exact Hxs |exact Hdxs | |].
        + eapply arrow_application; [exact HP |apply point_in_context].
        + intros indices Hlen Hbounds. exact (Hbranches (i::indices) (f_equal S Hlen) (Forall_cons i Hi Hbounds)).
      - eapply arrow_application; [exact HQ |apply point_in_context].
      - symmetry. apply applied_family_beta. }
    pose proof (delta_eliminate_lower Γ q u _ r Hq Hr Hu Hdu HQ HB) as H.
    eapply FiniteUp.inhabited_conversion; [exact H | |apply applied_family_beta].
    eapply apply_terms_typed; [exact Htypes |exact HP].
Qed.
End FiniteLawElimination.
