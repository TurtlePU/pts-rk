(** Positive finite-observation certificates, in the original PTS. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRPositive DirectRFiniteTables.
Import ListNotations.

Module FiniteObservations.
Import Codes Core Structural NegativeLogic Positive FiniteTables.

Definition points q {n} : list (Term nat n) :=
  map (fun i => lift_closed (point q i)) (seq 0 q).
Definition delta q {n} (u : Term nat n) :=
  Membership (selector_type q) (points q) u.

Lemma points_typed {n} (Γ : Ctx nat n) q :
  Forall (fun x => Typed Γ x (selector_type q)) (points q).
Proof.
  unfold points. apply Forall_map, Forall_forall. intros i Hi.
  pose proof (lift_closed_typed Γ _ _ (point_typed q i)) as H.
  unfold lift_closed at 2 in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma delta_formation {n} (Γ : Ctx nat n) q u :
  0 < q -> Typed Γ u (selector_type q) -> Typed Γ (delta q u) (𝓤 4).
Proof.
  intros Hq Hu. apply membership_formation; auto using points_typed.
  - destruct q; [lia |apply selector_type_formation].
  - unfold points. destruct q; [lia |discriminate].
Qed.
Theorem delta_point {n} (Γ : Ctx nat n) q i :
  i < q -> inhabited Γ (delta q (lift_closed (point q i))).
Proof.
  intro Hi. apply membership_intro; auto using points_typed.
  - destruct q; [lia |apply selector_type_formation].
  - unfold points. apply in_map_iff. exists i. split; [reflexivity |].
    apply in_seq. lia.
Qed.
Theorem delta_eliminate {n} (Γ : Ctx nat n) q u Q :
  inhabited Γ (delta q u) -> Typed Γ Q (Arrow (selector_type q) (𝓤 3)) ->
  (forall i, i < q -> inhabited Γ (app Q (lift_closed (point q i)))) ->
  inhabited Γ (app Q u).
Proof.
  intros Hu HQ Hpoints. eapply membership_elim; [exact Hu |exact HQ |].
  unfold points. apply Forall_map, Forall_forall. intros i Hi.
  apply Hpoints. apply in_seq in Hi. lia.
Qed.
Lemma rename_delta {m n} (f : Fin m -> Fin n) q u :
  rename f (delta q u) = delta q (rename f u).
Proof.
  unfold delta. rewrite rename_membership, rename_selector_type.
  unfold points. rewrite map_map.
  assert (H : map (fun i => rename f (lift_closed (point q i))) (seq 0 q) =
    map (fun i => lift_closed (point q i)) (seq 0 q)).
  { apply map_ext. intro i. apply rename_lift_closed. }
  rewrite H. reflexivity.
Qed.

Definition compose {n} (A Q f : Term nat n) :=
  lam A (app (shift Q) (app (shift f) V0)).
Lemma compose_typed {n} (Γ : Ctx nat n) A Q f :
  Typed Γ A (𝓤 1) -> Typed Γ Q (Arrow A (𝓤 3)) ->
  Typed Γ f (Arrow A A) -> Typed Γ (compose A Q f) (Arrow A (𝓤 3)).
Proof.
  intros HA HQ Hf. unfold compose. apply (tLam HA).
  pose proof (weakening RankSorts _ _ A HQ) as HQ'. rewrite shift_arrow in HQ'.
  pose proof (weakening RankSorts _ _ A Hf) as Hf'. rewrite shift_arrow in Hf'.
  eapply arrow_application; [exact HQ' |].
  eapply arrow_application; [exact Hf' |exact (tV (Γ & A) fzero)].
Qed.
Lemma compose_beta {n} (A Q f u : Term nat n) :
  app (compose A Q f) u =ᵝ app Q (app f u).
Proof.
  unfold compose. eapply beta_trans; [apply beta_contract |].
  rewrite !subst_app, !substitute_shift, subst_V0. reflexivity.
Qed.
Lemma capped_typed {n} (Γ : Ctx nat n) q :
  Typed Γ (lift_closed (capped_successor q))
    (Arrow (selector_type q) (selector_type q)).
Proof.
  pose proof (lift_closed_typed Γ _ _ (capped_successor_typed q)) as H.
  unfold lift_closed at 2 in H. rewrite rename_arrow, !rename_selector_type in H. exact H.
Qed.
Lemma point_in_context {n} (Γ : Ctx nat n) q i :
  Typed Γ (lift_closed (point q i)) (selector_type q).
Proof.
  pose proof (lift_closed_typed Γ _ _ (point_typed q i)) as H.
  unfold lift_closed at 2 in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma capped_delta_elim {n} (Γ : Ctx nat n) q u Q :
  0 < q -> Typed Γ u (selector_type q) -> inhabited Γ (delta q u) ->
  Typed Γ Q (Arrow (selector_type q) (𝓤 3)) ->
  (forall i, i < q -> inhabited Γ (app Q (lift_closed (point q i)))) ->
  inhabited Γ (app Q (app (lift_closed (capped_successor q)) u)).
Proof.
  intros Hq Hu Hdelta HQ Hpoints.
  assert (HA : Typed Γ (selector_type q) (𝓤 1)).
  { destruct q; [lia |apply selector_type_formation]. }
  pose proof (capped_typed Γ q) as Hs.
  pose proof (compose_typed Γ _ _ _ HA HQ Hs) as HM.
  assert (Hbranches : forall i, i < q -> inhabited Γ
    (app (compose (selector_type q) Q (lift_closed (capped_successor q)))
      (lift_closed (point q i)))).
  { intros i Hi. destruct (Hpoints _ (capped_entry_bound q i Hq)) as [p Hp].
    exists p. eapply tConv; [exact Hp | |].
    - eapply arrow_application; [exact HM |apply point_in_context].
    - symmetry. eapply beta_trans; [apply compose_beta |].
      apply beta_app; [reflexivity |].
      exact (rename_equiv empty_renaming _ _ (capped_successor_action q i Hi)). }
  destruct (delta_eliminate Γ q u _ Hdelta HM Hbranches) as [p Hp].
  exists p. eapply tConv; [exact Hp | |apply compose_beta].
  eapply arrow_application; [exact HQ |]. eapply arrow_application; eassumption.
Qed.
Theorem delta_successor {n} (Γ : Ctx nat n) q u :
  0 < q -> Typed Γ u (selector_type q) -> inhabited Γ (delta q u) ->
  inhabited Γ (delta q (app (lift_closed (capped_successor q)) u)).
Proof.
  intros Hq Hu Hd.
  assert (HA : Typed Γ (selector_type q) (𝓤 1)).
  { destruct q; [lia |apply selector_type_formation]. }
  set (QA := @Arrow n (selector_type q) (𝓤 3)).
  assert (HQA : Typed Γ QA (𝓤 2)) by
    (exact (arrow_formation Γ _ _ _ _ HA (tU Γ 3))).
  assert (HV : Typed (Γ & QA) V0 (Arrow (selector_type q) (𝓤 3))).
  { pose proof (tV (Γ & QA) fzero) as H.
    change (Typed (Γ & QA) V0 (shift QA)) in H.
    unfold QA, shift in H. rewrite rename_arrow, rename_selector_type in H. exact H. }
  assert (HB : inhabited (Γ & QA)
    (Arrows (map (fun x => app V0 (shift x)) (points q))
      (app V0 (shift (app (lift_closed (capped_successor q)) u))))).
  { apply arrows_intro.
    - apply Forall_map. pose proof (points_typed Γ q) as Hxs.
      eapply Forall_impl; [|exact Hxs]. intros x Hx. exists 3.
      eapply arrow_application; [exact HV |].
      pose proof (weakening RankSorts _ _ QA Hx) as H.
      unfold shift in H. rewrite rename_selector_type in H. exact H.
    - intros m Δ f Hext Hargs.
      rewrite rename_application. unfold shift. rewrite rename_application,
        rename_lift_closed, rename_application, rename_lift_closed.
      apply capped_delta_elim; [exact Hq | | | |].
      + pose proof (weakening RankSorts _ _ QA Hu) as H.
        pose proof (extension_typed _ _ _ _ _ Hext H) as H'.
        unfold shift in H'. rewrite !rename_selector_type in H'. exact H'.
      + pose proof (inhabited_shift Γ _ QA Hd) as H.
        pose proof (extension_inhabited _ _ _ _ Hext H) as H'.
        unfold shift in H'. rewrite !rename_delta in H'. exact H'.
      + pose proof (extension_typed _ _ _ _ _ Hext HV) as H.
        rewrite rename_arrow, rename_selector_type in H. exact H.
      + intros i Hi.
        assert (Hin : In (app (@V0 n) (shift (lift_closed (point q i))))
          (map (fun x => app V0 (shift x)) (points q))).
        { apply in_map_iff. exists (lift_closed (point q i)). split; [reflexivity |].
          unfold points. apply in_map_iff. exists i. split; [reflexivity |].
          apply in_seq. lia. }
        specialize (Hargs _ Hin). rewrite rename_application in Hargs.
        unfold shift in Hargs. rewrite !rename_lift_closed in Hargs. exact Hargs. }
  destruct HB as [p Hp]. exists (lam QA p). exact (tLam HQA Hp).
Qed.
Definition delta_step_type q : closed_term :=
  Π (selector_type q)
    (Arrow (delta q V0) (delta q (app (lift_closed (capped_successor q)) V0))).
Theorem delta_step_realized q : 0 < q -> Realizes (delta_step_type q).
Proof.
  intro Hq.
  assert (HA : Typed ε (selector_type q) (𝓤 1)).
  { destruct q; [lia |apply selector_type_formation]. }
  assert (Hu : Typed (ε & selector_type q) V0 (selector_type q)).
  { pose proof (tV (ε & selector_type q) fzero) as H.
    change (Typed (ε & selector_type q) V0 (shift (selector_type q))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H. }
  assert (HB : inhabited (ε & selector_type q)
    (Arrow (delta q V0) (delta q (app (lift_closed (capped_successor q)) V0)))).
  { apply arrow_intro.
    - exists 4. apply delta_formation; assumption.
    - unfold shift. rewrite rename_delta, rename_application, rename_lift_closed.
      apply delta_successor; [exact Hq | |].
      + pose proof (weakening RankSorts _ _ (delta q V0) Hu) as H.
        unfold shift in H. rewrite rename_selector_type in H. exact H.
      + pose proof (newest (ε & selector_type q) (delta q V0)) as H.
        unfold shift in H. rewrite rename_delta in H. exact H. }
  destruct HB as [p Hp]. exists (lam (selector_type q) p). exact (tLam HA Hp).
Qed.
End FiniteObservations.
