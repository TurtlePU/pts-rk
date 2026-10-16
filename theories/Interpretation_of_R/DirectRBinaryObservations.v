(** Positive domain closure for arbitrary bounded binary selector tables. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural
  DirectRLogic DirectRPositive DirectRFiniteTables DirectRBinaryTables DirectRFiniteObservations.
Import ListNotations.
Module BinaryObservations.
Import CommonCodes Core Structural NegativeLogic Positive FiniteTables BinaryTables FiniteObservations.

Lemma binary_in_context {n} (Γ : Ctx nat n) q b :
  Typed Γ (lift_closed (binary_table q b))
    (Arrow (selector_type q) (Arrow (selector_type q) (selector_type q))).
Proof.
  pose proof (lift_closed_typed Γ _ _ (binary_table_typed q b)) as H.
  unfold lift_closed at 2 in H. rewrite !rename_arrow, !rename_selector_type in H. exact H.
Qed.
Definition compose_left {n} (A Q op v : Term nat n) :=
  lam A (app (shift Q) (app (app (shift op) V0) (shift v))).
Lemma compose_left_typed {n} (Γ : Ctx nat n) A Q op v :
  Typed Γ A (𝓤 1) -> Typed Γ Q (Arrow A (𝓤 3)) ->
  Typed Γ op (Arrow A (Arrow A A)) -> Typed Γ v A ->
  Typed Γ (compose_left A Q op v) (Arrow A (𝓤 3)).
Proof.
  intros HA HQ Hop Hv. unfold compose_left. apply (tLam HA).
  pose proof (weakening RankSorts _ _ A HQ) as HQ'. rewrite shift_arrow in HQ'.
  pose proof (weakening RankSorts _ _ A Hop) as Hop'. rewrite !shift_arrow in Hop'.
  pose proof (weakening RankSorts _ _ A Hv) as Hv'.
  eapply arrow_application; [exact HQ' |].
  eapply arrow_application; [eapply arrow_application; [exact Hop' |exact (tV (Γ & A) fzero)] |exact Hv'].
Qed.
Lemma compose_left_beta {n} (A Q op v u : Term nat n) :
  app (compose_left A Q op v) u =ᵝ app Q (app (app op u) v).
Proof.
  unfold compose_left. eapply beta_trans; [apply beta_contract |].
  rewrite !subst_app, !substitute_shift, subst_V0. reflexivity.
Qed.
Lemma binary_delta_elim {n} (Γ : Ctx nat n) q b u v Q :
  0 < q -> (forall i j, i < q -> j < q -> b i j < q) ->
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  inhabited Γ (delta q u) -> inhabited Γ (delta q v) ->
  Typed Γ Q (Arrow (selector_type q) (𝓤 3)) ->
  (forall i, i < q -> inhabited Γ (app Q (lift_closed (point q i)))) ->
  inhabited Γ (app Q (app (app (lift_closed (binary_table q b)) u) v)).
Proof.
  intros Hq Hbound Hu Hv Hdu Hdv HQ Hpoints.
  assert (HA : Typed Γ (selector_type q) (𝓤 1)).
  { destruct q; [lia |apply selector_type_formation]. }
  pose proof (binary_in_context Γ q b) as Hop.
  pose proof (compose_left_typed Γ _ _ _ _ HA HQ Hop Hv) as HM.
  assert (HB : forall i, i < q -> inhabited Γ
    (app (compose_left (selector_type q) Q (lift_closed (binary_table q b)) v)
      (lift_closed (point q i)))).
  { intros i Hi. pose proof (point_in_context Γ q i) as HiD.
    assert (Hpart : Typed Γ (app (lift_closed (binary_table q b)) (lift_closed (point q i)))
      (Arrow (selector_type q) (selector_type q))).
    { eapply arrow_application; eassumption. }
    pose proof (compose_typed Γ _ _ _ HA HQ Hpart) as HN.
    assert (HC : forall j, j < q -> inhabited Γ
      (app (compose (selector_type q) Q (app (lift_closed (binary_table q b)) (lift_closed (point q i))))
        (lift_closed (point q j)))).
    { intros j Hj. destruct (Hpoints _ (Hbound i j Hi Hj)) as [p Hp].
      exists p. eapply tConv; [exact Hp | |].
      - eapply arrow_application; [exact HN |apply point_in_context].
      - symmetry. eapply beta_trans; [apply compose_beta |].
        apply beta_app; [reflexivity |].
        exact (rename_equiv empty_renaming _ _ (binary_table_action q b i j Hi Hj)). }
    destruct (delta_eliminate Γ q v _ Hdv HN HC) as [p Hp].
    exists p. eapply tConv; [exact Hp | |].
    - eapply arrow_application; [exact HM |exact HiD].
    - eapply beta_trans; [apply compose_beta |]. symmetry. apply compose_left_beta. }
  destruct (delta_eliminate Γ q u _ Hdu HM HB) as [p Hp].
  exists p. eapply tConv; [exact Hp | |apply compose_left_beta].
  eapply arrow_application; [exact HQ |].
  eapply arrow_application; [eapply arrow_application; [exact Hop |exact Hu] |exact Hv].
Qed.
Theorem delta_binary {n} (Γ : Ctx nat n) q b u v :
  0 < q -> (forall i j, i < q -> j < q -> b i j < q) ->
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  inhabited Γ (delta q u) -> inhabited Γ (delta q v) ->
  inhabited Γ (delta q (app (app (lift_closed (binary_table q b)) u) v)).
Proof.
  intros Hq Hbound Hu Hv Hdu Hdv.
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
      (app V0 (shift (app (app (lift_closed (binary_table q b)) u) v))))).
  { apply arrows_intro.
    - apply Forall_map. pose proof (points_typed Γ q) as Hxs.
      eapply Forall_impl; [|exact Hxs]. intros x Hx. exists 3.
      eapply arrow_application; [exact HV |].
      pose proof (weakening RankSorts _ _ QA Hx) as H.
      unfold shift in H. rewrite rename_selector_type in H. exact H.
    - intros m Δ f Hext Hargs.
      rewrite rename_application. unfold shift. rewrite !rename_application, !rename_lift_closed.
      apply binary_delta_elim; [exact Hq |exact Hbound | | | | | |].
      + pose proof (weakening RankSorts _ _ QA Hu) as H.
        pose proof (extension_typed _ _ _ _ _ Hext H) as H'.
        unfold shift in H'. rewrite !rename_selector_type in H'. exact H'.
      + pose proof (weakening RankSorts _ _ QA Hv) as H.
        pose proof (extension_typed _ _ _ _ _ Hext H) as H'.
        unfold shift in H'. rewrite !rename_selector_type in H'. exact H'.
      + pose proof (inhabited_shift Γ _ QA Hdu) as H.
        pose proof (extension_inhabited _ _ _ _ Hext H) as H'.
        unfold shift in H'. rewrite !rename_delta in H'. exact H'.
      + pose proof (inhabited_shift Γ _ QA Hdv) as H.
        pose proof (extension_inhabited _ _ _ _ Hext H) as H'.
        unfold shift in H'. rewrite !rename_delta in H'. exact H'.
      + pose proof (extension_typed _ _ _ _ _ Hext HV) as H.
        rewrite rename_arrow, rename_selector_type in H. exact H.
      + intros i Hi.
        assert (Hin : In (app (@V0 n) (shift (lift_closed (point q i))))
          (map (fun x => app V0 (shift x)) (points q))).
        { apply in_map_iff. exists (lift_closed (point q i)). split; [reflexivity |].
          unfold points. apply in_map_iff. exists i. split; [reflexivity |]. apply in_seq. lia. }
        specialize (Hargs _ Hin). rewrite rename_application in Hargs.
        unfold shift in Hargs. rewrite !rename_lift_closed in Hargs. exact Hargs. }
  destruct HB as [p Hp]. exists (lam QA p). exact (tLam HQA Hp).
Qed.
Corollary delta_addition {n} (Γ : Ctx nat n) q u v :
  0 < q -> Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  inhabited Γ (delta q u) -> inhabited Γ (delta q v) ->
  inhabited Γ (delta q (app (app (lift_closed (capped_addition q)) u) v)).
Proof.
  intros Hq Hu Hv Hdu Hdv. apply delta_binary; try assumption.
  intros i j Hi Hj. pose proof (Nat.le_min_r (i+j) (Nat.pred q)). lia.
Qed.
Corollary delta_multiplication {n} (Γ : Ctx nat n) q u v :
  0 < q -> Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  inhabited Γ (delta q u) -> inhabited Γ (delta q v) ->
  inhabited Γ (delta q (app (app (lift_closed (capped_multiplication q)) u) v)).
Proof.
  intros Hq Hu Hv Hdu Hdv. apply delta_binary; try assumption.
  intros i j Hi Hj. pose proof (Nat.le_min_r (i*j) (Nat.pred q)). lia.
Qed.
End BinaryObservations.
