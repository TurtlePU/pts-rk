(** Guarded relation certificates for functional finite observations.
    This module is being extended to the full arithmetic law telescope. *)
From Stdlib Require Import Arith.PeanoNat Lia Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R.functional Require Import DirectRCodes.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic
  DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp DirectRRelationTables
  DirectRFiniteLawElimination.
Import ListNotations.
Module FunctionalFiniteLaws.
Import Codes Core Structural NegativeLogic FiniteTables FiniteObservations RelationTables.
Definition reflexivity_family q r : closed_term :=
  lam (selector_type q) (Neg (relation_at q r V0 V0)).
Lemma reflexivity_family_typed q r : 0 < q ->
  Typed ε (reflexivity_family q r) (Arrow (selector_type q) (𝓤 2)).
Proof.
  intro Hq. unfold reflexivity_family. apply (tLam (selector_type_formation q ε)).
  apply neg_formation, relation_at_typed;
    pose proof (tV (ε & selector_type q) fzero) as H;
    change (Typed (ε & selector_type q) V0 (shift (selector_type q))) in H;
    unfold shift in H; rewrite rename_selector_type in H; exact H.
Qed.
Lemma reflexivity_family_beta {n} q r (u : Term nat n) :
  app (lift_closed (reflexivity_family q r)) u =ᵝ Neg (relation_at q r u u).
Proof.
  unfold reflexivity_family, lift_closed. cbn [rename].
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_rename. unfold Neg.
  rewrite replace_arrow, replace_lift_closed, replace_relation_at.
  reflexivity.
Qed.
Theorem relation_reflexivity {n} (Γ : Ctx nat n) q r u :
  0 < q -> (forall i, i < q -> r i i = true) ->
  Typed Γ u (selector_type q) -> inhabited Γ (delta q u) ->
  inhabited Γ (Neg (relation_at q r u u)).
Proof.
  intros Hq Hr Hu Hd.
  pose proof (lift_closed_typed Γ _ _ (reflexivity_family_typed q r Hq)) as HP.
  unfold lift_closed at 2 in HP. rewrite rename_arrow, rename_selector_type in HP.
  assert (HB : forall i, i < q -> inhabited Γ
    (app (lift_closed (reflexivity_family q r)) (lift_closed (point q i)))).
  { intros i Hi. eapply FiniteUp.inhabited_conversion.
    - apply (negative_true Γ q r i i Hi Hi (Hr i Hi)).
    - eapply arrow_application; [exact HP |apply point_in_context].
    - symmetry. apply reflexivity_family_beta. }
  pose proof (FiniteLawElimination.delta_eliminate_lower Γ q u _ 2 Hq
    (ltac:(lia)) Hu Hd HP HB) as H.
  eapply FiniteUp.inhabited_conversion; [exact H | |apply reflexivity_family_beta].
  apply neg_formation, relation_at_typed; exact Hu.
Qed.
Definition reflexivity_type q r : closed_term :=
  Π (selector_type q) (Arrow (delta q V0) (Neg (relation_at q r V0 V0))).
Theorem reflexivity_realized q r :
  0 < q -> (forall i, i < q -> r i i = true) -> Realizes (reflexivity_type q r).
Proof.
  intros Hq Hr.
  assert (Hu : Typed (ε & selector_type q) V0 (selector_type q)).
  { pose proof (tV (ε & selector_type q) fzero) as H.
    change (Typed (ε & selector_type q) V0 (shift (selector_type q))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H. }
  assert (HB : inhabited (ε & selector_type q) (Arrow (delta q V0) (Neg (relation_at q r V0 V0)))).
  { apply arrow_intro; [exists 4; apply delta_formation; assumption |].
    rewrite shift_neg. unfold shift. rewrite rename_as_replace, replace_relation_at.
    apply relation_reflexivity; [exact Hq |exact Hr | |].
    - pose proof (weakening RankSorts _ _ (delta q V0) Hu) as H.
      unfold shift in H. rewrite rename_selector_type in H. exact H.
    - pose proof (newest (ε & selector_type q) (delta q V0)) as H.
      unfold shift in H. rewrite rename_delta in H. exact H. }
  destruct HB as [p Hp]. exists (lam (selector_type q) p).
  exact (tLam (selector_type_formation q ε) Hp).
Qed.
Corollary equality_reflexivity_realized q : 0 < q -> Realizes (reflexivity_type q Nat.eqb).
Proof. intro Hq. apply reflexivity_realized; [exact Hq |intros i Hi; apply Nat.eqb_refl]. Qed.
Corollary order_reflexivity_realized q : 0 < q -> Realizes (reflexivity_type q Nat.leb).
Proof. intro Hq. apply reflexivity_realized; [exact Hq |intros i Hi; apply Nat.leb_refl]. Qed.

Definition symmetry_body {n} q r (u v : Term nat n) :=
  Arrow (Neg (relation_at q r u v)) (Neg (relation_at q r v u)).
Definition symmetry_family q r : closed_term :=
  lam (selector_type q) (lam (selector_type q) (symmetry_body q r (shift V0) V0)).
Lemma symmetry_body_typed {n} (Γ : Ctx nat n) q r u v :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (symmetry_body q r u v) (𝓤 3).
Proof.
  intros Hu Hv. unfold symmetry_body. apply (arrow_formation _ _ _ 2 2);
    apply neg_formation, relation_at_typed; assumption.
Qed.
Lemma symmetry_family_typed q r : Typed ε (symmetry_family q r)
  (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 3))).
Proof.
  unfold symmetry_family, Arrow, shift. rewrite !rename_product, !rename_selector_type.
  apply (tLam (selector_type_formation q ε)).
  apply (tLam (selector_type_formation q (ε & selector_type q))).
  apply symmetry_body_typed.
  - pose proof (tV (ε & selector_type q & selector_type q) (fsucc fzero)) as H.
    change (Typed (ε & selector_type q & selector_type q) (shift V0)
      (shift (shift (selector_type q)))) in H.
    unfold shift in H. rewrite !rename_selector_type in H. exact H.
  - pose proof (tV (ε & selector_type q & selector_type q) fzero) as H.
    change (Typed (ε & selector_type q & selector_type q) V0 (shift (selector_type q))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma replace_symmetry_body {m n} (f : Fin m -> Term nat n) q r u v :
  replace f (symmetry_body q r u v) = symmetry_body q r (replace f u) (replace f v).
Proof.
  unfold symmetry_body, Neg. rewrite !replace_arrow, !replace_relation_at,
    !replace_lift_closed. reflexivity.
Qed.
Lemma symmetry_family_beta {n} q r (u v : Term nat n) :
  app (app (lift_closed (symmetry_family q r)) u) v =ᵝ symmetry_body q r u v.
Proof.
  unfold symmetry_family, lift_closed. cbn [rename].
  eapply beta_trans; [eapply beta_app; [apply beta_contract |reflexivity] |].
  unfold subst at 1. cbn [replace].
  rewrite !replace_rename, replace_symmetry_body.
  cbn [replace V0 fin_match transpose weak].
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_symmetry_body.
  change (symmetry_body q r (subst (shift u) v) v =ᵝ symmetry_body q r u v).
  rewrite substitute_shift. reflexivity.
Qed.
Lemma symmetry_points {n} (Γ : Ctx nat n) q r i j :
  i < q -> j < q -> (r i j = true -> r j i = true) ->
  inhabited Γ (symmetry_body q r (lift_closed (point q i)) (lift_closed (point q j))).
Proof.
  intros Hi Hj Hr. unfold symmetry_body.
  apply arrow_intro; [exists 2; apply neg_formation, relation_at_typed; apply point_in_context |].
  rewrite shift_neg. unfold shift. rewrite rename_as_replace, replace_relation_at,
    !replace_lift_closed.
  destruct (r i j) eqn:Hrij.
  - apply negative_true; [exact Hj |exact Hi |apply Hr; reflexivity].
  - unfold Neg. apply arrow_intro.
    + exists 1. apply relation_at_typed; apply point_in_context.
    + apply inhabited_shift.
      eapply negative_false; [exact Hi |exact Hj |exact Hrij |].
      pose proof (newest Γ (Neg (relation_at q r (lift_closed (point q i))
        (lift_closed (point q j))))) as H.
      rewrite shift_neg in H. unfold shift in H.
      rewrite rename_as_replace, replace_relation_at, !replace_lift_closed in H. exact H.
Qed.
Theorem relation_symmetry {n} (Γ : Ctx nat n) q r u v :
  0 < q -> (forall i j, i < q -> j < q -> r i j = true -> r j i = true) ->
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  inhabited Γ (delta q u) -> inhabited Γ (delta q v) ->
  inhabited Γ (symmetry_body q r u v).
Proof.
  intros Hq Hr Hu Hv Hdu Hdv.
  pose proof (lift_closed_typed Γ _ _ (symmetry_family_typed q r)) as HP.
  unfold lift_closed at 2 in HP. rewrite !rename_arrow, !rename_selector_type in HP.
  assert (HB : forall indices, length indices = 2 -> Forall (fun i => i < q) indices ->
    inhabited Γ (table_apply (lift_closed (symmetry_family q r))
      (map (fun i => lift_closed (point q i)) indices))).
  { intros [|i [|j [|k rest]]] Hlen Hbounds; cbn in Hlen; try discriminate.
    inversion Hbounds as [|? ? Hi Htail]; subst.
    inversion Htail as [|? ? Hj Hnil]; subst.
    cbn [map table_apply fold_left]. eapply FiniteUp.inhabited_conversion.
    - apply symmetry_points; [exact Hi |exact Hj |apply Hr; assumption].
    - eapply arrow_application; [eapply arrow_application; [exact HP |apply point_in_context] |apply point_in_context].
    - symmetry. apply symmetry_family_beta. }
  pose proof (FiniteLawElimination.delta_eliminate_arguments Γ q [u;v] _ 3 Hq
    (Nat.le_refl 3) (Forall_cons u Hu (Forall_cons v Hv (Forall_nil _)))
    (Forall_cons u Hdu (Forall_cons v Hdv (Forall_nil _))) HP HB) as H.
  eapply FiniteUp.inhabited_conversion; [exact H |apply symmetry_body_typed; assumption |].
  apply symmetry_family_beta.
Qed.
Lemma rename_symmetry_body {m n} (f : Fin m -> Fin n) q r u v :
  rename f (symmetry_body q r u v) = symmetry_body q r (rename f u) (rename f v).
Proof. rewrite rename_as_replace, replace_symmetry_body, <- !rename_as_replace. reflexivity. Qed.
Definition symmetry_type q r : closed_term :=
  Π (selector_type q) (Arrow (delta q V0)
    (Π (selector_type q) (Arrow (delta q V0) (symmetry_body q r (shift V0) V0)))).
Theorem symmetry_realized q r :
  0 < q -> (forall i j, i < q -> j < q -> r i j = true -> r j i = true) ->
  Realizes (symmetry_type q r).
Proof.
  intros Hq Hr. unfold symmetry_type.
  assert (Hu : Typed (ε & selector_type q) V0 (selector_type q)).
  { pose proof (tV (ε & selector_type q) fzero) as H.
    change (Typed (ε & selector_type q) V0 (shift (selector_type q))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H. }
  assert (HB : inhabited (ε & selector_type q) (Arrow (delta q V0)
    (Π (selector_type q) (Arrow (delta q V0) (symmetry_body q r (shift V0) V0))))).
  { apply arrow_intro; [exists 4; apply delta_formation; assumption |].
    unfold shift. rewrite rename_product, rename_selector_type, rename_arrow,
      rename_delta, rename_symmetry_body.
    apply product_intro; [eexists; apply selector_type_formation |].
    change (inhabited (ε & selector_type q & delta q V0 & selector_type q)
      (Arrow (delta q V0) (symmetry_body q r (var (fsucc (fsucc fzero))) V0))).
    apply arrow_intro.
    - exists 4. apply delta_formation; [exact Hq |].
      pose proof (tV (ε & selector_type q & delta q V0 & selector_type q) fzero) as H.
      cbn [index ctx_top fin_match] in H. unfold shift in H. rewrite rename_selector_type in H. exact H.
    - unfold shift. rewrite rename_symmetry_body.
      apply relation_symmetry; [exact Hq |exact Hr | | | |].
      + pose proof (tV (ε & selector_type q & delta q V0 & selector_type q & delta q V0)
          (fsucc (fsucc (fsucc fzero)))) as H.
        change (Typed (ε & selector_type q & delta q V0 & selector_type q & delta q V0)
          (var (fsucc (fsucc (fsucc fzero))))
          (shift (shift (shift (shift (selector_type q)))))) in H.
        unfold shift in H. rewrite !rename_selector_type in H. exact H.
      + pose proof (tV (ε & selector_type q & delta q V0 & selector_type q & delta q V0)
          (fsucc fzero)) as H.
        change (Typed (ε & selector_type q & delta q V0 & selector_type q & delta q V0)
          (var (fsucc fzero)) (shift (shift (selector_type q)))) in H.
        unfold shift in H. rewrite !rename_selector_type in H. exact H.
      + eexists. pose proof (tV (ε & selector_type q & delta q V0 & selector_type q & delta q V0)
          (fsucc (fsucc fzero))) as H.
        change (Typed (ε & selector_type q & delta q V0 & selector_type q & delta q V0)
          (var (fsucc (fsucc fzero))) (shift (shift (shift (delta q V0))))) in H.
        unfold shift in H. rewrite !rename_delta in H. exact H.
      + eexists. pose proof (tV (ε & selector_type q & delta q V0 & selector_type q & delta q V0)
          fzero) as H.
        cbn [index ctx_top ctx_pred fin_match] in H.
        unfold shift in H. rewrite rename_delta in H. exact H. }
  destruct HB as [p Hp]. exists (lam (selector_type q) p).
  exact (tLam (selector_type_formation q ε) Hp).
Qed.
Corollary equality_symmetry_realized q : 0 < q -> Realizes (symmetry_type q Nat.eqb).
Proof.
  intro Hq. apply symmetry_realized; [exact Hq |].
  intros i j Hi Hj H. rewrite Nat.eqb_sym. exact H.
Qed.
End FunctionalFiniteLaws.
