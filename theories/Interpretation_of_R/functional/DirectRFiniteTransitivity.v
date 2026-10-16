(** Uniform closed transitivity certificates for the finite observations.
    The same construction serves equality and order, at every positive arity. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R.functional Require Import DirectRCodes.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRPositive
  DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp DirectRRelationTables
  DirectRFiniteLawElimination DirectRGuardedFiniteLaws.
Import ListNotations.
Module FiniteTransitivity.
Import Codes Core Structural NegativeLogic Positive FiniteTables FiniteObservations
  RelationTables GuardedFiniteLaws.

Definition body {n} q r (u v w : Term nat n) :=
  Arrow (Neg (relation_at q r u v))
    (Arrow (Neg (relation_at q r v w)) (Neg (relation_at q r u w))).
Lemma body_typed {n} (Γ : Ctx nat n) q r u v w :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ w (selector_type q) -> Typed Γ (body q r u v w) (𝓤 3).
Proof.
  intros Hu Hv Hw. unfold body. apply (arrow_formation _ _ _ 2 3).
  - apply neg_formation, relation_at_typed; assumption.
  - apply (arrow_formation _ _ _ 2 2); apply neg_formation, relation_at_typed; assumption.
Qed.
Lemma replace_body {m n} (f : Fin m -> Term nat n) q r u v w :
  replace f (body q r u v w) = body q r (replace f u) (replace f v) (replace f w).
Proof.
  unfold body, Neg. rewrite !replace_arrow, !replace_relation_at, !replace_lift_closed. reflexivity.
Qed.
Lemma rename_body {m n} (f : Fin m -> Fin n) q r u v w :
  rename f (body q r u v w) = body q r (rename f u) (rename f v) (rename f w).
Proof. rewrite rename_as_replace, replace_body, <- !rename_as_replace. reflexivity. Qed.
Definition family q r : closed_term :=
  lam (selector_type q) (lam (selector_type q) (lam (selector_type q)
    (body q r (shift (shift V0)) (shift V0) V0))).
Lemma family_typed q r :
  Typed ε (family q r) (Arrows (repeat (selector_type q) 3) (𝓤 3)).
Proof.
  change (Typed ε (family q r)
    (Arrow (selector_type q) (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 3))))).
  unfold family, Arrow, shift. rewrite !rename_product, !rename_selector_type.
  do 3 (apply (tLam (selector_type_formation q _))).
  apply body_typed.
  - pose proof (tV (ε & selector_type q & selector_type q & selector_type q)
      (fsucc (fsucc fzero))) as H.
    change (Typed (ε & selector_type q & selector_type q & selector_type q)
      (shift (shift V0)) (shift (shift (shift (selector_type q))))) in H.
    unfold shift in H. rewrite !rename_selector_type in H. exact H.
  - pose proof (tV (ε & selector_type q & selector_type q & selector_type q)
      (fsucc fzero)) as H.
    change (Typed (ε & selector_type q & selector_type q & selector_type q)
      (shift V0) (shift (shift (selector_type q)))) in H.
    unfold shift in H. rewrite !rename_selector_type in H. exact H.
  - apply selector_newest.
Qed.
Lemma family_beta {n} q r (u v w : Term nat n) :
  app (app (app (lift_closed (family q r)) u) v) w =ᵝ body q r u v w.
Proof.
  unfold family, lift_closed. cbn [rename].
  rewrite !rename_selector_type, rename_body.
  eapply beta_trans.
  - eapply beta_app; [eapply beta_app; [apply beta_contract |reflexivity] |reflexivity].
  - unfold subst at 1. cbn [replace]. rewrite !replace_selector_type, replace_body.
    change (app (app (lam (selector_type q) (lam (selector_type q)
      (body q r (shift (shift u)) (shift V0) V0))) v) w =ᵝ body q r u v w).
    eapply beta_trans; [eapply beta_app; [apply beta_contract |reflexivity] |].
    unfold subst at 1. cbn [replace]. rewrite replace_selector_type, replace_body,
      !replace_shift.
    cbn [replace V0 fin_match transpose]. rewrite replace_shift_substitution.
    eapply beta_trans; [apply beta_contract |].
    unfold subst. rewrite replace_body, !replace_shift_substitution.
    reflexivity.
Qed.
Lemma body_points {n} q r i j k : i < q -> j < q -> k < q ->
  @body n q r (lift_closed (point q i)) (lift_closed (point q j)) (lift_closed (point q k)) =ᵝ
    boolean_horn [r i j; r j k] (r i k).
Proof.
  intros Hi Hj Hk. unfold body, boolean_horn. cbn [map Arrows fold_right].
  apply Structural.arrow_beta; [apply FiniteUp.neg_beta, relation_at_points; assumption |].
  apply Structural.arrow_beta; apply FiniteUp.neg_beta, relation_at_points; assumption.
Qed.
Lemma point_branch q r i j k : i < q -> j < q -> k < q ->
  (r i j = true -> r j k = true -> r i k = true) ->
  Realizes (table_apply (family q r) [point q i; point q j; point q k]).
Proof.
  intros Hi Hj Hk Htrans. eapply FiniteUp.inhabited_conversion.
  - apply (boolean_horn_realized ε [r i j; r j k] (r i k)).
    intro H. inversion H as [|? ? Hij Htail]; subst.
    inversion Htail as [|? ? Hjk Hnil]; subst. apply Htrans; assumption.
  - eapply FiniteLawElimination.apply_terms_typed.
    + repeat constructor; apply point_typed.
    + exact (family_typed q r).
  - symmetry. cbn [table_apply fold_left].
    rewrite <- (lift_closed_zero (family q r)),
      <- (lift_closed_zero (point q i)), <- (lift_closed_zero (point q j)),
      <- (lift_closed_zero (point q k)).
    eapply beta_trans; [apply family_beta |apply body_points; assumption].
Qed.

Definition transitivity_type q r := guarded q 3 (family q r).
Definition expanded_type q r : closed_term :=
  Π (selector_type q) (Arrow (delta q V0)
    (Π (selector_type q) (Arrow (delta q V0)
      (Π (selector_type q) (Arrow (delta q V0)
        (body q r (shift (shift V0)) (shift V0) V0)))))).
Lemma transitivity_type_beta q r : transitivity_type q r =ᵝ expanded_type q r.
Proof.
  unfold transitivity_type, expanded_type.
  rewrite <- (lift_closed_zero (family q r)). cbn [guarded].
  do 3 (apply beta_pi; [reflexivity |]; apply Structural.arrow_beta; [reflexivity |]).
  unfold shift. rewrite !rename_application, !rename_lift_closed.
  apply family_beta.
Qed.
Lemma expanded_type_typed q r : 0 < q -> Typed ε (expanded_type q r) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold expanded_type.
  do 2 (apply (tPi (b:=5) (selector_type_formation (S q) _));
    apply (arrow_formation _ _ _ 4 5);
      [apply delta_formation; [lia |apply selector_newest] |]).
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 3);
    [apply delta_formation; [lia |apply selector_newest] |].
  apply body_typed.
  - pose proof (tV (ε & selector_type (S q) & selector_type (S q) & selector_type (S q))
      (fsucc (fsucc fzero))) as H.
    change (Typed (ε & selector_type (S q) & selector_type (S q) & selector_type (S q))
      (shift (shift V0)) (shift (shift (shift (selector_type (S q)))))) in H.
    unfold shift in H. rewrite !rename_selector_type in H. exact H.
  - pose proof (tV (ε & selector_type (S q) & selector_type (S q) & selector_type (S q))
      (fsucc fzero)) as H.
    change (Typed (ε & selector_type (S q) & selector_type (S q) & selector_type (S q))
      (shift V0) (shift (shift (selector_type (S q))))) in H.
    unfold shift in H. rewrite !rename_selector_type in H. exact H.
  - apply selector_newest.
Qed.
Theorem transitivity_realized q r :
  0 < q ->
  (forall i j k, i < q -> j < q -> k < q ->
    r i j = true -> r j k = true -> r i k = true) ->
  Realizes (transitivity_type q r).
Proof.
  intros Hq Hr. apply (guarded_finite_realized q 3 _ 3 Hq (Nat.le_refl 3) (family_typed q r)).
  intros [|i [|j [|k [|l rest]]]] Hlen Hb; cbn in Hlen; try discriminate.
  inversion Hb as [|? ? Hi Htail]; subst.
  inversion Htail as [|? ? Hj Htail']; subst.
  inversion Htail' as [|? ? Hk Hnil]; subst.
  apply point_branch; [exact Hi |exact Hj |exact Hk |apply Hr; assumption].
Qed.
Theorem expanded_transitivity_realized q r :
  0 < q ->
  (forall i j k, i < q -> j < q -> k < q ->
    r i j = true -> r j k = true -> r i k = true) ->
  Realizes (expanded_type q r).
Proof.
  intros Hq Hr. eapply FiniteUp.inhabited_conversion.
  - exact (transitivity_realized q r Hq Hr).
  - apply expanded_type_typed; exact Hq.
  - apply transitivity_type_beta.
Qed.
Corollary equality_transitivity_realized q :
  0 < q -> Realizes (expanded_type q Nat.eqb).
Proof.
  intro Hq. apply expanded_transitivity_realized; [exact Hq |].
  intros i j k Hi Hj Hk Hij Hjk. apply Nat.eqb_eq in Hij, Hjk.
  apply Nat.eqb_eq. congruence.
Qed.
Corollary order_transitivity_realized q :
  0 < q -> Realizes (expanded_type q Nat.leb).
Proof.
  intro Hq. apply expanded_transitivity_realized; [exact Hq |].
  intros i j k Hi Hj Hk Hij Hjk. apply Nat.leb_le in Hij, Hjk.
  apply Nat.leb_le. lia.
Qed.
End FiniteTransitivity.
