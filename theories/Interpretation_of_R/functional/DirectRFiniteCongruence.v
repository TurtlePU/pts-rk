(** Finite relation congruence in both arguments, with all four domain guards.
    In particular this supplies the observation's order-congruence law. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R.functional Require Import DirectRCodes.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRPositive
  DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp DirectRRelationTables
  DirectRFiniteLawElimination DirectRGuardedFiniteLaws.
Import ListNotations.
Module FiniteCongruence.
Import Codes Core Structural NegativeLogic Positive FiniteTables FiniteObservations
  RelationTables GuardedFiniteLaws.

Definition body {n} q r (u u' v v' : Term nat n) :=
  Arrow (Neg (relation_at q Nat.eqb u u'))
    (Arrow (Neg (relation_at q Nat.eqb v v'))
      (Arrow (Neg (relation_at q r u v)) (Neg (relation_at q r u' v')))).
Lemma body_typed {n} (Γ : Ctx nat n) q r u u' v v' :
  Typed Γ u (selector_type q) -> Typed Γ u' (selector_type q) ->
  Typed Γ v (selector_type q) -> Typed Γ v' (selector_type q) ->
  Typed Γ (body q r u u' v v') (𝓤 3).
Proof.
  intros Hu Hu' Hv Hv'. unfold body.
  do 2 (apply (arrow_formation _ _ _ 2 3);
    [apply neg_formation, relation_at_typed; assumption |]).
  apply (arrow_formation _ _ _ 2 2); apply neg_formation, relation_at_typed; assumption.
Qed.
Lemma replace_body {m n} (f : Fin m -> Term nat n) q r u u' v v' :
  replace f (body q r u u' v v') =
    body q r (replace f u) (replace f u') (replace f v) (replace f v').
Proof.
  unfold body, Neg. rewrite !replace_arrow, !replace_relation_at, !replace_lift_closed. reflexivity.
Qed.
Lemma rename_body {m n} (f : Fin m -> Fin n) q r u u' v v' :
  rename f (body q r u u' v v') =
    body q r (rename f u) (rename f u') (rename f v) (rename f v').
Proof. rewrite rename_as_replace, replace_body, <- !rename_as_replace. reflexivity. Qed.
Definition family q r : closed_term :=
  lam (selector_type q) (lam (selector_type q) (lam (selector_type q)
    (lam (selector_type q) (body q r
      (shift (shift (shift V0))) (shift (shift V0)) (shift V0) V0)))).
Lemma family_typed q r :
  Typed ε (family q r) (Arrows (repeat (selector_type q) 4) (𝓤 3)).
Proof.
  change (Typed ε (family q r) (Arrow (selector_type q) (Arrow (selector_type q)
    (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 3)))))).
  unfold family, Arrow, shift. rewrite !rename_product, !rename_selector_type.
  do 4 (apply (tLam (selector_type_formation q _))).
  apply body_typed; repeat apply selector_weaken; apply selector_newest.
Qed.
Lemma family_beta {n} q r (u u' v v' : Term nat n) :
  app (app (app (app (lift_closed (family q r)) u) u') v) v' =ᵝ body q r u u' v v'.
Proof.
  unfold family, lift_closed. cbn [rename]. rewrite !rename_selector_type, rename_body.
  eapply beta_trans.
  - eapply beta_app; [eapply beta_app; [eapply beta_app;
      [apply beta_contract |reflexivity] |reflexivity] |reflexivity].
  - unfold subst at 1. cbn [replace]. rewrite !replace_selector_type, replace_body.
    change (app (app (app (lam (selector_type q) (lam (selector_type q)
      (lam (selector_type q) (body q r (shift (shift (shift u)))
        (shift (shift V0)) (shift V0) V0)))) u') v) v' =ᵝ body q r u u' v v').
    eapply beta_trans; [eapply beta_app; [eapply beta_app;
      [apply beta_contract |reflexivity] |reflexivity] |].
    unfold subst at 1. cbn [replace]. rewrite !replace_selector_type, replace_body, !replace_shift.
    cbn [replace V0 fin_match transpose]. rewrite replace_shift_substitution.
    eapply beta_trans; [eapply beta_app; [apply beta_contract |reflexivity] |].
    unfold subst at 1. cbn [replace]. rewrite replace_selector_type, replace_body, !replace_shift.
    cbn [replace V0 fin_match transpose]. rewrite !replace_shift_substitution.
    eapply beta_trans; [apply beta_contract |].
    unfold subst. rewrite replace_body, !replace_shift_substitution. reflexivity.
Qed.
Lemma body_points {n} q r i i' j j' : i < q -> i' < q -> j < q -> j' < q ->
  @body n q r (lift_closed (point q i)) (lift_closed (point q i'))
    (lift_closed (point q j)) (lift_closed (point q j')) =ᵝ
  boolean_horn [Nat.eqb i i'; Nat.eqb j j'; r i j] (r i' j').
Proof.
  intros Hi Hi' Hj Hj'. unfold body, boolean_horn. cbn [map Arrows fold_right].
  do 2 (apply Structural.arrow_beta; [apply FiniteUp.neg_beta, relation_at_points; assumption |]).
  apply Structural.arrow_beta; apply FiniteUp.neg_beta, relation_at_points; assumption.
Qed.
Lemma point_branch q r i i' j j' : i < q -> i' < q -> j < q -> j' < q ->
  Realizes (table_apply (family q r) [point q i; point q i'; point q j; point q j']).
Proof.
  intros Hi Hi' Hj Hj'. eapply FiniteUp.inhabited_conversion.
  - apply (boolean_horn_realized ε [Nat.eqb i i'; Nat.eqb j j'; r i j] (r i' j')).
    intro H. inversion H as [|? ? Hii Htail]; subst.
    inversion Htail as [|? ? Hjj Htail']; subst.
    inversion Htail' as [|? ? Hij Hnil]; subst.
    apply Nat.eqb_eq in Hii, Hjj. subst. exact Hij.
  - eapply FiniteLawElimination.apply_terms_typed.
    + repeat constructor; apply point_typed.
    + exact (family_typed q r).
  - symmetry. cbn [table_apply fold_left].
    rewrite <- (lift_closed_zero (family q r)), <- (lift_closed_zero (point q i)),
      <- (lift_closed_zero (point q i')), <- (lift_closed_zero (point q j)),
      <- (lift_closed_zero (point q j')).
    eapply beta_trans; [apply family_beta |apply body_points; assumption].
Qed.
Definition congruence_type q r := guarded q 4 (family q r).
Definition expanded_type q r : closed_term :=
  Π (selector_type q) (Arrow (delta q V0) (Π (selector_type q) (Arrow (delta q V0)
    (Π (selector_type q) (Arrow (delta q V0) (Π (selector_type q) (Arrow (delta q V0)
      (body q r (shift (shift (shift V0))) (shift (shift V0)) (shift V0) V0)))))))).
Lemma congruence_type_beta q r : congruence_type q r =ᵝ expanded_type q r.
Proof.
  unfold congruence_type, expanded_type.
  rewrite <- (lift_closed_zero (family q r)). cbn [guarded].
  do 4 (apply beta_pi; [reflexivity |]; apply Structural.arrow_beta; [reflexivity |]).
  unfold shift. rewrite !rename_application, !rename_lift_closed. apply family_beta.
Qed.
Lemma expanded_type_typed q r : 0 < q -> Typed ε (expanded_type q r) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold expanded_type.
  do 3 (apply (tPi (b:=5) (selector_type_formation (S q) _));
    apply (arrow_formation _ _ _ 4 5);
      [apply delta_formation; [lia |apply selector_newest] |]).
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 3);
    [apply delta_formation; [lia |apply selector_newest] |].
  apply body_typed; repeat apply selector_weaken; apply selector_newest.
Qed.
Theorem relation_congruence_realized q r : 0 < q -> Realizes (expanded_type q r).
Proof.
  intro Hq.
  assert (H : Realizes (congruence_type q r)).
  { apply (guarded_finite_realized q 4 _ 3 Hq (Nat.le_refl 3) (family_typed q r)).
    intros [|i [|i' [|j [|j' [|k rest]]]]] Hlen Hb; cbn in Hlen; try discriminate.
    inversion Hb as [|? ? Hi Htail]; subst.
    inversion Htail as [|? ? Hi' Htail']; subst.
    inversion Htail' as [|? ? Hj Htail'']; subst.
    inversion Htail'' as [|? ? Hj' Hnil]; subst.
    apply point_branch; assumption. }
  eapply FiniteUp.inhabited_conversion; [exact H |apply expanded_type_typed; exact Hq |].
  apply congruence_type_beta.
Qed.
Corollary order_congruence_realized q : 0 < q -> Realizes (expanded_type q Nat.leb).
Proof. apply relation_congruence_realized. Qed.
End FiniteCongruence.
