(** Guarded finite arithmetic equations compiled from numerical identities. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFiniteZeroLaws
  DirectRFiniteExpressions DirectRArithmetic.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRPositive
  DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp DirectRRelationTables
  DirectRFiniteLawElimination DirectRGuardedFiniteLaws.
Import ListNotations.
Module FiniteRecursionLaws.
Import Codes Core Structural NegativeLogic Positive FiniteTables FiniteObservations
  RelationTables GuardedFiniteLaws FiniteExpressions.
Definition body {n} q l r (u v : Term nat n) :=
  Neg (relation_at q Nat.eqb (denote q l u v) (denote q r u v)).
Lemma body_typed {n} (Γ : Ctx nat n) q l r u v :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (body q l r u v) (𝓤 2).
Proof. intros Hu Hv. apply neg_formation, relation_at_typed; apply denote_typed; assumption. Qed.
Lemma replace_body {m n} (f : Fin m -> Term nat n) q l r u v :
  replace f (body q l r u v) = body q l r (replace f u) (replace f v).
Proof.
  unfold body, Neg. rewrite replace_arrow, replace_relation_at, !replace_denote,
    replace_lift_closed. reflexivity.
Qed.
Lemma rename_body {m n} (f : Fin m -> Fin n) q l r u v :
  rename f (body q l r u v) = body q l r (rename f u) (rename f v).
Proof. rewrite rename_as_replace, replace_body, <- !rename_as_replace. reflexivity. Qed.
Definition family q l r : closed_term :=
  lam (selector_type q) (lam (selector_type q) (body q l r (shift V0) V0)).
Lemma family_typed q l r :
  Typed ε (family q l r) (Arrows (repeat (selector_type q) 2) (𝓤 2)).
Proof.
  change (Typed ε (family q l r) (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 2)))).
  unfold family, Arrow, shift. rewrite !rename_product, !rename_selector_type.
  do 2 (apply (tLam (selector_type_formation q _))).
  apply body_typed; [apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Lemma family_beta {n} q l r (u v : Term nat n) :
  app (app (lift_closed (family q l r)) u) v =ᵝ body q l r u v.
Proof.
  unfold family, lift_closed. cbn [rename]. rewrite !rename_selector_type, rename_body.
  eapply beta_trans; [eapply beta_app; [apply beta_contract |reflexivity] |].
  unfold subst at 1. cbn [replace]. rewrite replace_selector_type, replace_body.
  change (app (lam (selector_type q) (body q l r (shift u) V0)) v =ᵝ body q l r u v).
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_body, replace_shift_substitution. reflexivity.
Qed.
Definition expanded_type q l r : closed_term :=
  Π (selector_type q) (Arrow (delta q V0)
    (Π (selector_type q) (Arrow (delta q V0) (body q l r (shift V0) V0)))).
Lemma expanded_type_beta q l r : guarded q 2 (family q l r) =ᵝ expanded_type q l r.
Proof.
  unfold expanded_type. rewrite <- (lift_closed_zero (family q l r)). cbn [guarded].
  do 2 (apply beta_pi; [reflexivity |]; apply Structural.arrow_beta; [reflexivity |]).
  unfold shift. rewrite !rename_application, !rename_lift_closed. apply family_beta.
Qed.
Lemma expanded_type_typed q l r : 0 < q -> Typed ε (expanded_type q l r) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold expanded_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5); [apply delta_formation; [lia |apply selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2); [apply delta_formation; [lia |apply selector_newest] |].
  apply body_typed; [apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Theorem equation_realized q l r : 0 < q ->
  (forall i j, i < q -> j < q -> value q l i j = value q r i j) ->
  Realizes (expanded_type q l r).
Proof.
  intros Hq Heq. assert (H : Realizes (guarded q 2 (family q l r))).
  { apply (guarded_finite_realized q 2 _ 2 Hq (ltac:(lia)) (family_typed q l r)).
    intros [|i [|j [|k rest]]] Hlen Hb; cbn in Hlen; try discriminate.
    inversion Hb as [|? ? Hi Htail]; subst. inversion Htail as [|? ? Hj Hnil]; subst.
    assert (HB : inhabited ε (body q l r (point q i) (point q j))).
    { eapply FiniteUp.inhabited_conversion.
      - pose proof (negative_true ε q Nat.eqb (value q l i j) (value q r i j)
          (value_bound q l i j Hq Hi Hj) (value_bound q r i j Hq Hi Hj)
          (ltac:(apply Nat.eqb_eq; apply Heq; assumption))) as Hp.
        rewrite !lift_closed_zero in Hp. exact Hp.
      - apply body_typed; apply point_typed.
      - apply FiniteUp.neg_beta. symmetry. apply FiniteZeroLaws.relation_beta;
          apply denote_points; assumption. }
    eapply FiniteUp.inhabited_conversion; [exact HB | |].
    - eapply FiniteLawElimination.apply_terms_typed.
      + repeat constructor; apply point_typed.
      + exact (family_typed q l r).
    - symmetry. cbn [table_apply fold_left].
      rewrite <- (lift_closed_zero (family q l r)). apply family_beta. }
  eapply FiniteUp.inhabited_conversion; [exact H |apply expanded_type_typed; exact Hq |].
  apply expanded_type_beta.
Qed.
Theorem addition_successor_realized q : 0 < q ->
  Realizes (expanded_type q (addition (successor first) second)
    (successor (addition first second))).
Proof.
  intro Hq. apply equation_realized; [exact Hq |].
  intros i j Hi Hj. exact (CappedArithmetic.capped_add_succ (Nat.pred q) i j).
Qed.
Theorem multiplication_successor_realized q : 0 < q ->
  Realizes (expanded_type q (multiplication (successor first) second)
    (addition second (multiplication first second))).
Proof.
  intro Hq. apply equation_realized; [exact Hq |].
  intros i j Hi Hj. exact (CappedArithmetic.capped_mul_succ (Nat.pred q) i j).
Qed.
End FiniteRecursionLaws.
