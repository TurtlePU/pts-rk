(** Uniform zero equations in the original PTS, with the finite-domain guard
    retained. Numerical table equations are used only to discharge beta actions. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRStructural DirectRLogic DirectRPositive
  DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp DirectRUnary
  DirectRBinaryTables DirectRRelationTables DirectRFiniteLawElimination
  DirectRGuardedFiniteLaws DirectRFiniteBinaryCongruence.
Import ListNotations.
Module FiniteZeroLaws.
Import Codes Core Structural NegativeLogic Positive FiniteTables FiniteObservations
  BinaryTables RelationTables GuardedFiniteLaws.

Definition argument {n} q (is_zero : bool) (u : Term nat n) :=
  if is_zero then lift_closed (point q 0) else u.
Definition lhs {n} q op (right : bool) (u : Term nat n) :=
  FiniteBinaryCongruence.output op (argument q (negb right) u) (argument q right u).
Definition body {n} q op right result_zero (u : Term nat n) :=
  Neg (relation_at q Nat.eqb (lhs q op right u) (argument q result_zero u)).
Lemma argument_typed {n} (Γ : Ctx nat n) q b u :
  Typed Γ u (selector_type q) -> Typed Γ (argument q b u) (selector_type q).
Proof. intro H. destruct b; [apply point_typed_in_context |exact H]. Qed.
Lemma body_typed {n} (Γ : Ctx nat n) q op right result_zero u :
  Typed ε op (FiniteBinaryCongruence.operation_type q) ->
  Typed Γ u (selector_type q) -> Typed Γ (body q op right result_zero u) (𝓤 2).
Proof.
  intros Hop Hu. apply neg_formation, relation_at_typed.
  - apply FiniteBinaryCongruence.output_typed; [exact Hop | |]; apply argument_typed, Hu.
  - apply argument_typed, Hu.
Qed.
Lemma replace_argument {m n} (f : Fin m -> Term nat n) q b u :
  replace f (argument q b u) = argument q b (replace f u).
Proof. destruct b; [apply replace_lift_closed |reflexivity]. Qed.
Lemma replace_body {m n} (f : Fin m -> Term nat n) q op r z u :
  replace f (body q op r z u) = body q op r z (replace f u).
Proof.
  unfold body, Neg, lhs, FiniteBinaryCongruence.output.
  rewrite !replace_arrow, !replace_relation_at, !replace_application,
    !replace_lift_closed, !replace_argument. reflexivity.
Qed.
Lemma rename_body {m n} (f : Fin m -> Fin n) q op r z u :
  rename f (body q op r z u) = body q op r z (rename f u).
Proof. rewrite rename_as_replace, replace_body, <- rename_as_replace. reflexivity. Qed.
Definition family q op r z : closed_term := lam (selector_type q) (body q op r z V0).
Lemma family_typed q op r z : Typed ε op (FiniteBinaryCongruence.operation_type q) ->
  Typed ε (family q op r z) (Arrow (selector_type q) (𝓤 2)).
Proof.
  intro Hop. apply (tLam (selector_type_formation q ε)).
  apply body_typed; [exact Hop |apply selector_newest].
Qed.
Lemma family_beta {n} q op r z (u : Term nat n) :
  app (lift_closed (family q op r z)) u =ᵝ body q op r z u.
Proof.
  unfold family, lift_closed. cbn [rename]. rewrite rename_selector_type, rename_body.
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_body. reflexivity.
Qed.
Lemma relation_beta q r u v u' v' : u =ᵝ u' -> v =ᵝ v' ->
  @relation_at 0 q r u v =ᵝ relation_at q r u' v'.
Proof.
  intros Hu Hv. transitivity (app (app (relation_table q r) u) v).
  - symmetry. apply relation_table_beta.
  - transitivity (app (app (relation_table q r) u') v').
    + apply beta_app; [apply beta_app; [reflexivity |exact Hu] |exact Hv].
    + apply relation_table_beta.
Qed.
Definition expanded_type q op r z : closed_term :=
  Π (selector_type q) (Arrow (delta q V0) (body q op r z V0)).
Lemma expanded_type_beta q op r z : guarded q 1 (family q op r z) =ᵝ expanded_type q op r z.
Proof.
  unfold expanded_type. rewrite <- (lift_closed_zero (family q op r z)). cbn [guarded].
  apply beta_pi; [reflexivity |]. apply Unary.arrow_beta; [reflexivity |].
  rewrite <- lift_closed_shift. apply family_beta.
Qed.
Lemma expanded_type_typed q op r z : 0 < q ->
  Typed ε op (FiniteBinaryCongruence.operation_type q) ->
  Typed ε (expanded_type q op r z) (𝓤 5).
Proof.
  intros Hq Hop. destruct q as [|q]; [lia |].
  apply (tPi (b:=5) (selector_type_formation (S q) ε)).
  apply (arrow_formation _ _ _ 4 2).
  - apply delta_formation; [lia |apply selector_newest].
  - apply body_typed; [exact Hop |apply selector_newest].
Qed.
Theorem zero_law_realized q op r z : 0 < q ->
  Typed ε op (FiniteBinaryCongruence.operation_type q) ->
  (forall i, i < q -> lhs q op r (point q i) =ᵝ argument q z (point q i)) ->
  Realizes (expanded_type q op r z).
Proof.
  intros Hq Hop Haction. assert (H : Realizes (guarded q 1 (family q op r z))).
  { apply (guarded_finite_realized q 1 _ 2 Hq (ltac:(lia)) (family_typed q op r z Hop)).
    intros [|i [|j rest]] Hlen Hb; cbn in Hlen; try discriminate.
    inversion Hb as [|? ? Hi Hnil]; subst.
    assert (HB : inhabited ε (body q op r z (point q i))).
    { eapply FiniteUp.inhabited_conversion.
      - pose proof (negative_true ε q Nat.eqb (if z then 0 else i)
          (if z then 0 else i) (ltac:(destruct z; assumption))
          (ltac:(destruct z; assumption)) (Nat.eqb_refl _)) as Hp.
        rewrite !lift_closed_zero in Hp. exact Hp.
      - apply body_typed; [exact Hop |apply point_typed].
      - apply FiniteUp.neg_beta. symmetry. eapply beta_trans.
        + apply relation_beta; [apply Haction; exact Hi |reflexivity].
        + destruct z; unfold argument; rewrite ?lift_closed_zero; reflexivity. }
    eapply FiniteUp.inhabited_conversion; [exact HB | |].
    - cbn [table_apply fold_left]. eapply arrow_application;
        [apply family_typed; exact Hop |apply point_typed].
    - symmetry. cbn [table_apply fold_left].
      rewrite <- (lift_closed_zero (family q op r z)). apply family_beta. }
  eapply FiniteUp.inhabited_conversion; [exact H |apply expanded_type_typed; assumption |].
  apply expanded_type_beta.
Qed.
Corollary addition_zero_realized q : 0 < q ->
  Realizes (expanded_type q (capped_addition q) false false).
Proof.
  intro Hq. apply zero_law_realized; [exact Hq |apply capped_addition_typed |].
  intros i Hi. unfold lhs, argument, FiniteBinaryCongruence.output. rewrite !lift_closed_zero.
  eapply beta_trans; [apply capped_addition_action; [exact Hq |exact Hi] |].
  rewrite Nat.add_0_l, Nat.min_l by lia. reflexivity.
Qed.
Corollary multiplication_zero_left_realized q : 0 < q ->
  Realizes (expanded_type q (capped_multiplication q) false true).
Proof.
  intro Hq. apply zero_law_realized; [exact Hq |apply capped_multiplication_typed |].
  intros i Hi. unfold lhs, argument, FiniteBinaryCongruence.output. rewrite !lift_closed_zero.
  eapply beta_trans; [apply capped_multiplication_action; [exact Hq |exact Hi] |].
  rewrite Nat.mul_0_l, Nat.min_0_l. reflexivity.
Qed.
Corollary multiplication_zero_right_realized q : 0 < q ->
  Realizes (expanded_type q (capped_multiplication q) true true).
Proof.
  intro Hq. apply zero_law_realized; [exact Hq |apply capped_multiplication_typed |].
  intros i Hi. unfold lhs, argument, FiniteBinaryCongruence.output. rewrite !lift_closed_zero.
  eapply beta_trans; [apply capped_multiplication_action; [exact Hi |exact Hq] |].
  rewrite Nat.mul_0_r, Nat.min_0_l. reflexivity.
Qed.
End FiniteZeroLaws.
