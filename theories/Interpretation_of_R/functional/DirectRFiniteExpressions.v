(** Compositional beta evaluation of finite-table expressions in two variables.
    This syntax describes finite observations, not the interpreted domain D. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFiniteUnaryCongruence
  DirectRFiniteBinaryCongruence.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic
  DirectRFiniteTables DirectRBinaryTables DirectRRelationTables.
Module FiniteExpressions.
Import Codes Core Structural NegativeLogic FiniteTables BinaryTables RelationTables.
Inductive expression :=
| zero | first | second
| successor (e : expression)
| addition (e f : expression)
| multiplication (e f : expression).
Fixpoint denote {n} q e (u v : Term nat n) : Term nat n :=
  match e with
  | zero => lift_closed (point q 0)
  | first => u
  | second => v
  | successor e => app (lift_closed (capped_successor q)) (denote q e u v)
  | addition e f => app (app (lift_closed (capped_addition q)) (denote q e u v)) (denote q f u v)
  | multiplication e f => app (app (lift_closed (capped_multiplication q)) (denote q e u v)) (denote q f u v)
  end.
Fixpoint value q e i j : nat :=
  match e with
  | zero => 0
  | first => i
  | second => j
  | successor e => Nat.min (S (value q e i j)) (Nat.pred q)
  | addition e f => Nat.min (value q e i j + value q f i j) (Nat.pred q)
  | multiplication e f => Nat.min (value q e i j * value q f i j) (Nat.pred q)
  end.
Lemma denote_typed {n} (Γ : Ctx nat n) q e u v :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (denote q e u v) (selector_type q).
Proof.
  intros Hu Hv. induction e; cbn [denote].
  - apply point_typed_in_context.
  - exact Hu.
  - exact Hv.
  - apply FiniteUnaryCongruence.output_typed; [apply capped_successor_typed |exact IHe].
  - apply FiniteBinaryCongruence.output_typed; [apply capped_addition_typed |exact IHe1 |exact IHe2].
  - apply FiniteBinaryCongruence.output_typed; [apply capped_multiplication_typed |exact IHe1 |exact IHe2].
Qed.
Lemma replace_denote {m n} (f : Fin m -> Term nat n) q e u v :
  replace f (denote q e u v) = denote q e (replace f u) (replace f v).
Proof.
  induction e; cbn [denote]; rewrite ?replace_application, ?replace_application,
    ?replace_lift_closed, ?IHe, ?IHe1, ?IHe2; reflexivity.
Qed.
Lemma value_bound q e i j : 0 < q -> i < q -> j < q -> value q e i j < q.
Proof.
  intros Hq Hi Hj. induction e; cbn [value]; try assumption;
    try (eapply Nat.le_lt_trans; [apply Nat.le_min_r |lia]); lia.
Qed.
Theorem denote_points q e i j : 0 < q -> i < q -> j < q ->
  denote q e (point q i) (point q j) =ᵝ point q (value q e i j).
Proof.
  intros Hq Hi Hj. induction e; cbn [denote value]; rewrite ?lift_closed_zero;
    try reflexivity.
  - eapply beta_trans; [eapply beta_app; [reflexivity |exact IHe] |].
    apply capped_successor_action, value_bound; assumption.
  - eapply beta_trans; [eapply beta_app; [eapply beta_app;
      [reflexivity |exact IHe1] |exact IHe2] |].
    apply capped_addition_action; apply value_bound; assumption.
  - eapply beta_trans; [eapply beta_app; [eapply beta_app;
      [reflexivity |exact IHe1] |exact IHe2] |].
    apply capped_multiplication_action; apply value_bound; assumption.
Qed.
End FiniteExpressions.
