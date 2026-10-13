(** Uniform beta fold equations for the actual unary Church numerals. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRStructural DirectRSymbolic DirectRUnary
  DirectRFiniteTables.

Module UnaryEvaluation.
Import Codes Core Structural FiniteTables.
Definition evaluate {n} (d X z s : Term nat n) := app (app (app d X) z) s.

(** Prove the fixed open schema, then substitute arbitrary scoped terms.
    The schema variables are not assumed typed or canonical. *)
Lemma zero_schema :
  evaluate (lift_closed Unary.zero) (@var nat 3 (fsucc (fsucc fzero)))
    (var (fsucc fzero)) V0 =ᵝ var (fsucc fzero).
Proof.
  match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end.
Qed.
Lemma successor_schema :
  evaluate (app (lift_closed Unary.successor) (@var nat 4 (fsucc (fsucc (fsucc fzero)))))
    (var (fsucc (fsucc fzero))) (var (fsucc fzero)) V0 =ᵝ
  app V0 (evaluate (var (fsucc (fsucc (fsucc fzero))))
    (var (fsucc (fsucc fzero))) (var (fsucc fzero)) V0).
Proof.
  match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end.
Qed.
Lemma evaluate_zero {n} (X z s : Term nat n) :
  evaluate (lift_closed Unary.zero) X z s =ᵝ z.
Proof.
  pose proof (replace_equiv
    (fin_match s (fin_match z (fin_match X (fun i : Fin 0 => match i with end))))
    _ _ zero_schema) as H.
  unfold evaluate in H. rewrite !replace_application, replace_lift_closed in H. exact H.
Qed.
Lemma evaluate_successor {n} (d X z s : Term nat n) :
  evaluate (app (lift_closed Unary.successor) d) X z s =ᵝ app s (evaluate d X z s).
Proof.
  pose proof (replace_equiv
    (fin_match s (fin_match z (fin_match X (fin_match d (fun i : Fin 0 => match i with end)))))
    _ _ successor_schema) as H.
  unfold evaluate in H. rewrite !replace_application, replace_lift_closed in H. exact H.
Qed.
Fixpoint iterations {n} k (z s : Term nat n) : Term nat n :=
  match k with 0 => z | S k => app s (iterations k z s) end.
Theorem numeral_evaluation k : forall n (X z s : Term nat n),
  evaluate (lift_closed (Unary.numeral k)) X z s =ᵝ iterations k z s.
Proof.
  induction k as [|k IH]; intros n X z s; cbn [Unary.numeral iterations].
  - apply evaluate_zero.
  - change (evaluate (app (lift_closed Unary.successor)
      (lift_closed (Unary.numeral k))) X z s =ᵝ app s (iterations k z s)).
    eapply beta_trans; [apply evaluate_successor |]. apply beta_app; [reflexivity |apply IH].
Qed.
Lemma finite_iterations q k :
  iterations k (point q 0) (capped_successor q) = iterate q k.
Proof. induction k; cbn [iterations iterate]; congruence. Qed.
Theorem finite_numeral_evaluation c k :
  evaluate (Unary.numeral k) (selector_type (S c)) (point (S c) 0)
    (capped_successor (S c)) =ᵝ point (S c) (Nat.min k c).
Proof.
  rewrite <- (lift_closed_zero (Unary.numeral k)).
  eapply beta_trans; [apply numeral_evaluation |]. rewrite finite_iterations.
  apply iterate_computation.
Qed.
End UnaryEvaluation.
