(** Beta fold equations for the original four-constructor carrier. *)
From Stdlib Require Import Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRStructural DirectRSymbolic DirectRFiniteTables
  DirectRBinaryTables DirectRUnaryEvaluation.
Module FunctionalEvaluation.
Import Codes Core Structural FiniteTables BinaryTables.
Definition evaluate {n} (d X z s a m : Term nat n) :=
  app (app (app (app (app d X) z) s) a) m.
Lemma zero_schema :
  evaluate (lift_closed zero) (@var nat 5 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 5 (fsucc (fsucc (fsucc fzero)))) (@var nat 5 (fsucc (fsucc fzero))) (@var nat 5 (fsucc fzero)) (@var nat 5 fzero) =ᵝ (@var nat 5 (fsucc (fsucc (fsucc fzero)))).
Proof.
  match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end.
Qed.
Lemma evaluate_zero {n} (X z s a m : Term nat n) :
  evaluate (lift_closed zero) X z s a m =ᵝ z.
Proof.
  pose proof (replace_equiv (fin_match m (fin_match a (fin_match s (fin_match z (fin_match X (fun i : Fin 0 => match i with end)))))) _ _ zero_schema) as H.
  unfold evaluate in H. rewrite !replace_application, !replace_lift_closed in H. exact H.
Qed.
Lemma successor_schema :
  evaluate (app (lift_closed successor) (@var nat 6 (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))) (@var nat 6 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 6 (fsucc (fsucc (fsucc fzero)))) (@var nat 6 (fsucc (fsucc fzero))) (@var nat 6 (fsucc fzero)) (@var nat 6 fzero) =ᵝ app (@var nat 6 (fsucc (fsucc fzero))) (evaluate (@var nat 6 (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))) (@var nat 6 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 6 (fsucc (fsucc (fsucc fzero)))) (@var nat 6 (fsucc (fsucc fzero))) (@var nat 6 (fsucc fzero)) (@var nat 6 fzero)).
Proof.
  match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end.
Qed.
Lemma evaluate_successor {n} (d X z s a m : Term nat n) :
  evaluate (app (lift_closed successor) d) X z s a m =ᵝ app s (evaluate d X z s a m).
Proof.
  pose proof (replace_equiv (fin_match m (fin_match a (fin_match s (fin_match z (fin_match X (fin_match d (fun i : Fin 0 => match i with end))))))) _ _ successor_schema) as H.
  unfold evaluate in H. rewrite !replace_application, !replace_lift_closed in H. exact H.
Qed.
Lemma addition_schema :
  evaluate (app (app (lift_closed addition) (@var nat 7 (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))) (@var nat 7 (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))) (@var nat 7 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 7 (fsucc (fsucc (fsucc fzero)))) (@var nat 7 (fsucc (fsucc fzero))) (@var nat 7 (fsucc fzero)) (@var nat 7 fzero) =ᵝ app (app (@var nat 7 (fsucc fzero)) (evaluate (@var nat 7 (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))) (@var nat 7 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 7 (fsucc (fsucc (fsucc fzero)))) (@var nat 7 (fsucc (fsucc fzero))) (@var nat 7 (fsucc fzero)) (@var nat 7 fzero))) (evaluate (@var nat 7 (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))) (@var nat 7 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 7 (fsucc (fsucc (fsucc fzero)))) (@var nat 7 (fsucc (fsucc fzero))) (@var nat 7 (fsucc fzero)) (@var nat 7 fzero)).
Proof.
  match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end.
Qed.
Lemma evaluate_addition {n} (d e X z s a m : Term nat n) :
  evaluate (app (app (lift_closed addition) d) e) X z s a m =ᵝ app (app a (evaluate d X z s a m)) (evaluate e X z s a m).
Proof.
  pose proof (replace_equiv (fin_match m (fin_match a (fin_match s (fin_match z (fin_match X (fin_match e (fin_match d (fun i : Fin 0 => match i with end)))))))) _ _ addition_schema) as H.
  unfold evaluate in H. rewrite !replace_application, !replace_lift_closed in H. exact H.
Qed.
Lemma multiplication_schema :
  evaluate (app (app (lift_closed multiplication) (@var nat 7 (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))) (@var nat 7 (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))) (@var nat 7 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 7 (fsucc (fsucc (fsucc fzero)))) (@var nat 7 (fsucc (fsucc fzero))) (@var nat 7 (fsucc fzero)) (@var nat 7 fzero) =ᵝ app (app (@var nat 7 fzero) (evaluate (@var nat 7 (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))) (@var nat 7 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 7 (fsucc (fsucc (fsucc fzero)))) (@var nat 7 (fsucc (fsucc fzero))) (@var nat 7 (fsucc fzero)) (@var nat 7 fzero))) (evaluate (@var nat 7 (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))) (@var nat 7 (fsucc (fsucc (fsucc (fsucc fzero))))) (@var nat 7 (fsucc (fsucc (fsucc fzero)))) (@var nat 7 (fsucc (fsucc fzero))) (@var nat 7 (fsucc fzero)) (@var nat 7 fzero)).
Proof.
  match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end.
Qed.
Lemma evaluate_multiplication {n} (d e X z s a m : Term nat n) :
  evaluate (app (app (lift_closed multiplication) d) e) X z s a m =ᵝ app (app m (evaluate d X z s a m)) (evaluate e X z s a m).
Proof.
  pose proof (replace_equiv (fin_match m (fin_match a (fin_match s (fin_match z (fin_match X (fin_match e (fin_match d (fun i : Fin 0 => match i with end)))))))) _ _ multiplication_schema) as H.
  unfold evaluate in H. rewrite !replace_application, !replace_lift_closed in H. exact H.
Qed.
Theorem numeral_evaluation k : forall n (X z s a m : Term nat n),
  evaluate (lift_closed (numeral k)) X z s a m =ᵝ UnaryEvaluation.iterations k z s.
Proof.
  induction k as [|k IH]; intros n X z s a m; cbn [numeral UnaryEvaluation.iterations].
  - apply evaluate_zero.
  - change (evaluate (app (lift_closed successor) (lift_closed (numeral k))) X z s a m =ᵝ
      app s (UnaryEvaluation.iterations k z s)).
    eapply beta_trans; [apply evaluate_successor |].
    apply beta_app; [reflexivity |apply IH].
Qed.
Theorem finite_numeral_evaluation c k :
  evaluate (numeral k) (selector_type (S c)) (point (S c) 0)
    (capped_successor (S c)) (capped_addition (S c)) (capped_multiplication (S c)) =ᵝ
  point (S c) (Nat.min k c).
Proof.
  rewrite <- (lift_closed_zero (numeral k)).
  eapply beta_trans; [apply numeral_evaluation |].
  rewrite UnaryEvaluation.finite_iterations. apply iterate_computation.
Qed.
End FunctionalEvaluation.
