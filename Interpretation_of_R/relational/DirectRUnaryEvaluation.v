(** Uniform beta fold equations for the actual unary Church numerals. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural
  DirectRSymbolic DirectRFiniteTables DirectRIterations.
From Interpretation_of_R.relational Require Import DirectRUnary.

Module UnaryEvaluation.
Import CommonCodes Core Structural FiniteTables.
Export Iterations.
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
Theorem numeral_evaluation k : forall n (X z s : Term nat n),
  evaluate (lift_closed (Unary.numeral k)) X z s =ᵝ iterations k z s.
Proof.
  induction k as [|k IH]; intros n X z s; cbn [Unary.numeral iterations].
  - apply evaluate_zero.
  - change (evaluate (app (lift_closed Unary.successor)
      (lift_closed (Unary.numeral k))) X z s =ᵝ app s (iterations k z s)).
    eapply beta_trans; [apply evaluate_successor |]. apply beta_app; [reflexivity |apply IH].
Qed.
Theorem finite_numeral_evaluation c k :
  evaluate (Unary.numeral k) (selector_type (S c)) (point (S c) 0)
    (capped_successor (S c)) =ᵝ point (S c) (Nat.min k c).
Proof.
  rewrite <- (lift_closed_zero (Unary.numeral k)).
  eapply beta_trans; [apply numeral_evaluation |]. rewrite finite_iterations.
  apply iterate_computation.
Qed.
(** Fully annotated Church normal forms. *)
Definition church k : closed_term :=
  lam (𝓤 1) (lam V0 (lam (Arrow (shift V0) (shift V0)) (iterations k (shift V0) V0))).
Definition succ_body {n} (d : Term nat n) :=
  lam (𝓤 1) (lam V0 (lam (Arrow (shift V0) (shift V0))
    (app V0 (evaluate (shift (shift (shift d))) (shift (shift V0)) (shift V0) V0)))).
Lemma successor_body_schema : app (lift_closed Unary.successor) (@V0 0) =ᵝ succ_body V0.
Proof. match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end. Qed.
Lemma successor_body {n} (d : Term nat n) : app (lift_closed Unary.successor) d =ᵝ succ_body d.
Proof.
  pose proof (replace_equiv (fin_match d (fun i : Fin 0 => match i with end)) _ _ successor_body_schema) as H.
  unfold succ_body, evaluate in H. rewrite replace_application, replace_lift_closed in H.
  cbn [replace] in H. rewrite !replace_shift in H. exact H.
Qed.
Theorem numeral_normal_form k : Unary.numeral k =ᵝ church k.
Proof.
  destruct k as [|k].
  - reflexivity.
  - change (app Unary.successor (Unary.numeral k) =ᵝ church (S k)).
    rewrite <- (lift_closed_zero Unary.successor).
    eapply beta_trans; [apply successor_body |]. unfold succ_body, church.
    apply beta_lam; [reflexivity |]. apply beta_lam; [reflexivity |].
    apply beta_lam; [reflexivity |]. cbn [iterations]. apply beta_app; [reflexivity |].
    rewrite Unary.shift_closed, <- !lift_closed_shift. apply numeral_evaluation.
Qed.
Lemma iterations_beta {n} k (z z' s s' : Term nat n) :
  z =ᵝ z' -> s =ᵝ s' -> iterations k z s =ᵝ iterations k z' s'.
Proof. intros Hz Hs. induction k; cbn [iterations]; auto using beta_app. Qed.
Lemma iterations_add {n} m k (z s : Term nat n) :
  iterations m (iterations k z s) s = iterations (m+k) z s.
Proof. induction m; cbn [iterations Nat.add]; congruence. Qed.
Definition add_body {n} (d e : Term nat n) :=
  lam (𝓤 1) (lam V0 (lam (Arrow (shift V0) (shift V0))
    (evaluate (shift (shift (shift d))) (shift (shift V0))
      (evaluate (shift (shift (shift e))) (shift (shift V0)) (shift V0) V0) V0))).
Lemma addition_body_schema :
  app (app (lift_closed Unary.addition) (@var nat 2 (fsucc fzero))) V0 =ᵝ add_body (shift V0) V0.
Proof. match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end. Qed.
Lemma addition_body {n} (d e : Term nat n) :
  app (app (lift_closed Unary.addition) d) e =ᵝ add_body d e.
Proof.
  pose proof (replace_equiv (fin_match e (fin_match d (fun i : Fin 0 => match i with end)))
    _ _ addition_body_schema) as H.
  unfold add_body, evaluate in H. rewrite !replace_application, replace_lift_closed in H.
  cbn [replace] in H. rewrite !replace_shift in H. exact H.
Qed.
Theorem addition_numerals m k :
  app (app Unary.addition (Unary.numeral m)) (Unary.numeral k) =ᵝ Unary.numeral (m+k).
Proof.
  rewrite <- (lift_closed_zero Unary.addition).
  eapply beta_trans; [apply addition_body |].
  eapply beta_trans; [|symmetry; apply numeral_normal_form]. unfold add_body, church.
  apply beta_lam; [reflexivity |]. apply beta_lam; [reflexivity |]. apply beta_lam; [reflexivity |].
  rewrite !Unary.shift_closed, <- !lift_closed_shift.
  eapply beta_trans; [apply numeral_evaluation |].
  rewrite <- iterations_add. apply iterations_beta; [apply numeral_evaluation |reflexivity].
Qed.
Definition church_function {n} k (X s : Term nat n) :=
  lam X (evaluate (lift_closed (Unary.numeral k)) (shift X) V0 (shift s)).
Lemma church_function_beta {n} k (X z s : Term nat n) :
  app (church_function k X s) z =ᵝ iterations k z s.
Proof.
  unfold church_function, evaluate. eapply beta_trans; [apply beta_contract |].
  rewrite !subst_app, subst_closed, !substitute_shift, subst_V0. apply numeral_evaluation.
Qed.
Lemma iterations_multiply {n} m k (X z s : Term nat n) :
  iterations m z (church_function k X s) =ᵝ iterations (m*k) z s.
Proof.
  induction m as [|m IH]; cbn [iterations Nat.mul]; [reflexivity |].
  eapply beta_trans; [apply church_function_beta |].
  rewrite <- iterations_add. apply iterations_beta; [exact IH |reflexivity].
Qed.
Definition mul_body {n} (d e : Term nat n) :=
  lam (𝓤 1) (lam V0 (lam (Arrow (shift V0) (shift V0))
    (evaluate (shift (shift (shift d))) (shift (shift V0)) (shift V0)
      (lam (shift (shift V0))
        (evaluate (shift (shift (shift (shift e)))) (shift (shift (shift V0))) V0 (shift V0)))))).
Lemma multiplication_body_schema :
  app (app (lift_closed Unary.multiplication) (@var nat 2 (fsucc fzero))) V0 =ᵝ mul_body (shift V0) V0.
Proof. match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end. Qed.
Lemma multiplication_body {n} (d e : Term nat n) :
  app (app (lift_closed Unary.multiplication) d) e =ᵝ mul_body d e.
Proof.
  pose proof (replace_equiv (fin_match e (fin_match d (fun i : Fin 0 => match i with end)))
    _ _ multiplication_body_schema) as H.
  unfold mul_body, evaluate in H. rewrite !replace_application, replace_lift_closed in H.
  cbn [replace] in H. rewrite !replace_shift in H. exact H.
Qed.
Theorem multiplication_numerals m k :
  app (app Unary.multiplication (Unary.numeral m)) (Unary.numeral k) =ᵝ Unary.numeral (m*k).
Proof.
  rewrite <- (lift_closed_zero Unary.multiplication).
  eapply beta_trans; [apply multiplication_body |].
  eapply beta_trans; [|symmetry; apply numeral_normal_form]. unfold mul_body, church.
  apply beta_lam; [reflexivity |]. apply beta_lam; [reflexivity |]. apply beta_lam; [reflexivity |].
  rewrite !Unary.shift_closed, <- !lift_closed_shift.
  eapply beta_trans; [apply numeral_evaluation |]. apply iterations_multiply.
Qed.
End UnaryEvaluation.
