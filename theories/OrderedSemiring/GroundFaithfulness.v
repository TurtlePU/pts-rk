(** Uniform ground evaluation and internal refutation for the NEW observer
    equality, difference order and source-oriented arithmetic graphs. Numerical side conditions
    select actual native PTS inhabitants; no external Bottom assumption is used. *)
From Stdlib Require Import Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRSymbolic DirectRFiniteUp.
From Interpretation_of_R.relational Require Import DirectRUnary
  DirectRUnaryEvaluation DirectRRelationalSyntax.
From OrderedSemiring Require Import ModelInterface FirstOrderTranslation
  ObservationEquality OrderNumerals OrderCuts BoundedCases.

Module GroundFaithfulness.
Import CommonCodes Core Structural NegativeLogic FiniteUp FirstOrderTranslation.

(** Only the common Church arithmetic's beta computations are reused from
    UnaryEvaluation.  No old equality/order realization is used. *)
Lemma addition_reversal_schema :
  app (app (lift_closed Model.addition) (@var nat 2 (fsucc fzero))) V0 =ᵝ
  app (app (lift_closed Unary.addition) V0) (shift V0).
Proof. match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end. Qed.
Lemma multiplication_reversal_schema :
  app (app (lift_closed Model.multiplication) (@var nat 2 (fsucc fzero))) V0 =ᵝ
  app (app (lift_closed Unary.multiplication) V0) (shift V0).
Proof. match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end. Qed.
Lemma addition_reversal {n} (d e : Term nat n) :
  app (app (lift_closed Model.addition) d) e =ᵝ
  app (app (lift_closed Unary.addition) e) d.
Proof.
  pose proof (replace_equiv (fin_match e (fin_match d (fun i : Fin 0 => match i with end)))
    _ _ addition_reversal_schema) as H.
  rewrite !replace_application, !replace_lift_closed in H. exact H.
Qed.
Lemma multiplication_reversal {n} (d e : Term nat n) :
  app (app (lift_closed Model.multiplication) d) e =ᵝ
  app (app (lift_closed Unary.multiplication) e) d.
Proof.
  pose proof (replace_equiv (fin_match e (fin_match d (fun i : Fin 0 => match i with end)))
    _ _ multiplication_reversal_schema) as H.
  rewrite !replace_application, !replace_lift_closed in H. exact H.
Qed.
Definition addition_result m n := app (app Model.addition (Model.numeral m)) (Model.numeral n).
Definition multiplication_result m n := app (app Model.multiplication (Model.numeral m)) (Model.numeral n).
Lemma addition_result_typed m n : Typed ε (addition_result m n) Model.Domain.
Proof.
  unfold addition_result. eapply arrow_application; [|apply Unary.numeral_typed].
  eapply arrow_application; [apply Model.addition_typed |apply Unary.numeral_typed].
Qed.
Lemma multiplication_result_typed m n : Typed ε (multiplication_result m n) Model.Domain.
Proof.
  unfold multiplication_result. eapply arrow_application; [|apply Unary.numeral_typed].
  eapply arrow_application; [apply Model.multiplication_typed |apply Unary.numeral_typed].
Qed.
Theorem addition_numerals m n : addition_result m n =ᵝ Model.numeral (m+n).
Proof.
  unfold addition_result. rewrite <- (lift_closed_zero Model.addition).
  eapply beta_trans; [apply addition_reversal |]. rewrite lift_closed_zero, Nat.add_comm.
  apply UnaryEvaluation.addition_numerals.
Qed.
Theorem multiplication_numerals m n : multiplication_result m n =ᵝ Model.numeral (m*n).
Proof.
  unfold multiplication_result. rewrite <- (lift_closed_zero Model.multiplication).
  eapply beta_trans; [apply multiplication_reversal |]. rewrite lift_closed_zero, Nat.mul_comm.
  apply UnaryEvaluation.multiplication_numerals.
Qed.

Theorem numeral_equality {n} (Γ : Ctx nat n) i j : i = j ->
  inhabited Γ (Model.E (lift_closed (Model.numeral i)) (lift_closed (Model.numeral j))).
Proof. intros ->. apply equality_reflexivity_in_context, lift_closed_typed, Unary.numeral_typed. Qed.
Theorem numeral_inequality {n} (Γ : Ctx nat n) i j : i <> j ->
  inhabited Γ (Neg (Model.E (lift_closed (Model.numeral i)) (lift_closed (Model.numeral j)))).
Proof. apply OrderNumerals.numeral_inequality. Qed.
Theorem numeral_order {n} (Γ : Ctx nat n) i j : i <= j ->
  inhabited Γ (Model.O (lift_closed (Model.numeral i)) (lift_closed (Model.numeral j))).
Proof. apply OrderCuts.ground_order. Qed.
Theorem numeral_order_refutation {n} (Γ : Ctx nat n) i j : j < i ->
  inhabited Γ (Neg (Model.O (lift_closed (Model.numeral i)) (lift_closed (Model.numeral j)))).
Proof. apply BoundedCases.false_order_numerals. Qed.

(** Conversion transports an actual equality or refutation witness. *)
Lemma ground_equation l v k : Typed ε l Model.Domain -> l =ᵝ Model.numeral v -> v = k ->
  Realizes (Model.E l (Model.numeral k)).
Proof.
  intros Hl Hbeta <-. eapply inhabited_conversion.
  - apply equality_reflexivity_in_context. rewrite lift_closed_zero. apply Unary.numeral_typed.
  - apply Model.equality_in_context; rewrite lift_closed_zero; auto using Unary.numeral_typed.
  - unfold Model.E. apply beta_app; [|reflexivity].
    apply beta_app; [reflexivity |symmetry; exact Hbeta].
Qed.
Lemma ground_inequation l v k : Typed ε l Model.Domain -> l =ᵝ Model.numeral v -> v <> k ->
  Realizes (Neg (Model.E l (Model.numeral k))).
Proof.
  intros Hl Hbeta Hne. eapply inhabited_conversion.
  - pose proof (numeral_inequality ε v k Hne) as H. rewrite !lift_closed_zero in H. exact H.
  - apply neg_formation, Model.equality_in_context;
      rewrite lift_closed_zero; auto using Unary.numeral_typed.
  - apply neg_beta. unfold Model.E. apply beta_app; [|reflexivity].
    apply beta_app; [reflexivity |symmetry; exact Hbeta].
Qed.
Definition AddAtom m n k := Model.E (addition_result m n) (Model.numeral k).
Definition MulAtom m n k := Model.E (multiplication_result m n) (Model.numeral k).
Theorem ground_addition_true m n k : m+n=k -> Realizes (AddAtom m n k).
Proof. apply (ground_equation _ (m+n)); auto using addition_result_typed, addition_numerals. Qed.
Theorem ground_addition_false m n k : m+n<>k -> Realizes (Neg (AddAtom m n k)).
Proof. apply (ground_inequation _ (m+n)); auto using addition_result_typed, addition_numerals. Qed.
Theorem ground_multiplication_true m n k : m*n=k -> Realizes (MulAtom m n k).
Proof. apply (ground_equation _ (m*n)); auto using multiplication_result_typed, multiplication_numerals. Qed.
Theorem ground_multiplication_false m n k : m*n<>k -> Realizes (Neg (MulAtom m n k)).
Proof. apply (ground_inequation _ (m*n)); auto using multiplication_result_typed, multiplication_numerals. Qed.

(** The same results for every closed source term, not just displayed numerals. *)
Theorem equality_true t u : value t = value u -> Realizes (sentence (Relational.equal t u)).
Proof.
  intro H. unfold sentence. cbn [formula]. rewrite !closed_term_translation, H.
  apply equality_reflexivity_in_context. rewrite lift_closed_zero. apply Unary.numeral_typed.
Qed.
Theorem equality_false t u : value t <> value u -> Realizes (Neg (sentence (Relational.equal t u))).
Proof.
  intro H. unfold sentence. cbn [formula]. rewrite !closed_term_translation.
  pose proof (numeral_inequality ε (value t) (value u) H) as Hn.
  rewrite !lift_closed_zero in Hn. exact Hn.
Qed.
Theorem order_true t u : value t <= value u -> Realizes (sentence (Relational.less_equal t u)).
Proof.
  intro H. unfold sentence. cbn [formula]. rewrite !closed_term_translation.
  pose proof (numeral_order ε (value t) (value u) H) as Ho.
  rewrite !lift_closed_zero in Ho. exact Ho.
Qed.
Theorem order_false t u : value u < value t ->
  Realizes (Neg (sentence (Relational.less_equal t u))).
Proof.
  intro H. unfold sentence. cbn [formula]. rewrite !closed_term_translation.
  pose proof (numeral_order_refutation ε (value t) (value u) H) as Ho.
  rewrite !lift_closed_zero in Ho. exact Ho.
Qed.
Theorem addition_true t u v : value t + value u = value v ->
  Realizes (sentence (Relational.add_graph t u v)).
Proof.
  unfold sentence. cbn [formula]. rewrite !closed_term_translation, lift_closed_zero.
  apply ground_addition_true.
Qed.
Theorem addition_false t u v : value t + value u <> value v ->
  Realizes (Neg (sentence (Relational.add_graph t u v))).
Proof.
  unfold sentence. cbn [formula]. rewrite !closed_term_translation, lift_closed_zero.
  apply ground_addition_false.
Qed.
Theorem multiplication_true t u v : value t * value u = value v ->
  Realizes (sentence (Relational.mul_graph t u v)).
Proof.
  unfold sentence. cbn [formula]. rewrite !closed_term_translation, lift_closed_zero.
  apply ground_multiplication_true.
Qed.
Theorem multiplication_false t u v : value t * value u <> value v ->
  Realizes (Neg (sentence (Relational.mul_graph t u v))).
Proof.
  unfold sentence. cbn [formula]. rewrite !closed_term_translation, lift_closed_zero.
  apply ground_multiplication_false.
Qed.

Print Assumptions numeral_inequality.
Print Assumptions equality_true.
Print Assumptions equality_false.
Print Assumptions order_true.
Print Assumptions order_false.
Print Assumptions addition_true.
Print Assumptions addition_false.
Print Assumptions multiplication_true.
Print Assumptions multiplication_false.
End GroundFaithfulness.
