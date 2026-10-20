(** Ground evaluation and internal refutation for arbitrary nested functional
    terms. Native nat computes only the external value and side conditions;
    every conclusion is inhabited by an original annotated PTS term. *)
From Stdlib Require Import Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRFiniteUp.
From Interpretation_of_R.relational Require Import DirectRUnary.
From OrderedSemiring Require Import ModelInterface GroundFaithfulness.
From OrderedSemiringFunctional Require Import Source Translation.

Module FunctionalGround.
Import CommonCodes Core Structural NegativeLogic FiniteUp FunctionalTranslation.

Theorem closed_term_beta (t : FunctionalSource.term 0) :
  term empty_env t =ᵝ Model.numeral (value t).
Proof.
  induction t; cbn [term value].
  - exact (match f with end).
  - rewrite lift_closed_zero. reflexivity.
  - change (app (lift_closed Model.successor) (term empty_env t) =ᵝ
      app Model.successor (Model.numeral (value t))).
    rewrite lift_closed_zero. apply beta_app; [reflexivity |exact IHt].
  - rewrite lift_closed_zero.
    eapply (@Core.beta_trans 0 _ (GroundFaithfulness.addition_result (value t1) (value t2)) _).
    + unfold GroundFaithfulness.addition_result.
      apply beta_app; [apply beta_app; [reflexivity |exact IHt1] |exact IHt2].
    + apply GroundFaithfulness.addition_numerals.
  - rewrite lift_closed_zero.
    eapply (@Core.beta_trans 0 _ (GroundFaithfulness.multiplication_result (value t1) (value t2)) _).
    + unfold GroundFaithfulness.multiplication_result.
      apply beta_app; [apply beta_app; [reflexivity |exact IHt1] |exact IHt2].
    + apply GroundFaithfulness.multiplication_numerals.
Qed.

Theorem closed_term_typed (t : FunctionalSource.term 0) :
  Typed ε (term empty_env t) Model.Domain.
Proof.
  rewrite <- (lift_closed_zero Model.Domain). apply term_typed.
  intro i. exact (match i with end).
Qed.
Theorem closed_term_admitted (t : FunctionalSource.term 0) :
  Realizes (Model.admitted (term empty_env t)).
Proof.
  apply term_admitted; intro i; exact (match i with end).
Qed.

Lemma equality_beta t u : sentence (FunctionalSource.equal t u) =ᵝ
  Model.E (Model.numeral (value t)) (Model.numeral (value u)).
Proof.
  unfold sentence. cbn [formula]. unfold Model.E.
  apply beta_app; [apply beta_app; [reflexivity |apply closed_term_beta] |apply closed_term_beta].
Qed.
Lemma order_beta t u : sentence (FunctionalSource.less_equal t u) =ᵝ
  Model.O (Model.numeral (value t)) (Model.numeral (value u)).
Proof.
  unfold sentence. cbn [formula]. unfold Model.O.
  apply beta_app; [apply beta_app; [reflexivity |apply closed_term_beta] |apply closed_term_beta].
Qed.
Lemma sentence_typed A : Typed ε (sentence A) (𝓤 (formula_rank A)).
Proof. apply formula_typed. intro i. exact (match i with end). Qed.

Theorem equality_true t u : value t = value u ->
  Realizes (sentence (FunctionalSource.equal t u)).
Proof.
  intro Heq. eapply inhabited_conversion.
  - pose proof (GroundFaithfulness.numeral_equality ε _ _ Heq) as H.
    rewrite !lift_closed_zero in H. exact H.
  - apply sentence_typed.
  - symmetry. apply equality_beta.
Qed.
Theorem equality_false t u : value t <> value u ->
  Realizes (Neg (sentence (FunctionalSource.equal t u))).
Proof.
  intro Hne. eapply inhabited_conversion.
  - pose proof (GroundFaithfulness.numeral_inequality ε _ _ Hne) as H.
    rewrite !lift_closed_zero in H. exact H.
  - apply neg_formation, sentence_typed.
  - apply neg_beta. symmetry. apply equality_beta.
Qed.
Theorem order_true t u : value t <= value u ->
  Realizes (sentence (FunctionalSource.less_equal t u)).
Proof.
  intro Hle. eapply inhabited_conversion.
  - pose proof (GroundFaithfulness.numeral_order ε _ _ Hle) as H.
    rewrite !lift_closed_zero in H. exact H.
  - apply sentence_typed.
  - symmetry. apply order_beta.
Qed.
Theorem order_false t u : value u < value t ->
  Realizes (Neg (sentence (FunctionalSource.less_equal t u))).
Proof.
  intro Hlt. eapply inhabited_conversion.
  - pose proof (GroundFaithfulness.numeral_order_refutation ε _ _ Hlt) as H.
    rewrite !lift_closed_zero in H. exact H.
  - apply neg_formation, sentence_typed.
  - apply neg_beta. symmetry. apply order_beta.
Qed.

Theorem ground_faithfulness :
  (forall t u, value t = value u -> Realizes (sentence (FunctionalSource.equal t u))) /\
  (forall t u, value t <> value u -> Realizes (Neg (sentence (FunctionalSource.equal t u)))) /\
  (forall t u, value t <= value u -> Realizes (sentence (FunctionalSource.less_equal t u))) /\
  (forall t u, value u < value t -> Realizes (Neg (sentence (FunctionalSource.less_equal t u)))).
Proof. repeat split; auto using equality_true, equality_false, order_true, order_false. Qed.

Print Assumptions closed_term_beta.
Print Assumptions closed_term_admitted.
Print Assumptions ground_faithfulness.
End FunctionalGround.
