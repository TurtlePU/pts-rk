(** Ground correctness for the independent relational source syntax.
    Truth and falsity produce PTS inhabitants, not merely host propositions. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRUnary DirectRSeparation DirectRUnaryArithmetic
  DirectRRelationalSyntax DirectRRelationalTranslation.
Module RelationalGround.
Import Codes Core Structural RelationalTranslation.
Theorem equality_true t u : value t = value u -> Realizes (sentence (Relational.equal t u)).
Proof.
  intro H. unfold sentence. cbn [formula]. rewrite !closed_term_translation, H.
  exists (app Unary.equality_reflexivity (Unary.numeral (value u))).
  apply Unary.equality_reflexivity_application, Unary.numeral_typed.
Qed.
Theorem equality_false t u : value t <> value u -> Realizes (Neg (sentence (Relational.equal t u))).
Proof. unfold sentence. cbn [formula]. rewrite !closed_term_translation. apply Separation.R3_realized. Qed.
Theorem order_true t u : value t <= value u -> Realizes (sentence (Relational.less_equal t u)).
Proof. unfold sentence. cbn [formula]. rewrite !closed_term_translation. apply Unary.ground_order_realized. Qed.
Theorem order_false t u : value u < value t -> Realizes (Neg (sentence (Relational.less_equal t u))).
Proof. unfold sentence. cbn [formula]. rewrite !closed_term_translation. apply Separation.ground_order_refutation. Qed.
Theorem addition_true t u v : value t + value u = value v ->
  Realizes (sentence (Relational.add_graph t u v)).
Proof.
  unfold sentence. cbn [formula]. rewrite !closed_term_translation, lift_closed_zero.
  apply UnaryArithmetic.ground_addition_true.
Qed.
Theorem addition_false t u v : value t + value u <> value v ->
  Realizes (Neg (sentence (Relational.add_graph t u v))).
Proof.
  unfold sentence. cbn [formula]. rewrite !closed_term_translation, lift_closed_zero.
  apply UnaryArithmetic.ground_addition_false.
Qed.
Theorem multiplication_true t u v : value t * value u = value v ->
  Realizes (sentence (Relational.mul_graph t u v)).
Proof.
  unfold sentence. cbn [formula]. rewrite !closed_term_translation, lift_closed_zero.
  apply UnaryArithmetic.ground_multiplication_true.
Qed.
Theorem multiplication_false t u v : value t * value u <> value v ->
  Realizes (Neg (sentence (Relational.mul_graph t u v))).
Proof.
  unfold sentence. cbn [formula]. rewrite !closed_term_translation, lift_closed_zero.
  apply UnaryArithmetic.ground_multiplication_false.
Qed.
End RelationalGround.
