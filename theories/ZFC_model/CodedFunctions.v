(** Local computation laws for a concrete coding bijection. This does NOT
    assume an abstract PTS model or assert that the necessary cardinal
    bijections exist. Their coherent construction remains outstanding. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections.

Definition encode_function f A body := apply_set f (graph A body).
Definition decode_function A B K f c :=
  apply_set (inverse (dependent_product A B) K f) c.
Definition coded_application A B K f c x := apply_set (decode_function A B K f c) x.

Theorem encoded_abstraction_typed A B K f body :
  bijection (dependent_product A B) K f ->
  family_extensional body -> (forall x, IN x A -> IN (body x) (B x)) ->
  IN (encode_function f A body) K.
Proof.
  intros Hf Hbody Htyped. apply (apply_set_typed (dependent_product A B) (fun _ => K)).
  - exact (proj1 Hf).
  - apply dependent_product_introduction; assumption.
Qed.
Theorem decoded_function_typed A B K f c :
  bijection (dependent_product A B) K f -> IN c K ->
  IN (decode_function A B K f c) (dependent_product A B).
Proof.
  intros Hf Hc. apply (apply_set_typed K (fun _ => dependent_product A B)).
  - apply inverse_typed; exact Hf.
  - exact Hc.
Qed.
Theorem coded_application_typed A B K f c x :
  bijection (dependent_product A B) K f -> IN c K -> IN x A ->
  IN (coded_application A B K f c x) (B x).
Proof.
  intros Hf Hc Hx. apply (apply_set_typed A B); [apply decoded_function_typed; assumption | exact Hx].
Qed.
Theorem coded_beta A B K f body x :
  bijection (dependent_product A B) K f ->
  family_extensional body -> (forall y, IN y A -> IN (body y) (B y)) ->
  IN x A -> EQ (coded_application A B K f (encode_function f A body) x) (body x).
Proof.
  intros Hf Hbody Htyped Hx. unfold coded_application, decode_function, encode_function.
  eapply EQ_tran.
  - apply apply_set_extensional; [| apply EQ_refl]. apply inverse_left; [exact Hf |].
    apply dependent_product_introduction; assumption.
  - apply apply_set_beta; assumption.
Qed.
Theorem coded_application_extensional A B K f c c' x x' :
  EQ c c' -> EQ x x' ->
  EQ (coded_application A B K f c x) (coded_application A B K f c' x').
Proof.
  intros Ec Ex. apply apply_set_extensional; [| exact Ex].
  apply apply_set_extensional; [apply EQ_refl | exact Ec].
Qed.
Theorem empty_fiber_forces_empty_code A B K f x :
  bijection (dependent_product A B) K f -> IN x A -> EQ (B x) Vide ->
  EQ K Vide.
Proof.
  intros Hf Hx E. apply tout_vide_est_Vide. intros c Hc. exfalso.
  apply (dependent_product_empty_fiber A B x Hx E (decode_function A B K f c)).
  apply decoded_function_typed; assumption.
Qed.

Print Assumptions encoded_abstraction_typed.
Print Assumptions decoded_function_typed.
Print Assumptions coded_application_typed.
Print Assumptions coded_beta.
Print Assumptions coded_application_extensional.
Print Assumptions empty_fiber_forces_empty_code.
Check coded_beta.
Check empty_fiber_forces_empty_code.
