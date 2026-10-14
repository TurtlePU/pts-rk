(** Uniform arithmetic on the singleton-numeral code representation.
    Tripling is a bounded iteration graph, not a table of finite examples. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes BoundedFormulas BoundedGraphs BoundedRecursion
  BoundedFiniteCarriers CodeHierarchyBounds.
Import Bounded CodeUniverses.CodeUniverses.

Lemma singleton_in_omega x : IN x omega_codes -> IN (Sing x) omega_codes.
Proof.
  intro Hx. apply omega_membership in Hx as [n E].
  apply omega_membership. exists (S n). apply Sing_sound; exact E.
Qed.

Definition triple_successor x := Sing (Sing (Sing x)).
Definition triple_successor_certificate : Formula 3 :=
  ex (fsucc (fsucc fzero)) (conj (singletonF fzero (fsucc (fsucc fzero)))
    (ex (fsucc (fsucc (fsucc fzero)))
      (conj (singletonF fzero (fsucc fzero)) (singletonF (fsucc (fsucc fzero)) fzero)))).
Definition triple_parameters := fin_match omega_codes (fun i : Fin 0 => match i with end).

Lemma triple_successor_certificate_correct x y : IN x omega_codes ->
  (holds triple_successor_certificate (fin_match y (fin_match x triple_parameters)) <->
    EQ y (triple_successor x)).
Proof.
  intro Hx. unfold triple_successor_certificate. cbn [holds].
  setoid_rewrite singleton_correct. cbn [triple_parameters fin_match]. split.
  - intros [z [Hz [Ez [w [Hw [Ew Ey]]]]]].
    eapply EQ_tran; [exact Ey | apply Sing_sound].
    eapply EQ_tran; [exact Ew | apply Sing_sound; exact Ez].
  - intro E. exists (Sing x). split; [apply singleton_in_omega; exact Hx |].
    split; [apply EQ_refl |]. exists (Sing (Sing x)).
    split; [repeat apply singleton_in_omega; exact Hx |]. split; [apply EQ_refl | exact E].
Qed.
Definition triple_successor_graph := bounded_formula_graph
  triple_successor_certificate triple_parameters omega_codes omega_codes.
Lemma triple_successor_application x y :
  application triple_successor_graph x y <-> IN x omega_codes /\ EQ y (triple_successor x).
Proof.
  unfold triple_successor_graph. rewrite bounded_formula_graph_spec. split.
  - intros [Hx [Hy HP]]. split; [exact Hx |].
    apply (proj1 (triple_successor_certificate_correct x y Hx)); exact HP.
  - intros [Hx E]. split; [exact Hx |]. split.
    + apply (IN_sound_left (triple_successor x) y _ (EQ_sym _ _ E)).
      repeat apply singleton_in_omega; exact Hx.
    + apply (proj2 (triple_successor_certificate_correct x y Hx)); exact E.
Qed.

Lemma numeral_triple_step n : application triple_successor_graph (numeral (3*n)) (numeral (3*S n)).
Proof.
  apply triple_successor_application. split; [apply numeral_in_omega |].
  replace (3*S n) with (S (S (S (3*n)))) by lia. apply EQ_refl.
Qed.
Lemma numeral_triple_unique n x y : EQ x (numeral (3*n)) ->
  application triple_successor_graph x y -> EQ y (numeral (3*S n)).
Proof.
  intros Ex HP. apply triple_successor_application in HP as [_ Ey].
  replace (3*S n) with (S (S (S (3*n)))) by lia.
  eapply EQ_tran; [exact Ey | repeat apply Sing_sound; exact Ex].
Qed.

Definition numeral_tripling_graph := bounded_recursion_graph omega_codes triple_successor_graph Vide.
Theorem numeral_tripling_application n y :
  application numeral_tripling_graph (numeral n) y <-> EQ y (numeral (3*n)).
Proof.
  exact (bounded_recursion_graph_application omega_codes triple_successor_graph
    (fun n => numeral (3*n)) (fun n => numeral_in_omega (3*n))
    numeral_triple_step numeral_triple_unique n y).
Qed.
Theorem numeral_tripling_typed :
  IN numeral_tripling_graph (dependent_product omega_codes (fun _ => omega_codes)).
Proof.
  exact (bounded_recursion_graph_typed omega_codes triple_successor_graph
    (fun n => numeral (3*n)) (fun n => numeral_in_omega (3*n))
    numeral_triple_step numeral_triple_unique).
Qed.
Theorem numeral_tripling_beta n :
  EQ (apply_set numeral_tripling_graph (numeral n)) (numeral (3*n)).
Proof.
  apply apply_set_value.
  - apply numeral_tripling_application, EQ_refl.
  - intros y Hy. apply numeral_tripling_application; exact Hy.
Qed.

(** Environment: output carrier, input code, tripling graph, finite-carrier
    graph, omega. This is the finite decoder branch, not the full decoder. *)
Definition finite_decode_certificate : Formula 5 :=
  ex (fsucc (fsucc (fsucc (fsucc fzero))))
    (conj (applicationF (fsucc (fsucc (fsucc fzero))) fzero (fsucc (fsucc fzero)))
      (applicationF (fsucc (fsucc (fsucc (fsucc fzero)))) fzero (fsucc fzero))).
Definition finite_decode_parameters := fin_match numeral_tripling_graph
  (fin_match finite_carrier_graph (fin_match omega_codes (fun i : Fin 0 => match i with end))).

Theorem finite_decode_certificate_correct n y :
  holds finite_decode_certificate (fin_match y (fin_match (repr (finite n)) finite_decode_parameters))
  <-> EQ y (finite_carrier n).
Proof.
  unfold finite_decode_certificate. cbn [holds].
  setoid_rewrite application_correct. cbn [finite_decode_parameters fin_match]. split.
  - intros [q [Hq [HT HF]]]. apply omega_membership in Hq as [k EQq].
    assert (HT' : application numeral_tripling_graph (numeral k) (repr (finite n))) by
      (eapply application_arguments; [apply EQ_refl | exact EQq | apply EQ_refl | exact HT]).
    apply numeral_tripling_application in HT'. apply numeral_injective in HT'.
    change (3*n = 3*k) in HT'. assert (E : k = n) by lia; subst k.
    apply finite_carrier_graph_application.
    eapply application_arguments; [apply EQ_refl | exact EQq | apply EQ_refl | exact HF].
  - intro E. exists (numeral n). split; [apply numeral_in_omega |]. split.
    + apply numeral_tripling_application, EQ_refl.
    + apply finite_carrier_graph_application; exact E.
Qed.

Definition bounded_finite_decoder := bounded_formula_graph finite_decode_certificate
  finite_decode_parameters omega_codes (Power omega_codes).

Theorem bounded_finite_decoder_application n y :
  application bounded_finite_decoder (repr (finite n)) y <-> EQ y (finite_carrier n).
Proof.
  unfold bounded_finite_decoder. rewrite bounded_formula_graph_spec.
  rewrite finite_decode_certificate_correct. split; [tauto |].
  intro E. split; [apply numeral_in_omega |]. split; [| exact E].
  apply (IN_sound_left (finite_carrier n) y _ (EQ_sym _ _ E)).
  apply INC_IN_Power, finite_subset_omega.
Qed.

Theorem bounded_finite_decoder_beta n :
  EQ (apply_set bounded_finite_decoder (repr (finite n))) (finite_carrier n).
Proof.
  apply apply_set_value.
  - apply bounded_finite_decoder_application, EQ_refl.
  - intros y Hy. apply bounded_finite_decoder_application; exact Hy.
Qed.
Print Assumptions triple_successor_certificate_correct.
Print Assumptions numeral_tripling_application.
Print Assumptions numeral_tripling_typed.
Print Assumptions numeral_tripling_beta.
Print Assumptions finite_decode_certificate_correct.
Print Assumptions bounded_finite_decoder_application.
Print Assumptions bounded_finite_decoder_beta.
