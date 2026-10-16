(** A uniform bounded graph of iteration along singleton numerals.
    The reference family is used only in the correctness proof. Neither
    its range nor the range of finite separators is collected as a set. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes BoundedFormulas BoundedGraphs BoundedIteration.
Import Bounded CodeUniverses.CodeUniverses.

Definition recursion_parameters H P b :=
  fin_match omega_codes (fin_match H (fin_match P (fin_match (numeral 0)
    (fin_match b (fin_match (Power (Prod omega_codes H)) (fun i : Fin 0 => match i with end)))))).
Definition bounded_recursion_graph H P b := bounded_formula_graph
  carrier_iteration_certificate (recursion_parameters H P b) omega_codes H.

Fixpoint recursion_separator H (v : nat -> Ens) n :=
  match n with
  | 0 => slice_filter H (Prod omega_codes H) (numeral 0) (v 0)
  | S k => slice_filter H (recursion_separator H v k) (numeral (S k)) (v (S k))
  end.
Lemma recursion_separator_bound H v n : INC (recursion_separator H v n) (Prod omega_codes H).
Proof.
  destruct n; unfold recursion_separator, slice_filter, bounded_formula_graph; apply Comp_INC.
Qed.

Section Iteration.
Variables H P : Ens.
Variable v : nat -> Ens.
Hypothesis HV : forall n, IN (v n) H.
Hypothesis HS : forall n, application P (v n) (v (S n)).
Hypothesis HD : forall n x y, EQ x (v n) -> application P x y -> EQ y (v (S n)).

Lemma recursion_least R : iteration_closed R omega_codes H P (numeral 0) (v 0) ->
  forall n, application R (numeral n) (v n).
Proof.
  intros [HB HC] n. induction n as [|n IH]; [exact HB |].
  exact (HC (numeral n) (v n) (numeral (S n)) (v (S n))
    (numeral_in_omega n) (HV n) (numeral_in_omega (S n)) (HV (S n)) IH (EQ_refl _) (HS n)).
Qed.

Lemma recursion_separator_laws n :
  iteration_closed (recursion_separator H v n) omega_codes H P (numeral 0) (v 0) /\
  forall i y, application (recursion_separator H v n) i y -> EQ i (numeral n) -> EQ y (v n).
Proof.
  induction n as [|n [HC HU]].
  - split.
    + split.
      * apply slice_filter_application. split; [apply numeral_in_omega |].
        split; [apply HV |]. split.
        -- apply Couple_IN_Prod; [apply numeral_in_omega | apply HV].
        -- intro E; apply EQ_refl.
      * intros i x j y Hi Hx Hj Hy HR ES HP.
        apply slice_filter_application. split; [exact Hj |]. split; [exact Hy |]. split.
        -- apply Couple_IN_Prod; assumption.
        -- intro E. assert (EV : EQ Vide (Sing i)).
           { eapply EQ_tran; [apply EQ_sym; exact E | exact ES]. }
           destruct (not_EQ_Vide_Sing i EV).
    + intros i y HA E. apply slice_filter_application in HA as [_ [_ [_ HU]]]; apply HU; exact E.
  - destruct HC as [HB HC]. split.
    + split.
      * apply slice_filter_application. split; [apply numeral_in_omega |].
        split; [apply HV |]. split; [exact HB |].
        intro E; destruct (not_EQ_Vide_Sing (numeral n) E).
      * intros i x j y Hi Hx Hj Hy HR ES HP.
        apply slice_filter_application in HR as [_ [_ [HR _]]].
        apply slice_filter_application. split; [exact Hj |]. split; [exact Hy |]. split.
        -- exact (HC i x j y Hi Hx Hj Hy HR ES HP).
        -- intro EJ. apply (HD n x y); [| exact HP]. apply (HU i x HR).
           apply EQ_Sing_EQ. eapply EQ_tran; [apply EQ_sym; exact ES | exact EJ].
    + intros i y HA E. apply slice_filter_application in HA as [_ [_ [_ HU']]]; apply HU'; exact E.
Qed.

Theorem recursion_certificate_correct x n y : EQ x (numeral n) ->
  (holds carrier_iteration_certificate (fin_match y (fin_match x (recursion_parameters H P (v 0))))
    <-> EQ y (v n)).
Proof.
  intro Ex. unfold carrier_iteration_certificate. rewrite iteration_value_formula_correct.
  cbn [recursion_parameters fin_match]. split.
  - intro HC. destruct (recursion_separator_laws n) as [HC' HU].
    apply (HU x y); [| exact Ex]. apply HC; [| exact HC'].
    apply INC_IN_Power, recursion_separator_bound.
  - intros Ey R HR HC. pose proof (recursion_least R HC n) as HA.
    unfold application in *. apply (IN_sound_left (Couple (numeral n) (v n)) (Couple x y) R); [| exact HA].
    eapply EQ_tran; [apply Couple_sound_left; apply EQ_sym; exact Ex |].
    apply Couple_sound_right; apply EQ_sym; exact Ey.
Qed.

Theorem bounded_recursion_graph_typed :
  IN (bounded_recursion_graph H P (v 0)) (dependent_product omega_codes (fun _ => H)).
Proof.
  apply bounded_formula_graph_typed.
  - intros x Hx. apply omega_membership in Hx as [n Ex]. exists (v n).
    split; [apply HV | apply (proj2 (recursion_certificate_correct x n _ Ex)), EQ_refl].
  - intros x y z Hx Hy Hz HY HZ. apply omega_membership in Hx as [n Ex].
    apply (proj1 (recursion_certificate_correct x n y Ex)) in HY.
    apply (proj1 (recursion_certificate_correct x n z Ex)) in HZ.
    eapply EQ_tran; [exact HY | apply EQ_sym; exact HZ].
Qed.

Theorem bounded_recursion_graph_application n y :
  application (bounded_recursion_graph H P (v 0)) (numeral n) y <-> EQ y (v n).
Proof.
  unfold bounded_recursion_graph. rewrite bounded_formula_graph_spec.
  rewrite (recursion_certificate_correct _ n y (EQ_refl _)). split; [tauto |].
  intro E. split; [apply numeral_in_omega |]. split; [| exact E].
  exact (IN_sound_left (v n) y H (EQ_sym _ _ E) (HV n)).
Qed.

Theorem bounded_recursion_graph_beta n :
  EQ (apply_set (bounded_recursion_graph H P (v 0)) (numeral n)) (v n).
Proof.
  apply apply_set_value.
  - apply bounded_recursion_graph_application, EQ_refl.
  - intros y Hy. apply bounded_recursion_graph_application; exact Hy.
Qed.
End Iteration.
Print Assumptions recursion_separator_laws.
Print Assumptions recursion_certificate_correct.
Print Assumptions bounded_recursion_graph_typed.
Print Assumptions bounded_recursion_graph_application.
Print Assumptions bounded_recursion_graph_beta.
