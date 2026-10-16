(** An actual set-graph bijection omega_codes x omega_codes -> omega_codes.
    This is the countable base of the Cartesian cardinal estimates. *)
From Stdlib Require Import Arith.Cantor.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  ProductEmbedding CodeUniverses CountableCodes CardinalGrowth PowersetEmbedding SubsetFunctions.
Import CodeUniverses.CodeUniverses.

Definition pair_repr (p : nat * nat) := Couple (numeral (fst p)) (numeral (snd p)).
Lemma pair_repr_injective p q : EQ (pair_repr p) (pair_repr q) -> p = q.
Proof.
  destruct p as [n m], q as [n' m']; intro E.
  pose proof (numeral_injective _ _ (Couple_inj_left _ _ _ _ E)) as En.
  pose proof (numeral_injective _ _ (Couple_inj_right _ _ _ _ E)) as Em.
  cbn in En, Em; subst; reflexivity.
Qed.
Lemma pair_repr_member p : IN (pair_repr p) (Prod omega_codes omega_codes).
Proof. apply Couple_IN_Prod; apply numeral_in_omega. Qed.
Lemma omega_pair_membership x :
  IN x (Prod omega_codes omega_codes) <-> exists p, EQ x (pair_repr p).
Proof.
  split.
  - intro H. destruct (IN_Prod_EXType _ _ _ H) as [a [b E]].
    pose proof (IN_sound_left x (Couple a b) _ (EQ_sym _ _ E) H) as Hp.
    destruct (Couple_Prod_IN _ _ _ _ Hp) as [Ha Hb].
    apply omega_membership in Ha as [n En]. apply omega_membership in Hb as [m Em].
    exists (n,m). eapply EQ_tran; [apply EQ_sym; exact E |].
    eapply EQ_tran; [apply Couple_sound_left; exact En | apply Couple_sound_right; exact Em].
  - intros [p E]. exact (IN_sound_left (pair_repr p) x _ (EQ_sym _ _ E) (pair_repr_member p)).
Qed.

Definition pairing_graph := sup (nat * nat)
  (fun p => Couple (pair_repr p) (numeral (Cantor.to_nat p))).
Lemma pairing_application x y : application pairing_graph x y <->
  exists p, EQ x (pair_repr p) /\ EQ y (numeral (Cantor.to_nat p)).
Proof.
  split.
  - intros [p E]. exists p; split;
      [exact (Couple_inj_left _ _ _ _ E) | exact (Couple_inj_right _ _ _ _ E)].
  - intros [p [Ex Ey]]. exists p.
    eapply EQ_tran; [apply Couple_sound_left; exact Ex | apply Couple_sound_right; exact Ey].
Qed.
Lemma pairing_graph_bound :
  INC pairing_graph (Prod (Prod omega_codes omega_codes) omega_codes).
Proof.
  intros e [p E]. apply (IN_sound_left _ e _ (EQ_sym _ _ E)).
  apply Couple_IN_Prod; [apply pair_repr_member | apply numeral_in_omega].
Qed.
Lemma pairing_graph_laws :
  function_laws (Prod omega_codes omega_codes) (fun _ => omega_codes) pairing_graph.
Proof.
  split.
  - intros x Hx. apply omega_pair_membership in Hx as [p E].
    exists (numeral (Cantor.to_nat p)). apply pairing_application.
    exists p; split; [exact E | apply EQ_refl].
  - split.
    + intros x y H. apply pairing_application in H as [p [Ex Ey]]. split.
      * apply omega_pair_membership; exists p; exact Ex.
      * apply omega_membership; exists (Cantor.to_nat p); exact Ey.
    + intros x y z Hy Hz.
      apply pairing_application in Hy as [p [Ex Ey]].
      apply pairing_application in Hz as [q [Ex' Ez]].
      assert (Epq : p = q).
      { apply pair_repr_injective. exact (EQ_tran _ _ _ (EQ_sym _ _ Ex) Ex'). }
      subst q. exact (EQ_tran _ _ _ Ey (EQ_sym _ _ Ez)).
Qed.

Theorem countable_pairing_bijection :
  bijection (Prod omega_codes omega_codes) omega_codes pairing_graph.
Proof.
  split.
  - apply bounded_function_member; [apply pairing_graph_bound | apply pairing_graph_laws].
  - split.
    + intros x x' y H H'.
      apply pairing_application in H as [p [Ex Ey]].
      apply pairing_application in H' as [q [Ex' Ey']].
      assert (E : Cantor.to_nat p = Cantor.to_nat q).
      { apply numeral_injective. exact (EQ_tran _ _ _ (EQ_sym _ _ Ey) Ey'). }
      assert (Epq : p = q).
      { rewrite <- (Cantor.cancel_of_to p), <- (Cantor.cancel_of_to q). now rewrite E. }
      subst q. exact (EQ_tran _ _ _ Ex (EQ_sym _ _ Ex')).
    + intros y Hy. apply omega_membership in Hy as [n E].
      exists (pair_repr (Cantor.of_nat n)). apply pairing_application.
      exists (Cantor.of_nat n). split; [apply EQ_refl |].
      rewrite Cantor.cancel_to_of; exact E.
Qed.
Theorem countable_square_embeds : embeds (Prod omega_codes omega_codes) omega_codes.
Proof.
  exists pairing_graph. destruct countable_pairing_bijection as [Hf [Hi _]]. split; assumption.
Qed.
Theorem countable_square_equinumerous : equinumerous (Prod omega_codes omega_codes) omega_codes.
Proof. exists pairing_graph; apply countable_pairing_bijection. Qed.

Theorem square_absorption_subset_exponent K : embeds (Prod K K) K ->
  embeds (dependent_product K (fun _ => Power K)) (Power K).
Proof.
  intro HK. eapply embeds_transitive; [apply subset_function_embeds |].
  apply powerset_embeds; exact HK.
Qed.
Theorem countable_subset_exponent :
  embeds (dependent_product omega_codes (fun _ => Power omega_codes)) (Power omega_codes).
Proof. apply square_absorption_subset_exponent, countable_square_embeds. Qed.
Theorem countable_dependent_subset_exponent B enc :
  (forall x, IN x omega_codes -> injection (B x) (Power omega_codes) (apply_set enc x)) ->
  embeds (dependent_product omega_codes B) (Power omega_codes).
Proof.
  intro HB. eapply embeds_transitive.
  - apply (dependent_subset_product_bound omega_codes omega_codes B enc); exact HB.
  - apply powerset_embeds, countable_square_embeds.
Qed.

Print Assumptions square_absorption_subset_exponent.
Print Assumptions countable_subset_exponent.
Print Assumptions countable_dependent_subset_exponent.
Print Assumptions omega_pair_membership.
Print Assumptions countable_pairing_bijection.
Print Assumptions countable_square_embeds.
Print Assumptions countable_square_equinumerous.
Check countable_pairing_bijection.
