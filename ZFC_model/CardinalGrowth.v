(** Constructive Cantor diagonal and strict powerset growth. This is cardinal
    infrastructure, not an identification of powerset iterates with alephs
    and not a substitute for the manuscript's GCH product bound. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections ProductEmbedding.

Definition diagonal (A : Ens) (f : Ens -> Ens) := Comp A (fun x => ~ IN x (f x)).
Lemma diagonal_predicate f : family_extensional f ->
  forall x y, (~ IN x (f x)) -> EQ x y -> ~ IN y (f y).
Proof.
  intros Hf x y Hx E Hy. apply Hx.
  eapply IN_sound_right; [apply Hf; apply EQ_sym; exact E |].
  exact (IN_sound_left y x (f y) (EQ_sym _ _ E) Hy).
Qed.
Theorem cantor_no_surjection A f : family_extensional f ->
  ~ (forall y, IN y (Power A) -> exists x, IN x A /\ EQ (f x) y).
Proof.
  intros Hf Hsurj.
  assert (HD : IN (diagonal A f) (Power A)).
  { apply INC_IN_Power, Comp_INC. }
  destruct (Hsurj _ HD) as [x [Hx E]].
  assert (Hnot : ~ IN x (f x)).
  { intro Hin.
    pose proof (IN_sound_right x (f x) (diagonal A f) E Hin) as Hdiag.
    exact (IN_Comp_P A x _ (diagonal_predicate f Hf) Hdiag Hin). }
  apply Hnot.
  apply (IN_sound_right x (diagonal A f) (f x) (EQ_sym _ _ E)).
  apply IN_P_Comp; [apply diagonal_predicate; exact Hf | exact Hx | exact Hnot].
Qed.
Theorem cantor_no_bijection A : ~ equinumerous A (Power A).
Proof.
  intros [f Hf]. apply (cantor_no_surjection A (apply_set f)).
  - intros x y E. apply apply_set_extensional; [apply EQ_refl | exact E].
  - intros y Hy. apply (bijection_surjective_value A (Power A)); assumption.
Qed.
Theorem cantor_no_injection A : ~ embeds (Power A) A.
Proof.
  intros [f [Hf Hinj]].
  apply (cantor_no_surjection A (apply_set (inverse (Power A) A f))).
  - intros x y E. apply apply_set_extensional; [apply EQ_refl | exact E].
  - intros y Hy. exists (apply_set f y). split.
    + apply (apply_set_typed (Power A) (fun _ => A)); assumption.
    + apply apply_set_value.
      * apply inverse_application. split; [exact Hy |]. split.
        -- apply (apply_set_typed (Power A) (fun _ => A)); assumption.
        -- apply (apply_set_spec (Power A) (fun _ => A)); assumption.
      * intros z Hz. apply inverse_application in Hz as [_ [_ Hz]].
        apply (Hinj z y (apply_set f y)); [exact Hz |].
        apply (apply_set_spec (Power A) (fun _ => A)); assumption.
Qed.
Theorem embeds_powerset A : embeds A (Power A).
Proof.
  exists (graph A Sing). apply graph_injection.
  - intros x y E; apply Sing_sound; exact E.
  - intros x Hx. apply INC_IN_Power. intros y Hy.
    exact (IN_sound_left x y A (EQ_sym _ _ (IN_Sing_EQ y x Hy)) Hx).
  - intros x y Hx Hy E. apply EQ_Sing_EQ; exact E.
Qed.
Lemma embeds_reflexive A : embeds A A.
Proof.
  exists (graph A (fun x => x)). apply graph_injection;
    [intros x y E; exact E | auto | intros x y Hx Hy E; exact E].
Qed.
Theorem embeds_transitive A B C : embeds A B -> embeds B C -> embeds A C.
Proof.
  intros [f Hf] [g Hg]. exists (compose A f g). apply graph_injection.
  - apply composite_extensional.
  - intros x Hx. apply (apply_set_typed B (fun _ => C)); [exact (proj1 Hg) |].
    apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) | exact Hx].
  - intros x y Hx Hy E. apply (injection_values A B f x y Hf Hx Hy).
    apply (injection_values B C g _ _ Hg).
    + apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) | exact Hx].
    + apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) | exact Hy].
    + exact E.
Qed.
Fixpoint iterated_power (A : Ens) n : Ens :=
  match n with 0 => A | S n => Power (iterated_power A n) end.
Theorem iterated_power_monotone A i j : i <= j -> embeds (iterated_power A i) (iterated_power A j).
Proof.
  intro H; induction H; [apply embeds_reflexive |].
  eapply embeds_transitive; [exact IHle | apply embeds_powerset].
Qed.
Theorem iterated_power_strict A i j : i < j -> ~ embeds (iterated_power A j) (iterated_power A i).
Proof.
  intros Hlt Hback. apply (cantor_no_injection (iterated_power A i)).
  eapply embeds_transitive; [| exact Hback].
  apply (iterated_power_monotone A (S i) j); exact Hlt.
Qed.

Print Assumptions cantor_no_surjection.
Print Assumptions cantor_no_bijection.
Print Assumptions cantor_no_injection.
Print Assumptions embeds_powerset.
Print Assumptions embeds_transitive.
Print Assumptions iterated_power_monotone.
Print Assumptions iterated_power_strict.
Check cantor_no_injection.
Check iterated_power_strict.
