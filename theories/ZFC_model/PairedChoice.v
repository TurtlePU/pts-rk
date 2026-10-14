(** Choose related witnesses together, preserving their joint predicate. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SelectedCodes
  CountableDichotomy BoundedChoice.

Lemma pair_components_typed B C e : IN e (Prod B C) ->
  IN (pair_first B C e) B /\ IN (pair_second B C e) C.
Proof.
  intro He. destruct (IN_Prod_EXType B C e He) as [b [c E]].
  pose proof (Couple_Prod_IN B C b c (IN_sound_left e _ _ (EQ_sym _ _ E) He)) as [Hb Hc].
  split.
  - eapply IN_sound_left; [apply EQ_sym; apply (pair_first_beta B C e b c Hb Hc); apply EQ_sym; exact E | exact Hb].
  - eapply IN_sound_left; [apply EQ_sym; apply (pair_second_beta B C e b c Hb Hc); apply EQ_sym; exact E | exact Hc].
Qed.

Definition ternary_extensional (P : Ens -> Ens -> Ens -> Prop) :=
  forall x x' y y' z z', EQ x x' -> EQ y y' -> EQ z z' -> (P x y z <-> P x' y' z').

Theorem paired_relation_choice (AC : family_choice) A B C P :
  ternary_extensional P ->
  (forall x, IN x A -> exists y z, IN y B /\ IN z C /\ P x y z) ->
  exists b c, family_extensional b /\ family_extensional c /\
    IN (graph A b) (dependent_product A (fun _ => B)) /\
    IN (graph A c) (dependent_product A (fun _ => C)) /\
    (forall x, IN x A -> IN (b x) B /\ IN (c x) C /\ P x (b x) (c x)).
Proof.
  intros EP HT.
  set (R := fun x e => P x (pair_first B C e) (pair_second B C e)).
  assert (ER : relation_extensional R).
  { intros x x' e e' Ex Ee. apply EP; [exact Ex | |];
      apply apply_set_extensional; [apply EQ_refl | exact Ee | apply EQ_refl | exact Ee]. }
  assert (HR : forall x, IN x A -> exists e, IN e (Prod B C) /\ R x e).
  { intros x Hx. destruct (HT x Hx) as [y [z [Hy [Hz HP]]]].
    exists (Couple y z); split; [apply Couple_IN_Prod; assumption |].
    apply (proj1 (EP x x y (pair_first B C (Couple y z)) z (pair_second B C (Couple y z))
      (EQ_refl x) (EQ_sym _ _ (pair_first_beta B C _ y z Hy Hz (EQ_refl _)))
      (EQ_sym _ _ (pair_second_beta B C _ y z Hy Hz (EQ_refl _))))); exact HP. }
  destruct (bounded_relation_choice AC A (Prod B C) R ER HR) as [f [Ef [_ Hf]]].
  set (b := fun x => pair_first B C (f x)).
  set (c := fun x => pair_second B C (f x)).
  assert (Eb : family_extensional b).
  { intros x y E; apply apply_set_extensional; [apply EQ_refl | apply Ef; exact E]. }
  assert (Ec : family_extensional c).
  { intros x y E; apply apply_set_extensional; [apply EQ_refl | apply Ef; exact E]. }
  assert (Ht : forall x, IN x A -> IN (b x) B /\ IN (c x) C /\ P x (b x) (c x)).
  { intros x Hx. destruct (Hf x Hx) as [Hpair HP].
    destruct (pair_components_typed B C (f x) Hpair) as [Hb Hc]. auto. }
  exists b, c; split; [exact Eb |]. split; [exact Ec |]. split.
  - apply dependent_product_introduction; [exact Eb | intros x Hx; exact (proj1 (Ht x Hx))].
  - split; [apply dependent_product_introduction; [exact Ec | intros x Hx; exact (proj1 (proj2 (Ht x Hx)))] | exact Ht].
Qed.
Print Assumptions paired_relation_choice.
