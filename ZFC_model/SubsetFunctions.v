(** Subset-valued functions embed into the powerset of a Cartesian product.
    This is the set-level exponent step; no GCH or cardinal bound assumed. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections ProductEmbedding CardinalGrowth.

Definition member_edge f e := exists x y, EQ e (Couple x y) /\ IN y (apply_set f x).
Lemma member_edge_extensional f e e' :
  member_edge f e -> EQ e e' -> member_edge f e'.
Proof.
  intros [x [y [E H]]] E'. exists x, y; split; [| exact H].
  eapply EQ_tran; [apply EQ_sym; exact E' | exact E].
Qed.
Definition flatten A B f := Comp (Prod A B) (member_edge f).
Lemma flatten_pair A B f x y :
  IN (Couple x y) (flatten A B f) <-> IN x A /\ IN y B /\ IN y (apply_set f x).
Proof.
  split.
  - intro H.
    destruct (Couple_Prod_IN _ _ _ _ (Comp_INC _ _ _ H)) as [Hx Hy].
    pose proof (IN_Comp_P _ _ _ (member_edge_extensional f) H) as Hr.
    destruct Hr as [x' [y' [E Hin]]].
    pose proof (Couple_inj_left _ _ _ _ E) as Ex.
    pose proof (Couple_inj_right _ _ _ _ E) as Ey.
    split; [exact Hx |]. split; [exact Hy |].
    eapply IN_sound_right.
    + apply apply_set_extensional; [apply EQ_refl | apply EQ_sym; exact Ex].
    + exact (IN_sound_left y' y _ (EQ_sym _ _ Ey) Hin).
  - intros [Hx [Hy Hin]]. apply IN_P_Comp.
    + apply member_edge_extensional.
    + apply Couple_IN_Prod; assumption.
    + exists x, y; split; [apply EQ_refl | exact Hin].
Qed.
Lemma flatten_inclusion A B f g : EQ f g -> INC (flatten A B f) (flatten A B g).
Proof.
  intros E e He. apply IN_P_Comp.
  - apply member_edge_extensional.
  - exact (Comp_INC _ _ _ He).
  - pose proof (IN_Comp_P _ _ _ (member_edge_extensional f) He) as Hr.
    destruct Hr as [x [y [Exy Hin]]]. exists x, y; split; [exact Exy |].
    eapply IN_sound_right; [apply apply_set_extensional; [exact E | apply EQ_refl] | exact Hin].
Qed.
Lemma flatten_extensional A B f g : EQ f g -> EQ (flatten A B f) (flatten A B g).
Proof. intro E; apply INC_EQ; apply flatten_inclusion; [exact E | apply EQ_sym; exact E]. Qed.
Lemma flatten_fiber_inclusion A B f g :
  IN f (dependent_product A (fun _ => Power B)) ->
  INC (flatten A B f) (flatten A B g) -> forall x, IN x A ->
  INC (apply_set f x) (apply_set g x).
Proof.
  intros Hf Hinc x Hx y Hy.
  assert (HyB : IN y B).
  { apply (IN_Power_INC B (apply_set f x)); [| exact Hy].
    apply (apply_set_typed A (fun _ => Power B)); assumption. }
  assert (Hpair : IN (Couple x y) (flatten A B f)).
  { apply flatten_pair; auto. }
  pose proof (Hinc _ Hpair) as Hpair'. apply flatten_pair in Hpair' as [_ [_ H]]. exact H.
Qed.
Theorem flatten_injective A B f g :
  IN f (dependent_product A (fun _ => Power B)) ->
  IN g (dependent_product A (fun _ => Power B)) ->
  EQ (flatten A B f) (flatten A B g) -> EQ f g.
Proof.
  intros Hf Hg E. apply (dependent_product_extensionality A (fun _ => Power B));
    [exact Hf | exact Hg |].
  intros x Hx. apply INC_EQ.
  - apply (flatten_fiber_inclusion A B f g Hf); [apply EQ_INC; exact E | exact Hx].
  - apply (flatten_fiber_inclusion A B g f Hg); [apply EQ_INC, EQ_sym; exact E | exact Hx].
Qed.
Definition flatten_graph A B := graph (dependent_product A (fun _ => Power B)) (flatten A B).
Theorem subset_function_injection A B :
  injection (dependent_product A (fun _ => Power B)) (Power (Prod A B)) (flatten_graph A B).
Proof.
  apply graph_injection.
  - intros f g E; apply flatten_extensional; exact E.
  - intros f Hf. apply INC_IN_Power, Comp_INC.
  - intros f g Hf Hg E; apply (flatten_injective A B); assumption.
Qed.
Theorem subset_function_embeds A B :
  embeds (dependent_product A (fun _ => Power B)) (Power (Prod A B)).
Proof. exists (flatten_graph A B); apply subset_function_injection. Qed.
Theorem dependent_subset_product_bound A K B enc :
  (forall x, IN x A -> injection (B x) (Power K) (apply_set enc x)) ->
  embeds (dependent_product A B) (Power (Prod A K)).
Proof.
  intro H. eapply embeds_transitive; [| apply subset_function_embeds].
  exists (product_injection A B (apply_set enc)).
  apply dependent_product_injection_from_graph; exact H.
Qed.

Print Assumptions flatten_pair.
Print Assumptions flatten_extensional.
Print Assumptions flatten_injective.
Print Assumptions subset_function_injection.
Print Assumptions subset_function_embeds.
Print Assumptions dependent_subset_product_bound.
Check subset_function_injection.
Check dependent_subset_product_bound.
