(** The constructive first step of the cardinal bound: fiberwise set
    injections induce an injection of dependent function sets. This does
    not choose fiber injections or assume/prove the missing GCH bound. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections.

Definition injection (A B f : Ens) : Prop :=
  IN f (dependent_product A (fun _ => B)) /\
  (forall x x' y, application f x y -> application f x' y -> EQ x x').
Definition embeds A B : Prop := exists f, injection A B f.

Lemma injection_values A B f x x' :
  injection A B f -> IN x A -> IN x' A ->
  EQ (apply_set f x) (apply_set f x') -> EQ x x'.
Proof.
  intros [Hf Hinj] Hx Hx' E. apply (Hinj x x' (apply_set f x')).
  - eapply application_arguments; [apply EQ_refl | apply EQ_refl | exact E |].
    apply (apply_set_spec A (fun _ => B)); assumption.
  - apply (apply_set_spec A (fun _ => B)); assumption.
Qed.
Lemma graph_extensional_on A f h :
  family_extensional f -> family_extensional h ->
  (forall x, IN x A -> EQ (f x) (h x)) -> EQ (graph A f) (graph A h).
Proof.
  intros Hf Hh Hp. apply INC_EQ; intros e [i E].
  - apply (IN_sound_left (Couple (pi2 A i) (f (pi2 A i))) e _ (EQ_sym _ _ E)).
    eapply application_arguments; [apply EQ_refl | apply EQ_refl | |].
    + apply EQ_sym, Hp, index_member.
    + exact (graph_beta A h (pi2 A i) Hh (index_member A i)).
  - apply (IN_sound_left (Couple (pi2 A i) (h (pi2 A i))) e _ (EQ_sym _ _ E)).
    eapply application_arguments; [apply EQ_refl | apply EQ_refl | |].
    + apply Hp, index_member.
    + exact (graph_beta A f (pi2 A i) Hf (index_member A i)).
Qed.
Lemma graph_injection A B f :
  family_extensional f -> (forall x, IN x A -> IN (f x) B) ->
  (forall x x', IN x A -> IN x' A -> EQ (f x) (f x') -> EQ x x') ->
  injection A B (graph A f).
Proof.
  intros Hf Htyped Hinj. split; [apply dependent_product_introduction; assumption |].
  intros x x' y H H'.
  destruct (graph_value A f x y Hf H) as [Hx E].
  destruct (graph_value A f x' y Hf H') as [Hx' E'].
  apply Hinj; [exact Hx | exact Hx' |].
  eapply EQ_tran; [apply EQ_sym; exact E | exact E'].
Qed.

Section Fiberwise.
Variables (A K : Ens) (B : Ens -> Ens) (enc : Ens -> Ens).
Definition encoded_body g x := apply_set (enc x) (apply_set g x).
Definition encoded_graph g := graph A (encoded_body g).
Definition product_injection := graph (dependent_product A B) encoded_graph.

Lemma encoded_body_extensional g : family_extensional enc -> family_extensional (encoded_body g).
Proof.
  intros Henc x y E. apply apply_set_extensional; [apply Henc; exact E |].
  apply apply_set_extensional; [apply EQ_refl | exact E].
Qed.
Lemma encoded_graph_extensional : family_extensional enc -> family_extensional encoded_graph.
Proof.
  intros Henc g h E. apply graph_extensional_on;
    [apply encoded_body_extensional; exact Henc | apply encoded_body_extensional; exact Henc |].
  intros x Hx. apply apply_set_extensional; [apply EQ_refl |].
  apply apply_set_extensional; [exact E | apply EQ_refl].
Qed.
Lemma encoded_graph_typed :
  family_extensional enc -> (forall x, IN x A -> injection (B x) K (enc x)) ->
  forall g, IN g (dependent_product A B) ->
  IN (encoded_graph g) (dependent_product A (fun _ => K)).
Proof.
  intros Henc Hinj g Hg. apply dependent_product_introduction.
  - apply encoded_body_extensional; exact Henc.
  - intros x Hx. apply (apply_set_typed (B x) (fun _ => K)).
    + exact (proj1 (Hinj x Hx)).
    + apply (apply_set_typed A B); assumption.
Qed.
Lemma encoded_graph_injective :
  family_extensional enc -> (forall x, IN x A -> injection (B x) K (enc x)) ->
  forall g h, IN g (dependent_product A B) -> IN h (dependent_product A B) ->
  EQ (encoded_graph g) (encoded_graph h) -> EQ g h.
Proof.
  intros Henc Hinj g h Hg Hh E.
  apply (dependent_product_extensionality A B); [exact Hg | exact Hh |].
  intros x Hx. apply (injection_values (B x) K (enc x)).
  - apply Hinj; exact Hx.
  - apply (apply_set_typed A B); assumption.
  - apply (apply_set_typed A B); assumption.
  - eapply EQ_tran.
    + apply EQ_sym. apply (apply_set_beta A (encoded_body g) x).
      * apply encoded_body_extensional; exact Henc.
      * exact Hx.
    + eapply EQ_tran.
      * apply apply_set_extensional; [exact E | apply EQ_refl].
      * apply (apply_set_beta A (encoded_body h) x).
        -- apply encoded_body_extensional; exact Henc.
        -- exact Hx.
Qed.
Theorem dependent_product_injection :
  family_extensional enc -> (forall x, IN x A -> injection (B x) K (enc x)) ->
  injection (dependent_product A B) (dependent_product A (fun _ => K)) product_injection.
Proof.
  intros Henc Hinj. apply graph_injection.
  - apply encoded_graph_extensional; exact Henc.
  - apply encoded_graph_typed; assumption.
  - apply encoded_graph_injective; assumption.
Qed.
Theorem dependent_product_embeds :
  family_extensional enc -> (forall x, IN x A -> injection (B x) K (enc x)) ->
  embeds (dependent_product A B) (dependent_product A (fun _ => K)).
Proof.
  intros Henc Hinj. exists product_injection. apply dependent_product_injection; assumption.
Qed.
End Fiberwise.

(** When the family of fiber injections is itself represented by a set
    graph, extensionality follows from concrete application; it need not
    be an extra hypothesis of the cardinal-bound step. *)
Theorem dependent_product_injection_from_graph A K B enc :
  (forall x, IN x A -> injection (B x) K (apply_set enc x)) ->
  injection (dependent_product A B) (dependent_product A (fun _ => K))
    (product_injection A B (apply_set enc)).
Proof.
  intro H. apply dependent_product_injection; [| exact H].
  intros x y E. apply apply_set_extensional; [apply EQ_refl | exact E].
Qed.

Print Assumptions graph_extensional_on.
Print Assumptions graph_injection.
Print Assumptions encoded_graph_typed.
Print Assumptions encoded_graph_injective.
Print Assumptions dependent_product_injection.
Print Assumptions dependent_product_embeds.
Print Assumptions dependent_product_injection_from_graph.
Check dependent_product_injection.
Check dependent_product_injection_from_graph.
