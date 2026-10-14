(** Set-theoretic dependent function graphs for the paper's proposed model.
    These are concrete constructions in the pinned rocq-archive/zfc library,
    not an assumed PTS model. Cardinal codes, GCH bounds, coding bijections,
    term interpretation and the typing soundness theorem remain to be built. *)
From ZFC Require Import Sets Axioms Cartesian.

Definition family_extensional (B : Ens -> Ens) : Prop :=
  forall x y, EQ x y -> EQ (B x) (B y).

Definition family_range (A : Ens) (B : Ens -> Ens) : Ens :=
  sup (pi1 A) (fun i => B (pi2 A i)).
Definition graph (A : Ens) (f : Ens -> Ens) : Ens :=
  sup (pi1 A) (fun i => Couple (pi2 A i) (f (pi2 A i))).
Definition application (g x y : Ens) : Prop := IN (Couple x y) g.

Definition function_laws (A : Ens) (B : Ens -> Ens) (g : Ens) : Prop :=
  (forall x, IN x A -> exists y, application g x y) /\
  (forall x y, application g x y -> IN x A /\ IN y (B x)) /\
  (forall x y z, application g x y -> application g x z -> EQ y z).

(** A subset of an actual powerset, rather than a meta-level collection of
    all functions Ens -> Ens (which would exceed Ens's indexing universe). *)
Definition dependent_product (A : Ens) (B : Ens -> Ens) : Ens :=
  Comp (Power (Prod A (Union (family_range A B)))) (function_laws A B).

Lemma application_extensional g h x y :
  EQ g h -> application g x y -> application h x y.
Proof. exact (IN_sound_right (Couple x y) g h). Qed.
Lemma function_laws_extensional A B g h :
  function_laws A B g -> EQ g h -> function_laws A B h.
Proof.
  intros [HT [HB HU]] E. split.
  - intros x Hx. destruct (HT x Hx) as [y Hy]. exists y.
    exact (application_extensional g h x y E Hy).
  - split.
    + intros x y H. apply HB.
      exact (application_extensional h g x y (EQ_sym _ _ E) H).
    + intros x y z H J. apply (HU x).
      * exact (application_extensional h g x y (EQ_sym _ _ E) H).
      * exact (application_extensional h g x z (EQ_sym _ _ E) J).
Qed.
Lemma dependent_product_elimination A B g :
  IN g (dependent_product A B) -> function_laws A B g.
Proof.
  unfold dependent_product. apply IN_Comp_P.
  intros x y H E. exact (function_laws_extensional A B x y H E).
Qed.
Lemma dependent_product_application A B g x :
  IN g (dependent_product A B) -> IN x A ->
  exists y, application g x y /\ IN y (B x).
Proof.
  intros Hg Hx. destruct (dependent_product_elimination A B g Hg) as [HT [HB HU]].
  destruct (HT x Hx) as [y Hy]. exists y. split; [exact Hy | exact (proj2 (HB x y Hy))].
Qed.
Lemma dependent_product_empty_fiber A B x :
  IN x A -> EQ (B x) Vide -> forall g, ~ IN g (dependent_product A B).
Proof.
  intros Hx E g Hg.
  destruct (dependent_product_application A B g x Hg Hx) as [y [_ Hy]].
  pose proof (IN_sound_right y (B x) Vide E Hy) as Hempty.
  destruct (Vide_est_vide y Hempty).
Qed.

Lemma index_member A (i : pi1 A) : IN (pi2 A i) A.
Proof. destruct A as [I a]. exists i. apply EQ_refl. Qed.

Lemma graph_beta A f x :
  family_extensional f -> IN x A -> application (graph A f) x (f x).
Proof.
  intros Hf Hx. destruct (IN_EXType A x Hx) as [i E].
  unfold application, graph, IN. exists i.
  eapply EQ_tran.
  - exact (Couple_sound_left x (pi2 A i) (f x) E).
  - apply Couple_sound_right. apply Hf. exact E.
Qed.
Lemma graph_value A f x y :
  family_extensional f -> application (graph A f) x y ->
  IN x A /\ EQ y (f x).
Proof.
  intros Hf H. destruct H as [i E].
  pose proof (Couple_inj_left _ _ _ _ E) as Ex.
  pose proof (Couple_inj_right _ _ _ _ E) as Ey.
  split.
  - exact (IN_sound_left (pi2 A i) x A (EQ_sym _ _ Ex) (index_member A i)).
  - eapply EQ_tran; [exact Ey |]. apply EQ_sym. apply Hf. exact Ex.
Qed.
Lemma graph_function_laws A B f :
  family_extensional f -> (forall x, IN x A -> IN (f x) (B x)) ->
  function_laws A B (graph A f).
Proof.
  intros Hf Htyped. split.
  - intros x Hx. exists (f x). apply graph_beta; assumption.
  - split.
    + intros x y H. destruct (graph_value A f x y Hf H) as [Hx E].
      split; [exact Hx |].
      exact (IN_sound_left (f x) y (B x) (EQ_sym _ _ E) (Htyped x Hx)).
    + intros x y z H J.
      destruct (graph_value A f x y Hf H) as [_ E].
      destruct (graph_value A f x z Hf J) as [_ E'].
      exact (EQ_tran y (f x) z E (EQ_sym _ _ E')).
Qed.
Lemma graph_bound A B f :
  (forall x, IN x A -> IN (f x) (B x)) ->
  INC (graph A f) (Prod A (Union (family_range A B))).
Proof.
  intros Hf e H. destruct H as [i E].
  apply (IN_sound_left (Couple (pi2 A i) (f (pi2 A i))) e _ (EQ_sym _ _ E)).
  apply Couple_IN_Prod.
  - apply index_member.
  - apply (IN_Union (family_range A B) (B (pi2 A i))).
    + exists i. apply EQ_refl.
    + apply Hf. apply index_member.
Qed.
Lemma dependent_product_introduction A B f :
  family_extensional f -> (forall x, IN x A -> IN (f x) (B x)) ->
  IN (graph A f) (dependent_product A B).
Proof.
  intros Hf Htyped. unfold dependent_product. apply IN_P_Comp.
  - intros g h H E. exact (function_laws_extensional A B g h H E).
  - apply INC_IN_Power. apply graph_bound. exact Htyped.
  - apply graph_function_laws; assumption.
Qed.
Lemma graph_application_unique A f x y :
  family_extensional f -> IN x A ->
  (application (graph A f) x y <-> EQ y (f x)).
Proof.
  intros Hf Hx. split.
  - intro H. exact (proj2 (graph_value A f x y Hf H)).
  - intro E. unfold application.
    apply (IN_sound_left (Couple x (f x)) (Couple x y) (graph A f)).
    + apply Couple_sound_right. apply EQ_sym. exact E.
    + apply graph_beta; assumption.
Qed.

Print Assumptions dependent_product_introduction.
Print Assumptions graph_beta.
Print Assumptions graph_application_unique.
Print Assumptions dependent_product_application.
Print Assumptions dependent_product_empty_fiber.
