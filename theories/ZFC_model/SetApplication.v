(** Choice-free functional application for the concrete set graphs.
    This is not yet the coded interpretation of PTS application: the paper's
    cardinal-coding bijections and their inverses still have to be built. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions.

Lemma application_arguments g h x x' y y' :
  EQ g h -> EQ x x' -> EQ y y' ->
  application g x y -> application h x' y'.
Proof.
  intros Eg Ex Ey H. unfold application in *.
  eapply IN_sound_right; [exact Eg |].
  eapply IN_sound_left; [| exact H].
  eapply EQ_tran; [apply Couple_sound_left; exact Ex |].
  apply Couple_sound_right; exact Ey.
Qed.

(** This library uses Couple x y = {{x},{empty,{y}}}, not the usual
    Kuratowski pair. Three unions, not two, therefore bound its values. *)
Definition value_bound (g : Ens) := Union (Union (Union g)).
Lemma application_value_bound g x y :
  application g x y -> IN y (value_bound g).
Proof.
  intro H. unfold value_bound.
  eapply IN_Union with (E' := Sing y); [| apply IN_Sing].
  eapply IN_Union with (E' := Paire Vide (Sing y)); [| apply IN_Paire_right].
  eapply IN_Union with (E' := Couple x y); [exact H | apply IN_Paire_right].
Qed.
Definition value_fiber (g x : Ens) : Ens :=
  Comp (value_bound g) (fun y => application g x y).
Definition apply_set (g x : Ens) : Ens := Union (value_fiber g x).

Lemma value_fiber_spec g x y :
  IN y (value_fiber g x) <-> application g x y.
Proof.
  unfold value_fiber. split.
  - apply IN_Comp_P. intros a b H E.
    eapply application_arguments; [apply EQ_refl | apply EQ_refl | exact E | exact H].
  - intro H. apply IN_P_Comp.
    + intros a b Ha E.
      eapply application_arguments; [apply EQ_refl | apply EQ_refl | exact E | exact Ha].
    + eapply application_value_bound; exact H.
    + exact H.
Qed.
Lemma value_fiber_extensional g h x x' :
  EQ g h -> EQ x x' -> EQ (value_fiber g x) (value_fiber h x').
Proof.
  intros Eg Ex. apply INC_EQ; intros y Hy; apply value_fiber_spec in Hy;
    apply value_fiber_spec.
  - eapply application_arguments; [exact Eg | exact Ex | apply EQ_refl | exact Hy].
  - eapply application_arguments; [apply EQ_sym; exact Eg | apply EQ_sym; exact Ex |
      apply EQ_refl | exact Hy].
Qed.
Theorem apply_set_extensional g h x x' :
  EQ g h -> EQ x x' -> EQ (apply_set g x) (apply_set h x').
Proof. intros Eg Ex. apply Union_sound, value_fiber_extensional; assumption. Qed.

Theorem apply_set_value g x y :
  application g x y ->
  (forall z, application g x z -> EQ z y) -> EQ (apply_set g x) y.
Proof.
  intros Hxy HU. apply INC_EQ; intros z Hz.
  - destruct (Union_IN (value_fiber g x) z Hz) as [v [Hv Hzv]].
    apply value_fiber_spec in Hv.
    exact (IN_sound_right z v y (HU v Hv) Hzv).
  - apply (IN_Union (value_fiber g x) y z); [apply value_fiber_spec; exact Hxy | exact Hz].
Qed.
Theorem apply_set_beta A f x :
  family_extensional f -> IN x A -> EQ (apply_set (graph A f) x) (f x).
Proof.
  intros Hf Hx. apply apply_set_value.
  - apply graph_beta; assumption.
  - intros z Hz. exact (proj2 (graph_value A f x z Hf Hz)).
Qed.
Theorem apply_set_typed A B g x :
  IN g (dependent_product A B) -> IN x A -> IN (apply_set g x) (B x).
Proof.
  intros Hg Hx.
  destruct (dependent_product_application A B g x Hg Hx) as [y [Hxy Hy]].
  destruct (dependent_product_elimination A B g Hg) as [_ [_ HU]].
  assert (E : EQ (apply_set g x) y).
  { apply apply_set_value; [exact Hxy | intros z Hz; exact (HU x z y Hz Hxy)]. }
  exact (IN_sound_left y (apply_set g x) (B x) (EQ_sym _ _ E) Hy).
Qed.
Theorem apply_set_spec A B g x :
  IN g (dependent_product A B) -> IN x A ->
  application g x (apply_set g x).
Proof.
  intros Hg Hx.
  destruct (dependent_product_application A B g x Hg Hx) as [y [Hxy Hy]].
  destruct (dependent_product_elimination A B g Hg) as [_ [_ HU]].
  assert (E : EQ (apply_set g x) y).
  { apply apply_set_value; [exact Hxy | intros z Hz; exact (HU x z y Hz Hxy)]. }
  eapply application_arguments; [apply EQ_refl | apply EQ_refl | apply EQ_sym; exact E | exact Hxy].
Qed.

Lemma dependent_product_pair A B g e :
  IN g (dependent_product A B) -> IN e g ->
  exists x y, EQ (Couple x y) e /\ IN x A /\ application g x y.
Proof.
  intros Hg He.
  pose proof (Comp_INC _ _ g Hg) as Hpower.
  pose proof (IN_Power_INC _ _ Hpower e He) as Hpair.
  destruct (IN_Prod_EXType _ _ _ Hpair) as [x [y E]].
  assert (Hxy : application g x y).
  { exact (IN_sound_left e (Couple x y) g (EQ_sym _ _ E) He). }
  destruct (dependent_product_elimination A B g Hg) as [_ [HB _]].
  exists x, y. split; [exact E |]. split; [exact (proj1 (HB x y Hxy)) | exact Hxy].
Qed.

(** Set graph extensionality is proved, not a functional-extensionality axiom.
    Eta here is a theorem about sets; no eta rule is added to PTS conversion. *)
Theorem apply_set_eta A B g :
  IN g (dependent_product A B) -> EQ (graph A (apply_set g)) g.
Proof.
  intro Hg.
  assert (Hext : family_extensional (apply_set g)).
  { intros x y E. apply apply_set_extensional; [apply EQ_refl | exact E]. }
  apply INC_EQ.
  - intros e He. destruct He as [i E].
    apply (IN_sound_left (Couple (pi2 A i) (apply_set g (pi2 A i))) e g).
    + apply EQ_sym; exact E.
    + apply (apply_set_spec A B); [exact Hg | apply index_member].
  - intros e He.
    destruct (dependent_product_pair A B g e Hg He) as [x [y [E [Hx Hxy]]]].
    destruct (dependent_product_elimination A B g Hg) as [_ [_ HU]].
    assert (Ey : EQ (apply_set g x) y).
    { apply apply_set_value; [exact Hxy | intros z Hz; exact (HU x z y Hz Hxy)]. }
    apply (IN_sound_left (Couple x y) e _ E).
    apply (IN_sound_left (Couple x (apply_set g x)) (Couple x y) _).
    + apply Couple_sound_right; exact Ey.
    + apply graph_beta; assumption.
Qed.
Theorem dependent_product_extensionality A B g h :
  IN g (dependent_product A B) -> IN h (dependent_product A B) ->
  (forall x, IN x A -> EQ (apply_set g x) (apply_set h x)) -> EQ g h.
Proof.
  intros Hg Hh Hpoint. apply INC_EQ.
  - intros e He.
    destruct (dependent_product_pair A B g e Hg He) as [x [y [E [Hx Hxy]]]].
    destruct (dependent_product_elimination A B g Hg) as [_ [_ HU]].
    assert (Ey : EQ y (apply_set h x)).
    { eapply EQ_tran; [apply EQ_sym; apply apply_set_value; [exact Hxy |
        intros z Hz; exact (HU x z y Hz Hxy)] | apply Hpoint; exact Hx]. }
    apply (IN_sound_left (Couple x y) e _ E).
    eapply application_arguments; [apply EQ_refl | apply EQ_refl | apply EQ_sym; exact Ey |].
    apply (apply_set_spec A B); assumption.
  - intros e He.
    destruct (dependent_product_pair A B h e Hh He) as [x [y [E [Hx Hxy]]]].
    destruct (dependent_product_elimination A B h Hh) as [_ [_ HU]].
    assert (Ey : EQ y (apply_set g x)).
    { eapply EQ_tran; [apply EQ_sym; apply apply_set_value; [exact Hxy |
        intros z Hz; exact (HU x z y Hz Hxy)] | apply EQ_sym; apply Hpoint; exact Hx]. }
    apply (IN_sound_left (Couple x y) e _ E).
    eapply application_arguments; [apply EQ_refl | apply EQ_refl | apply EQ_sym; exact Ey |].
    apply (apply_set_spec A B); assumption.
Qed.

Print Assumptions apply_set_extensional.
Print Assumptions apply_set_beta.
Print Assumptions apply_set_typed.
Print Assumptions apply_set_spec.
Print Assumptions apply_set_eta.
Print Assumptions dependent_product_extensionality.
