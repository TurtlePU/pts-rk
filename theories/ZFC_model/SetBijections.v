(** Concrete graph bijections and inverses. No bijection or cardinal bound
    is postulated here. These constructions will be used by cardinal coding. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication.

Definition bijection (A B f : Ens) : Prop :=
  IN f (dependent_product A (fun _ => B)) /\
  (forall x x' y, application f x y -> application f x' y -> EQ x x') /\
  (forall y, IN y B -> exists x, application f x y).

Definition reverse_edge f e : Prop :=
  exists x y, EQ e (Couple y x) /\ application f x y.
Definition inverse (A B f : Ens) : Ens := Comp (Prod B A) (reverse_edge f).
Lemma reverse_edge_extensional f e e' :
  reverse_edge f e -> EQ e e' -> reverse_edge f e'.
Proof.
  intros [x [y [E H]]] E'. exists x, y; split; [| exact H].
  eapply EQ_tran; [apply EQ_sym; exact E' | exact E].
Qed.
Theorem inverse_application A B f x y :
  application (inverse A B f) y x <->
  IN x A /\ IN y B /\ application f x y.
Proof.
  unfold inverse, application at 1. split.
  - intro H.
    pose proof (Comp_INC _ _ _ H) as Hpair.
    destruct (Couple_Prod_IN _ _ _ _ Hpair) as [Hy Hx].
    pose proof (IN_Comp_P _ _ _ (reverse_edge_extensional f) H) as Hr.
    destruct Hr as [u [v [E Huv]]].
    pose proof (Couple_inj_left _ _ _ _ E) as Ey.
    pose proof (Couple_inj_right _ _ _ _ E) as Ex.
    split; [exact Hx |]. split; [exact Hy |].
    eapply application_arguments; [apply EQ_refl | apply EQ_sym; exact Ex |
      apply EQ_sym; exact Ey | exact Huv].
  - intros [Hx [Hy Hxy]]. apply IN_P_Comp.
    + apply reverse_edge_extensional.
    + apply Couple_IN_Prod; assumption.
    + exists x, y; split; [apply EQ_refl | exact Hxy].
Qed.

(** A graph with function laws and an actual Cartesian bound belongs to
    the constructed function set. Function laws alone do not exclude junk
    graph elements, hence the separate bound is essential. *)
Lemma bounded_function_member A B f :
  INC f (Prod A B) -> function_laws A (fun _ => B) f ->
  IN f (dependent_product A (fun _ => B)).
Proof.
  intros Hbound Hlaws. unfold dependent_product. apply IN_P_Comp.
  - intros g h H E. exact (function_laws_extensional A (fun _ => B) g h H E).
  - apply INC_IN_Power. intros e He.
    destruct (IN_Prod_EXType _ _ _ (Hbound e He)) as [x [y E]].
    assert (Hxy : application f x y).
    { exact (IN_sound_left e (Couple x y) f (EQ_sym _ _ E) He). }
    destruct Hlaws as [_ [HB _]]. destruct (HB x y Hxy) as [Hx Hy].
    apply (IN_sound_left (Couple x y) e _ E). apply Couple_IN_Prod; [exact Hx |].
    apply (IN_Union (family_range A (fun _ => B)) B y); [| exact Hy].
    destruct (IN_EXType A x Hx) as [i Ei]. exists i; apply EQ_refl.
  - exact Hlaws.
Qed.
Theorem inverse_typed A B f : bijection A B f ->
  IN (inverse A B f) (dependent_product B (fun _ => A)).
Proof.
  intros [Hf [Hinj Hsurj]]. apply bounded_function_member.
  - apply Comp_INC.
  - destruct (dependent_product_elimination A (fun _ => B) f Hf) as [HT [HB HU]].
    split.
    + intros y Hy. destruct (Hsurj y Hy) as [x Hxy]. exists x.
      apply inverse_application. split; [exact (proj1 (HB x y Hxy)) | auto].
    + split.
      * intros y x H. apply inverse_application in H as [Hx [Hy _]]. auto.
      * intros y x x' H H'. apply inverse_application in H as [_ [_ H]].
        apply inverse_application in H' as [_ [_ H']]. eapply Hinj; eassumption.
Qed.
Theorem inverse_bijection A B f : bijection A B f -> bijection B A (inverse A B f).
Proof.
  intro Hf. split; [apply inverse_typed; exact Hf |].
  destruct Hf as [Hf [Hinj Hsurj]].
  destruct (dependent_product_elimination A (fun _ => B) f Hf) as [HT [HB HU]].
  split.
  - intros y y' x H H'. apply inverse_application in H as [_ [_ H]].
    apply inverse_application in H' as [_ [_ H']]. eapply HU; eassumption.
  - intros x Hx. destruct (HT x Hx) as [y Hy]. exists y.
    apply inverse_application. split; [exact Hx |]. split; [exact (proj2 (HB x y Hy)) | exact Hy].
Qed.
Theorem inverse_left A B f x : bijection A B f -> IN x A ->
  EQ (apply_set (inverse A B f) (apply_set f x)) x.
Proof.
  intros Hf Hx. pose proof (inverse_typed A B f Hf) as Hi.
  destruct Hf as [Hf _].
  pose proof (apply_set_typed A (fun _ => B) f x Hf Hx) as Hy.
  assert (Hxy : application (inverse A B f) (apply_set f x) x).
  { apply inverse_application. split; [exact Hx |]. split; [exact Hy |].
    apply (apply_set_spec A (fun _ => B)); assumption. }
  destruct (dependent_product_elimination B (fun _ => A) _ Hi) as [_ [_ HU]].
  apply apply_set_value; [exact Hxy | intros z Hz; exact (HU _ z x Hz Hxy)].
Qed.
Theorem inverse_right A B f y : bijection A B f -> IN y B ->
  EQ (apply_set f (apply_set (inverse A B f) y)) y.
Proof.
  intros Hf Hy. pose proof (inverse_typed A B f Hf) as Hi.
  pose proof (apply_set_spec B (fun _ => A) _ y Hi Hy) as Hxy.
  apply inverse_application in Hxy as [_ [_ Hxy]].
  destruct Hf as [Hf _].
  destruct (dependent_product_elimination A (fun _ => B) _ Hf) as [_ [_ HU]].
  apply apply_set_value; [exact Hxy | intros z Hz; exact (HU _ z y Hz Hxy)].
Qed.

Definition equinumerous A B := exists f, bijection A B f.
Lemma function_value A B f x y :
  IN f (dependent_product A (fun _ => B)) -> application f x y ->
  EQ (apply_set f x) y.
Proof.
  intros Hf Hxy.
  destruct (dependent_product_elimination A (fun _ => B) f Hf) as [_ [_ HU]].
  apply apply_set_value; [exact Hxy | intros z Hz; exact (HU x z y Hz Hxy)].
Qed.
Lemma bijection_injective_value A B f x x' :
  bijection A B f -> IN x A -> IN x' A ->
  EQ (apply_set f x) (apply_set f x') -> EQ x x'.
Proof.
  intros [Hf [Hinj _]] Hx Hx' E. apply (Hinj x x' (apply_set f x')).
  - eapply application_arguments; [apply EQ_refl | apply EQ_refl | exact E |].
    apply (apply_set_spec A (fun _ => B)); assumption.
  - apply (apply_set_spec A (fun _ => B)); assumption.
Qed.
Lemma bijection_surjective_value A B f y :
  bijection A B f -> IN y B -> exists x, IN x A /\ EQ (apply_set f x) y.
Proof.
  intros [Hf [_ Hsurj]] Hy. destruct (Hsurj y Hy) as [x Hxy].
  destruct (dependent_product_elimination A (fun _ => B) f Hf) as [_ [HB _]].
  exists x; split; [exact (proj1 (HB x y Hxy)) | eapply function_value; eassumption].
Qed.
Definition compose A f g := graph A (fun x => apply_set g (apply_set f x)).
Lemma composite_extensional f g : family_extensional (fun x => apply_set g (apply_set f x)).
Proof.
  intros x y E. apply apply_set_extensional; [apply EQ_refl |].
  apply apply_set_extensional; [apply EQ_refl | exact E].
Qed.
Theorem compose_bijection A B C f g :
  bijection A B f -> bijection B C g -> bijection A C (compose A f g).
Proof.
  intros Hf Hg. split.
  - apply dependent_product_introduction; [apply composite_extensional |].
    intros x Hx. apply (apply_set_typed B (fun _ => C)); [exact (proj1 Hg) |].
    apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) | exact Hx].
  - split.
    + intros x x' y H H'.
      destruct (graph_value A _ x y (composite_extensional f g) H) as [Hx E].
      destruct (graph_value A _ x' y (composite_extensional f g) H') as [Hx' E'].
      apply (bijection_injective_value A B f x x' Hf Hx Hx').
      apply (bijection_injective_value B C g _ _ Hg).
      * apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) | exact Hx].
      * apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) | exact Hx'].
      * eapply EQ_tran; [apply EQ_sym; exact E | exact E'].
    + intros y Hy.
      destruct (bijection_surjective_value B C g y Hg Hy) as [b [Hb Eb]].
      destruct (bijection_surjective_value A B f b Hf Hb) as [a [Ha Ea]].
      exists a. eapply (application_arguments (compose A f g) (compose A f g)
        a a (apply_set g (apply_set f a)) y); [apply EQ_refl | apply EQ_refl | |].
      * eapply EQ_tran; [apply apply_set_extensional; [apply EQ_refl | exact Ea] | exact Eb].
      * exact (graph_beta A (fun x => apply_set g (apply_set f x)) a
          (composite_extensional f g) Ha).
Qed.
Theorem equinumerous_refl A : equinumerous A A.
Proof.
  exists (graph A (fun x => x)). split.
  - apply dependent_product_introduction; [intros x y E; exact E | auto].
  - split.
    + intros x x' y H H'.
      destruct (graph_value A (fun x => x) x y (fun _ _ E => E) H) as [_ E].
      destruct (graph_value A (fun x => x) x' y (fun _ _ E => E) H') as [_ E'].
      eapply EQ_tran; [apply EQ_sym; exact E | exact E'].
    + intros y Hy. exists y. apply graph_beta; [intros x x' E; exact E | exact Hy].
Qed.
Theorem equinumerous_sym A B : equinumerous A B -> equinumerous B A.
Proof. intros [f Hf]. exists (inverse A B f); apply inverse_bijection; exact Hf. Qed.
Theorem equinumerous_trans A B C :
  equinumerous A B -> equinumerous B C -> equinumerous A C.
Proof.
  intros [f Hf] [g Hg]. exists (compose A f g).
  apply (compose_bijection A B C); assumption.
Qed.

Print Assumptions inverse_application.
Print Assumptions inverse_typed.
Print Assumptions inverse_bijection.
Print Assumptions inverse_left.
Print Assumptions inverse_right.
Print Assumptions equinumerous_refl.
Print Assumptions equinumerous_sym.
Print Assumptions compose_bijection.
Print Assumptions equinumerous_trans.
