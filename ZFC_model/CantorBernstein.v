(** Schroeder--Bernstein via a least closed subset of A. The region uses
    only the set bounds A, B and Power A; no sequence of iterates is collected.
    Classical logic is an explicit parameter for the final gluing argument. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections ProductEmbedding.

Section Construction.
Variables A B f g : Ens.
Hypothesis Hf : injection A B f.
Hypothesis Hg : injection B A g.

Definition cb_step x := apply_set g (apply_set f x).
Definition cb_base x := forall y, IN y B -> ~ application g y x.
Definition cb_closed X :=
  (forall x, IN x A -> cb_base x -> IN x X) /\
  (forall x, IN x A -> IN x X -> IN (cb_step x) X).
Definition cb_predicate x := forall X, IN X (Power A) -> cb_closed X -> IN x X.
Definition cb_region := Comp A cb_predicate.

Lemma cb_step_extensional x x' : EQ x x' -> EQ (cb_step x) (cb_step x').
Proof.
  intro E. apply apply_set_extensional; [apply EQ_refl |].
  apply apply_set_extensional; [apply EQ_refl | exact E].
Qed.
Lemma cb_step_typed x : IN x A -> IN (cb_step x) A.
Proof.
  intro Hx. apply (apply_set_typed B (fun _ => A)); [exact (proj1 Hg) |].
  apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) | exact Hx].
Qed.
Lemma cb_predicate_extensional x y : cb_predicate x -> EQ x y -> cb_predicate y.
Proof. intros H E X HX HC. exact (IN_sound_left x y X E (H X HX HC)). Qed.
Lemma cb_region_spec x : IN x cb_region <-> IN x A /\ cb_predicate x.
Proof.
  split.
  - intro H. split; [exact (Comp_INC _ _ _ H) |].
    exact (IN_Comp_P _ _ _ cb_predicate_extensional H).
  - intros [Hx Hp]. apply IN_P_Comp; [apply cb_predicate_extensional | exact Hx | exact Hp].
Qed.
Lemma cb_region_closed : cb_closed cb_region.
Proof.
  split.
  - intros x Hx Hb. apply cb_region_spec; split; [exact Hx |].
    intros X HX [HB _]. exact (HB x Hx Hb).
  - intros x Hx Hc. apply cb_region_spec in Hc as [_ HC].
    apply cb_region_spec; split; [apply cb_step_typed; exact Hx |].
    intros X HX Hclosed. exact (proj2 Hclosed x Hx (HC X HX Hclosed)).
Qed.
Lemma cb_region_least X : INC X A -> cb_closed X -> INC cb_region X.
Proof.
  intros HX HC x Hx. apply cb_region_spec in Hx as [_ Hp].
  apply Hp; [apply INC_IN_Power; exact HX | exact HC].
Qed.
Definition cb_successor_predicate z := cb_base z \/ exists x,
  IN x cb_region /\ EQ z (cb_step x).
Lemma cb_successor_extensional z z' : cb_successor_predicate z -> EQ z z' ->
  cb_successor_predicate z'.
Proof.
  intros [Hb | [x [Hx Ex]]] E.
  - left. intros y Hy Hgy. apply (Hb y Hy).
    eapply application_arguments; [apply EQ_refl | apply EQ_refl | apply EQ_sym; exact E | exact Hgy].
  - right; exists x; split; [exact Hx |]. exact (EQ_tran _ _ _ (EQ_sym _ _ E) Ex).
Qed.
Definition cb_successor := Comp A cb_successor_predicate.
Lemma cb_successor_spec z : IN z cb_successor <-> IN z A /\ cb_successor_predicate z.
Proof.
  split.
  - intro H; split; [exact (Comp_INC _ _ _ H) | exact (IN_Comp_P _ _ _ cb_successor_extensional H)].
  - intros [Hz Hp]. apply IN_P_Comp; [apply cb_successor_extensional | exact Hz | exact Hp].
Qed.
Lemma cb_successor_in_region : INC cb_successor cb_region.
Proof.
  intros z Hz. apply cb_successor_spec in Hz as [Hz [Hb | [x [Hx E]]]].
  - exact (proj1 cb_region_closed z Hz Hb).
  - apply (IN_sound_left (cb_step x) z _ (EQ_sym _ _ E)).
    apply (proj2 cb_region_closed); [exact (Comp_INC _ _ _ Hx) | exact Hx].
Qed.
Lemma cb_successor_closed : cb_closed cb_successor.
Proof.
  split.
  - intros z Hz Hb. apply cb_successor_spec; split; [exact Hz | left; exact Hb].
  - intros x Hx Hs. apply cb_successor_spec; split; [apply cb_step_typed; exact Hx |].
    right; exists x; split; [exact (cb_successor_in_region x Hs) | apply EQ_refl].
Qed.
Theorem cb_region_decomposition z : IN z cb_region ->
  cb_base z \/ exists x, IN x cb_region /\ EQ z (cb_step x).
Proof.
  intro Hz. pose proof (cb_region_least cb_successor (Comp_INC _ _) cb_successor_closed z Hz) as H.
  exact (proj2 (proj1 (cb_successor_spec z) H)).
Qed.
Definition cb_relation x y :=
  (IN x cb_region /\ application f x y) \/
  (~ IN x cb_region /\ application g y x).
Lemma cb_relation_extensional x x' y y' : EQ x x' -> EQ y y' ->
  cb_relation x y -> cb_relation x' y'.
Proof.
  intros Ex Ey [[HC Hxy] | [HC Hyx]].
  - left; split; [exact (IN_sound_left _ _ _ Ex HC) |].
    eapply application_arguments; [apply EQ_refl | exact Ex | exact Ey | exact Hxy].
  - right; split.
    + intro HC'; apply HC. exact (IN_sound_left _ _ _ (EQ_sym _ _ Ex) HC').
    + eapply application_arguments; [apply EQ_refl | exact Ey | exact Ex | exact Hyx].
Qed.
Definition cb_edge e := exists x, IN x A /\ exists y,
  IN y B /\ EQ e (Couple x y) /\ cb_relation x y.
Lemma cb_edge_extensional e e' : cb_edge e -> EQ e e' -> cb_edge e'.
Proof.
  intros [x [Hx [y [Hy [E HR]]]]] E'. exists x; split; [exact Hx |].
  exists y; split; [exact Hy |]. split; [| exact HR].
  exact (EQ_tran _ _ _ (EQ_sym _ _ E') E).
Qed.
Definition cb_graph := Comp (Prod A B) cb_edge.
Lemma cb_graph_application x y : application cb_graph x y <->
  IN x A /\ IN y B /\ cb_relation x y.
Proof.
  split.
  - intro H. destruct (Couple_Prod_IN _ _ _ _ (Comp_INC _ _ _ H)) as [Hx Hy].
    pose proof (IN_Comp_P _ _ _ cb_edge_extensional H) as HR.
    destruct HR as [x' [_ [y' [_ [E HR]]]]]. split; [exact Hx |]. split; [exact Hy |].
    eapply cb_relation_extensional; [apply EQ_sym; exact (Couple_inj_left _ _ _ _ E) |
      apply EQ_sym; exact (Couple_inj_right _ _ _ _ E) | exact HR].
  - intros [Hx [Hy HR]]. apply IN_P_Comp.
    + apply cb_edge_extensional.
    + apply Couple_IN_Prod; assumption.
    + exists x; split; [exact Hx |]. exists y; split; [exact Hy |].
      split; [apply EQ_refl | exact HR].
Qed.
Lemma cb_relation_functional x y z : cb_relation x y -> cb_relation x z -> EQ y z.
Proof.
  intros [[HC Hxy] | [HN Hyx]] [[HC' Hxz] | [HN' Hzx]]; try contradiction.
  - exact (proj2 (proj2 (dependent_product_elimination _ _ _ (proj1 Hf))) x y z Hxy Hxz).
  - exact (proj2 Hg y z x Hyx Hzx).
Qed.
Lemma cb_cross_region x y z : IN x A -> IN x cb_region ->
  application f x y -> application g y z -> IN z cb_region.
Proof.
  intros Hx HC Hxy Hyz.
  assert (E : EQ (cb_step x) z).
  { eapply EQ_tran; [apply apply_set_extensional; [apply EQ_refl |] |].
    - exact (function_value A B f x y (proj1 Hf) Hxy).
    - exact (function_value B A g y z (proj1 Hg) Hyz). }
  apply (IN_sound_left (cb_step x) z _ E).
  exact (proj2 cb_region_closed x Hx HC).
Qed.
Lemma cb_relation_injective x x' y : IN x A -> IN x' A ->
  cb_relation x y -> cb_relation x' y -> EQ x x'.
Proof.
  intros Hx Hx' [[HC Hxy] | [HN Hyx]] [[HC' Hx'y] | [HN' Hyx']].
  - exact (proj2 Hf x x' y Hxy Hx'y).
  - exfalso; apply HN'. exact (cb_cross_region x y x' Hx HC Hxy Hyx').
  - exfalso; apply HN. exact (cb_cross_region x' y x Hx' HC' Hx'y Hyx).
  - exact (proj2 (proj2 (dependent_product_elimination _ _ _ (proj1 Hg))) y x x' Hyx Hyx').
Qed.

Variable classical_logic : forall P : Prop, P \/ ~ P.
Lemma cb_relation_total x : IN x A -> exists y, IN y B /\ cb_relation x y.
Proof.
  intro Hx. destruct (classical_logic (IN x cb_region)) as [HC | HN].
  - exists (apply_set f x); split.
    + exact (apply_set_typed A (fun _ => B) f x (proj1 Hf) Hx).
    + left; split; [exact HC | exact (apply_set_spec A (fun _ => B) f x (proj1 Hf) Hx)].
  - destruct (classical_logic (exists y, IN y B /\ application g y x)) as [Hy | Hnone].
    + destruct Hy as [y [Hy Hyx]]. exists y; split; [exact Hy | right; auto].
    + exfalso; apply HN. apply (proj1 cb_region_closed x Hx).
      intros y Hy Hyx; apply Hnone; exists y; auto.
Qed.
Lemma cb_relation_surjective y : IN y B -> exists x, IN x A /\ cb_relation x y.
Proof.
  intro Hy. pose proof (apply_set_typed B (fun _ => A) g y (proj1 Hg) Hy) as Hx.
  pose proof (apply_set_spec B (fun _ => A) g y (proj1 Hg) Hy) as Hyx.
  destruct (classical_logic (IN (apply_set g y) cb_region)) as [HC | HN].
  - destruct (cb_region_decomposition _ HC) as [HB | [c [Hc E]]].
    + exfalso; exact (HB y Hy Hyx).
    + assert (HcA : IN c A) by exact (Comp_INC _ _ _ Hc).
      assert (Hfc : IN (apply_set f c) B).
      { exact (apply_set_typed A (fun _ => B) f c (proj1 Hf) HcA). }
      assert (Ey : EQ y (apply_set f c)).
      { exact (injection_values B A g y (apply_set f c) Hg Hy Hfc E). }
      exists c; split; [exact HcA |]. left; split; [exact Hc |].
      eapply application_arguments; [apply EQ_refl | apply EQ_refl | apply EQ_sym; exact Ey |].
      exact (apply_set_spec A (fun _ => B) f c (proj1 Hf) HcA).
  - exists (apply_set g y); split; [exact Hx | right; auto].
Qed.
Theorem cb_graph_bijection : bijection A B cb_graph.
Proof.
  split.
  - apply bounded_function_member; [apply Comp_INC |]. split.
    + intros x Hx. destruct (cb_relation_total x Hx) as [y [Hy HR]].
      exists y; apply cb_graph_application; auto.
    + split.
      * intros x y H. apply cb_graph_application in H; tauto.
      * intros x y z H H'. apply cb_graph_application in H as [_ [_ H]].
        apply cb_graph_application in H' as [_ [_ H']]. eapply cb_relation_functional; eassumption.
  - split.
    + intros x x' y H H'. apply cb_graph_application in H as [Hx [_ H]].
      apply cb_graph_application in H' as [Hx' [_ H']]. eapply cb_relation_injective; eassumption.
    + intros y Hy. destruct (cb_relation_surjective y Hy) as [x [Hx HR]].
      exists x; apply cb_graph_application; auto.
Qed.
End Construction.

Theorem cantor_bernstein (classical_logic : forall P : Prop, P \/ ~ P) A B :
  embeds A B -> embeds B A -> equinumerous A B.
Proof.
  intros [f Hf] [g Hg]. exists (cb_graph A B f g).
  apply cb_graph_bijection; assumption.
Qed.

Print Assumptions cb_region_closed.
Print Assumptions cb_region_decomposition.
Print Assumptions cb_graph_bijection.
Print Assumptions cantor_bernstein.
Check cantor_bernstein.
