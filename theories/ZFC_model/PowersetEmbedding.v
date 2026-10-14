(** Direct-image embeddings of powersets and graph bounds. All maps are
    constructed as sets; no cardinal comparison or choice is assumed. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections ProductEmbedding.

Definition direct_image f X := sup (pi1 X) (fun i => apply_set f (pi2 X i)).
Lemma direct_image_membership f X y :
  IN y (direct_image f X) <-> exists x, IN x X /\ EQ y (apply_set f x).
Proof.
  split.
  - intros [i E]. exists (pi2 X i); split; [apply index_member | exact E].
  - intros [x [Hx E]]. destruct (IN_EXType X x Hx) as [i Ex]. exists i.
    eapply EQ_tran; [exact E |]. apply apply_set_extensional; [apply EQ_refl | exact Ex].
Qed.
Lemma direct_image_extensional f X Y : EQ X Y -> EQ (direct_image f X) (direct_image f Y).
Proof.
  intro E. apply INC_EQ; intros y Hy; apply direct_image_membership in Hy as [x [Hx Ex]];
    apply direct_image_membership; exists x; split; [| exact Ex | | exact Ex].
  - exact (IN_sound_right x X Y E Hx).
  - exact (IN_sound_right x Y X (EQ_sym _ _ E) Hx).
Qed.
Lemma direct_image_bound A B f X :
  injection A B f -> INC X A -> INC (direct_image f X) B.
Proof.
  intros Hf HX y Hy. apply direct_image_membership in Hy as [x [Hx E]].
  apply (IN_sound_left (apply_set f x) y B (EQ_sym _ _ E)).
  apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) | apply HX; exact Hx].
Qed.
Lemma direct_image_reflects A B f X Y :
  injection A B f -> INC X A -> INC Y A ->
  EQ (direct_image f X) (direct_image f Y) -> EQ X Y.
Proof.
  intros Hf HX HY E. apply INC_EQ.
  - intros x Hx.
    assert (Him : IN (apply_set f x) (direct_image f X)).
    { apply direct_image_membership; exists x; split; [exact Hx | apply EQ_refl]. }
    pose proof (IN_sound_right _ _ _ E Him) as Hother.
    apply direct_image_membership in Hother as [y [Hy Exy]].
    assert (Ex : EQ x y).
    { apply (injection_values A B f x y Hf); [apply HX; exact Hx | apply HY; exact Hy | exact Exy]. }
    exact (IN_sound_left y x Y (EQ_sym _ _ Ex) Hy).
  - intros y Hy.
    assert (Him : IN (apply_set f y) (direct_image f Y)).
    { apply direct_image_membership; exists y; split; [exact Hy | apply EQ_refl]. }
    pose proof (IN_sound_right _ _ _ (EQ_sym _ _ E) Him) as Hother.
    apply direct_image_membership in Hother as [x [Hx Eyx]].
    assert (Ey : EQ y x).
    { apply (injection_values A B f y x Hf); [apply HY; exact Hy | apply HX; exact Hx | exact Eyx]. }
    exact (IN_sound_left x y X (EQ_sym _ _ Ey) Hx).
Qed.
Definition powerset_map A f := graph (Power A) (direct_image f).
Theorem powerset_injection A B f : injection A B f ->
  injection (Power A) (Power B) (powerset_map A f).
Proof.
  intro Hf. apply graph_injection.
  - intros X Y E; apply direct_image_extensional; exact E.
  - intros X HX. apply INC_IN_Power. apply (direct_image_bound A B f); [exact Hf |].
    apply IN_Power_INC; exact HX.
  - intros X Y HX HY E. apply (direct_image_reflects A B f); [exact Hf | | | exact E];
      apply IN_Power_INC; assumption.
Qed.
Theorem powerset_embeds A B : embeds A B -> embeds (Power A) (Power B).
Proof. intros [f Hf]. exists (powerset_map A f); apply powerset_injection; exact Hf. Qed.
Theorem inclusion_embeds A B : INC A B -> embeds A B.
Proof.
  intro H. exists (graph A (fun x => x)). apply graph_injection;
    [intros x y E; exact E | exact H | intros x y Hx Hy E; exact E].
Qed.
Theorem dependent_graph_bound A B :
  embeds (dependent_product A B) (Power (Prod A (Union (family_range A B)))).
Proof. apply inclusion_embeds, Comp_INC. Qed.

Print Assumptions direct_image_extensional.
Print Assumptions direct_image_reflects.
Print Assumptions powerset_injection.
Print Assumptions powerset_embeds.
Print Assumptions inclusion_embeds.
Print Assumptions dependent_graph_bound.
Check powerset_injection.
