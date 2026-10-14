(** Finite enumeration constructs actual set-graph bijections. *)
From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections ProductEmbedding CodeUniverses.
Import CodeUniverses.CodeUniverses.

Definition finite_enumeration_graph n (e : nat -> Ens) :=
  sup {i : nat | i < n} (fun i => Couple (numeral (proj1_sig i)) (e (proj1_sig i))).
Lemma finite_enumeration_application n e x y :
  application (finite_enumeration_graph n e) x y <->
  exists i, i < n /\ EQ x (numeral i) /\ EQ y (e i).
Proof.
  split.
  - intros [[i Hi] E]. exists i; split; [exact Hi |].
    split; [exact (Couple_inj_left _ _ _ _ E) | exact (Couple_inj_right _ _ _ _ E)].
  - intros [i [Hi [Ex Ey]]]. exists (Specif.exist _ i Hi).
    eapply EQ_tran; [apply Couple_sound_left; exact Ex | apply Couple_sound_right; exact Ey].
Qed.
Theorem finite_enumeration_bijection n e X :
  (forall i, i < n -> IN (e i) X) ->
  (forall i j, i < n -> j < n -> EQ (e i) (e j) -> i = j) ->
  (forall x, IN x X -> exists i, i < n /\ EQ x (e i)) ->
  bijection (finite_carrier n) X (finite_enumeration_graph n e).
Proof.
  intros HT HI HS. split.
  - apply bounded_function_member.
    + intros p [[i Hi] E]. apply (IN_sound_left _ p _ (EQ_sym _ _ E)).
      apply Couple_IN_Prod; [apply finite_carrier_membership; exists i; split; [exact Hi | apply EQ_refl] | apply HT; exact Hi].
    + split.
      * intros x Hx. apply finite_carrier_membership in Hx as [i [Hi E]].
        exists (e i); apply finite_enumeration_application. exists i; repeat split; auto; apply EQ_refl.
      * split.
        -- intros x y H. apply finite_enumeration_application in H as [i [Hi [Ex Ey]]]. split.
           ++ apply finite_carrier_membership; exists i; auto.
           ++ exact (IN_sound_left _ y X (EQ_sym _ _ Ey) (HT i Hi)).
        -- intros x y z H H'. apply finite_enumeration_application in H as [i [Hi [Ex Ey]]].
           apply finite_enumeration_application in H' as [j [Hj [Ex' Ez]]].
           assert (Eij : i = j) by (apply numeral_injective; eapply EQ_tran; [apply EQ_sym; exact Ex | exact Ex']).
           subst j. eapply EQ_tran; [exact Ey | apply EQ_sym; exact Ez].
  - split.
    + intros x x' y H H'. apply finite_enumeration_application in H as [i [Hi [Ex Ey]]].
      apply finite_enumeration_application in H' as [j [Hj [Ex' Ey']]].
      assert (Eij : i = j).
      { apply HI; [exact Hi | exact Hj |]. eapply EQ_tran; [apply EQ_sym; exact Ey | exact Ey']. }
      subst j. eapply EQ_tran; [exact Ex | apply EQ_sym; exact Ex'].
    + intros y Hy. destruct (HS y Hy) as [i [Hi Ei]]. exists (numeral i).
      apply finite_enumeration_application; exists i; split; [exact Hi |]. split; [apply EQ_refl | exact Ei].
Qed.

Lemma finite_selection (P : nat -> Prop) (dec : forall i, P i \/ ~ P i) n :
  exists m (e : nat -> nat), m <= n /\
    (forall i, i < m -> e i < n /\ P (e i)) /\
    (forall i j, i < m -> j < m -> e i = e j -> i = j) /\
    (forall k, k < n -> P k -> exists i, i < m /\ e i = k).
Proof.
  induction n as [|n [m [e [Hm [HT [HI HS]]]]]].
  - exists 0, (fun i => i). repeat split; intros; lia.
  - destruct (dec n) as [HP | HN].
    + exists (S m), (fun i => if lt_dec i m then e i else n).
      split; [lia |]. split.
      * intros i Hi. destruct (lt_dec i m) as [Him | Him].
        -- destruct (HT i Him); split; [lia | assumption].
        -- split; [lia | exact HP].
      * split.
        -- intros i j Hi Hj E. destruct (lt_dec i m), (lt_dec j m).
           ++ apply HI; assumption.
           ++ destruct (HT i l); lia.
           ++ destruct (HT j l); lia.
           ++ lia.
        -- intros k Hk Hpk. destruct (Nat.eq_dec k n) as [E | E].
           ++ subst k. exists m; split; [lia |]. destruct (lt_dec m m); [lia | reflexivity].
           ++ destruct (HS k ltac:(lia) Hpk) as [i [Hi Ei]]. exists i; split; [lia |].
              destruct (lt_dec i m); [exact Ei | lia].
    + exists m, e. split; [lia |]. split.
      * intros i Hi; destruct (HT i Hi); split; [lia | assumption].
      * split; [exact HI |]. intros k Hk HP. apply HS; [| exact HP].
        assert (k <> n) by (intro E; subst k; contradiction). lia.
Qed.

Print Assumptions finite_enumeration_bijection.
Print Assumptions finite_selection.

Theorem finite_subset_classification (classical_logic : forall P : Prop, P \/ ~ P) n X :
  INC X (finite_carrier n) -> exists m, m <= n /\ equinumerous X (finite_carrier m).
Proof.
  intro HX. destruct (finite_selection (fun k => IN (numeral k) X)
    (fun k => classical_logic _) n) as [m [e [Hm [HT [HI HS]]]]].
  exists m; split; [exact Hm |]. apply equinumerous_sym.
  exists (finite_enumeration_graph m (fun i => numeral (e i))).
  apply finite_enumeration_bijection.
  - intros i Hi; exact (proj2 (HT i Hi)).
  - intros i j Hi Hj E. apply HI; [exact Hi | exact Hj | apply numeral_injective; exact E].
  - intros x Hx. destruct (proj1 (finite_carrier_membership n x) (HX x Hx)) as [k [Hk Ek]].
    assert (HP : IN (numeral k) X) by exact (IN_sound_left x _ X Ek Hx).
    destruct (HS k Hk HP) as [i [Hi Ei]]. exists i; split; [exact Hi |]. rewrite Ei; exact Ek.
Qed.

Definition injection_range A B f := Comp B (fun y => exists x, IN x A /\ application f x y).
Lemma injection_range_predicate A f y y' :
  (exists x, IN x A /\ application f x y) -> EQ y y' ->
  exists x, IN x A /\ application f x y'.
Proof.
  intros [x [Hx Hxy]] E. exists x; split; [exact Hx |].
  eapply application_arguments; [apply EQ_refl | apply EQ_refl | exact E | exact Hxy].
Qed.
Lemma injection_range_spec A B f y :
  IN y (injection_range A B f) <-> IN y B /\ exists x, IN x A /\ application f x y.
Proof.
  split.
  - intro H; split; [exact (Comp_INC _ _ _ H) |].
    exact (IN_Comp_P _ _ _ (injection_range_predicate A f) H).
  - intros [Hy HP]. apply IN_P_Comp; [apply injection_range_predicate | exact Hy | exact HP].
Qed.
Theorem injection_onto_range A B f : injection A B f -> bijection A (injection_range A B f) f.
Proof.
  intros [HT HI]. pose proof (dependent_product_elimination _ _ _ HT) as [Htot [Hty Hu]].
  assert (HR : forall x y, application f x y -> IN y (injection_range A B f)).
  { intros x y H. destruct (Hty x y H) as [Hx Hy]. apply injection_range_spec.
    split; [exact Hy | exists x; auto]. }
  split.
  - apply bounded_function_member.
    + intros e He. destruct (dependent_product_pair A (fun _ => B) f e HT He)
        as [x [y [E [Hx Hxy]]]].
      apply (IN_sound_left _ e _ E). apply Couple_IN_Prod; [exact Hx | exact (HR x y Hxy)].
    + split; [exact Htot |]. split; [| exact Hu].
      intros x y H; split; [exact (proj1 (Hty x y H)) | exact (HR x y H)].
  - split; [exact HI |]. intros y Hy. apply injection_range_spec in Hy as [_ [x [Hx Hxy]]].
    exists x; exact Hxy.
Qed.
Theorem finite_embedding_classification (classical_logic : forall P : Prop, P \/ ~ P) n X :
  embeds X (finite_carrier n) -> exists m, m <= n /\ equinumerous X (finite_carrier m).
Proof.
  intros [f Hf]. destruct (finite_subset_classification classical_logic n
    (injection_range X (finite_carrier n) f) (Comp_INC _ _)) as [m [Hm HE]].
  exists m; split; [exact Hm |]. eapply equinumerous_trans; [| exact HE].
  exists f; apply injection_onto_range; exact Hf.
Qed.
Print Assumptions finite_subset_classification.
Print Assumptions injection_onto_range.
Print Assumptions finite_embedding_classification.
Check finite_embedding_classification.
