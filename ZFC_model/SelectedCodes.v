(** Use selected code/bijection pairs without choice of representatives. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  CartesianMaps CodeUniverses CardinalGrowth CardinalHierarchy HierarchyBounds
  CodeHierarchyBounds CountableDichotomy CardinalClassification ProductWitnesses
  CodeWitnesses CodedFunctions ProductExtensionality.
Import CodeUniverses.CodeUniverses.

Lemma cartesian_graph_beta A B f x y : binary_extensional f -> IN x A -> IN y B ->
  EQ (apply_set (cartesian_graph A B f) (Couple x y)) (f x y).
Proof.
  intros HF Hx Hy. apply apply_set_value.
  - apply (cartesian_application A B f HF). exists x; split; [exact Hx |].
    exists y; split; [exact Hy |]. split; apply EQ_refl.
  - intros z H. apply (cartesian_application A B f HF) in H as [x' [_ [y' [_ [E Ez]]]]].
    eapply EQ_tran; [exact Ez |]. apply HF.
    + apply EQ_sym; exact (Couple_inj_left _ _ _ _ E).
    + apply EQ_sym; exact (Couple_inj_right _ _ _ _ E).
Qed.
Definition pair_first A B e := apply_set (cartesian_graph A B (fun x _ => x)) e.
Definition pair_second A B e := apply_set (cartesian_graph A B (fun _ y => y)) e.
Lemma pair_first_beta A B e x y : IN x A -> IN y B -> EQ e (Couple x y) -> EQ (pair_first A B e) x.
Proof.
  intros Hx Hy E. eapply EQ_tran.
  - apply apply_set_extensional; [apply EQ_refl | exact E].
  - apply cartesian_graph_beta; [intros u u' v v' Eu Ev; exact Eu | exact Hx | exact Hy].
Qed.
Lemma pair_second_beta A B e x y : IN x A -> IN y B -> EQ e (Couple x y) -> EQ (pair_second A B e) y.
Proof.
  intros Hx Hy E. eapply EQ_tran.
  - apply apply_set_extensional; [apply EQ_refl | exact E].
  - apply cartesian_graph_beta; [intros u u' v v' Eu Ev; exact Ev | exact Hx | exact Hy].
Qed.
Lemma bijection_graph_equal A B f g : EQ f g -> bijection A B f -> bijection A B g.
Proof.
  intros E [HT [HI HS]]. split; [exact (IN_sound_left f g _ E HT) |]. split.
  - intros x x' y H H'. apply (HI x x' y).
    + exact (IN_sound_right _ g f (EQ_sym _ _ E) H).
    + exact (IN_sound_right _ g f (EQ_sym _ _ E) H').
  - intros y Hy. destruct (HS y Hy) as [x Hx]. exists x; exact (IN_sound_right _ f g E Hx).
Qed.
Definition witness_code m n e := pair_first (U (product_code_rank m n))
  (iterated_power (witness_ambient m n) 4) e.
Definition witness_bijection m n e := pair_second (U (product_code_rank m n))
  (iterated_power (witness_ambient m n) 4) e.
Theorem witness_components_typed m n a b e : IN e (product_code_witnesses m n a b) ->
  IN (witness_code m n e) (U (product_code_rank m n)) /\
  bijection (dependent_product (decode a) (fun x => decode (b x)))
    (decode (witness_code m n e)) (witness_bijection m n e).
Proof.
  intro H. destruct (product_code_witnesses_extract m n a b e H) as [c [f [Hc [E HB]]]].
  assert (Hf : IN f (iterated_power (witness_ambient m n) 4)).
  { pose proof (Comp_INC _ _ _ H) as Hp.
    pose proof (IN_sound_left _ _ _ E Hp) as Hpair.
    exact (proj2 (Couple_Prod_IN _ _ c f Hpair)). }
  pose proof (pair_first_beta _ _ e c f Hc Hf E) as Ec.
  pose proof (pair_second_beta _ _ e c f Hc Hf E) as Ef.
  split.
  - exact (IN_sound_left c _ _ (EQ_sym _ _ Ec) Hc).
  - apply (bijection_graph_equal _ _ f); [apply EQ_sym; exact Ef |].
    apply (bijection_codomain_equal _ (decode c)); [| exact HB].
    apply decoding_extensional, EQ_sym; exact Ec.
Qed.
Theorem witness_components_extensional m n e e' : EQ e e' ->
  EQ (witness_code m n e) (witness_code m n e') /\
  EQ (witness_bijection m n e) (witness_bijection m n e').
Proof. intro E; split; apply apply_set_extensional; [apply EQ_refl | exact E | apply EQ_refl | exact E]. Qed.

Definition selected_witness s m n a b := apply_set s (product_code_witnesses m n a b).
Definition selected_code s m n a b := witness_code m n (selected_witness s m n a b).
Definition selected_bijection s m n a b := witness_bijection m n (selected_witness s m n a b).
Theorem uniform_selected_codes
  (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) m n : exists s, forall a b,
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  IN (selected_code s m n a b) (U (product_code_rank m n)) /\
  bijection (dependent_product (decode a) (fun x => decode (b x)))
    (decode (selected_code s m n a b)) (selected_bijection s m n a b).
Proof.
  destruct (subset_choice_from_family_choice choice (carrier (13 + product_code_rank m n))) as [s Hs].
  exists s; intros a b Ha Hb. apply witness_components_typed, Hs.
  - apply INC_IN_Power. apply (iterated_power_transitive _ _ omega_codes_transitive).
    apply product_code_witnesses_rank_bound.
  - apply (product_code_witnesses_nonempty classical_logic comparison gap choice); assumption.
Qed.
Theorem selected_beta s m n a b body x :
  IN (selected_witness s m n a b) (product_code_witnesses m n a b) ->
  family_extensional body ->
  (forall y, IN y (decode a) -> IN (body y) (decode (b y))) -> IN x (decode a) ->
  EQ (coded_application (decode a) (fun y => decode (b y))
      (decode (selected_code s m n a b)) (selected_bijection s m n a b)
      (encode_function (selected_bijection s m n a b) (decode a) body) x) (body x).
Proof.
  intros HW HF HT Hx. apply coded_beta; [| exact HF | exact HT | exact Hx].
  exact (proj2 (witness_components_typed m n a b _ HW)).
Qed.
Print Assumptions witness_components_typed.
Print Assumptions witness_components_extensional.
Print Assumptions uniform_selected_codes.
Print Assumptions selected_beta.
Check uniform_selected_codes.

Lemma code_witnesses_source_congruence A A' U D T F : EQ A A' ->
  EQ (code_witnesses A U D T F) (code_witnesses A' U D T F).
Proof.
  intro EA. apply INC_EQ; intros e H; apply code_witnesses_spec in H
    as [c [Hc [f [Hf [E Hrest]]]]]; apply code_witnesses_spec;
    exists c; split; [exact Hc | | exact Hc |]; exists f; split; [exact Hf | | exact Hf |];
    split; [exact E | | exact E |]; destruct Hrest as [K [HK [HD HB]]];
    exists K; split; [exact HK | | exact HK |]; split; [exact HD | | exact HD |].
  - apply (bijection_domain_equal A A' K f EA); exact HB.
  - apply (bijection_domain_equal A' A K f (EQ_sym _ _ EA)); exact HB.
Qed.
Theorem selected_codes_congruence s m n a a' b b' :
  EQ (decode a) (decode a') ->
  family_extensional (fun x => decode (b x)) ->
  family_extensional (fun x => decode (b' x)) ->
  (forall x, IN x (decode a) -> EQ (decode (b x)) (decode (b' x))) ->
  EQ (selected_code s m n a b) (selected_code s m n a' b') /\
  EQ (selected_bijection s m n a b) (selected_bijection s m n a' b').
Proof.
  intros EA HB HB' HP. apply witness_components_extensional.
  apply apply_set_extensional; [apply EQ_refl |].
  apply code_witnesses_source_congruence, dependent_product_congruence; assumption.
Qed.
Print Assumptions selected_codes_congruence.
