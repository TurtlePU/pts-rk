(** One choice operation over a supplied hierarchy, independent of typing
    ranks. Existence/identification of the hierarchy is not assumed silently. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  ProductEmbedding CodeUniverses CountableCodes CardinalGrowth CardinalHierarchy
  HierarchyBounds CodeHierarchyBounds SuppliedHierarchy CartesianMaps
  CardinalClassification CountableDichotomy ProductWitnesses CodeWitnesses
  SelectedCodes PowersetSquares.
Import CodeUniverses.CodeUniverses.

Definition all_codes := sup Code repr.
Lemma all_codes_member c : IN c all_codes <-> exists d, EQ c (repr d).
Proof. split; intros [d E]; exists d; exact E. Qed.
Lemma universe_in_all_codes i : INC (U i) all_codes.
Proof. intros c Hc; apply universe_membership in Hc as [d [_ E]]; exists d; exact E. Qed.
Lemma all_codes_in_some_universe c : IN c all_codes -> exists i, IN c (U i).
Proof.
  intros [d E]. destruct d as [n|j|j].
  - exists 0; apply universe_membership; exists (finite n); split; [exact I | exact E].
  - exists j; apply universe_membership; exists (infinite j); split; [apply Nat.le_refl | exact E].
  - exists 0; apply universe_membership; exists (sort j); split; [exact I | exact E].
Qed.
Definition all_decoding_graph := graph all_codes decode.
Definition global_graph_bound H := Power (Prod H H).
Definition global_code_witnesses H A := code_witnesses A all_codes all_decoding_graph H (global_graph_bound H).

Theorem bounded_code_admissible k A c : IN c all_codes -> embeds A (carrier k) ->
  equinumerous A (decode c) -> IN c (U k).
Proof.
  intros [d E] HA HE. apply universe_membership. exists d; split; [| exact E].
  destruct d as [n|j|j]; cbn [Allowed]; [exact I | | exact I].
  destruct (Nat.le_gt_cases j k) as [Hle | Hgt]; [exact Hle |].
  exfalso; apply (carrier_strict k j Hgt).
  assert (Ev : EQ (decode c) (carrier j)).
  { eapply EQ_tran; [apply decoding_extensional; exact E | apply decode_infinite]. }
  eapply embeds_equal_domain; [exact Ev |].
  eapply embeds_transitive; [apply equinumerous_embeds, equinumerous_sym; exact HE | exact HA].
Qed.

Section Hierarchy.
Variables W H : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Lemma all_decoding_typed : IN all_decoding_graph (dependent_product all_codes (fun _ => H)).
Proof.
  apply dependent_product_introduction; [intros x y E; apply decoding_extensional; exact E |].
  intros c Hc. destruct (all_codes_in_some_universe c Hc) as [i Hi].
  exact (envelope_decode W H i c HO HH Hi).
Qed.
Lemma global_product_bound m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  INC (dependent_product (decode a) (fun x => decode (b x))) H.
Proof.
  intros Ha Hb x Hx. apply (envelope_transitive W H HW HH (witness_ambient m n)).
  - apply (envelope_carrier W H); assumption.
  - exact (product_subset_ambient m n a b Ha Hb x Hx).
Qed.
Theorem global_code_witnesses_nonempty
  (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  exists e, IN e (global_code_witnesses H (dependent_product (decode a) (fun x => decode (b x)))).
Proof.
  intros Ha Hb. destruct (decoded_product_code classical_logic comparison gap choice m n a b Ha Hb)
    as [c [Hc [f Hf]]]. exists (Couple c f). apply code_witnesses_spec.
  exists c; split; [apply (universe_in_all_codes (product_code_rank m n)); exact Hc |].
  exists f; split.
  - apply INC_IN_Power. intros e He.
    apply (cartesian_monotone (dependent_product (decode a) (fun x => decode (b x))) H (decode c) H);
      [exact (global_product_bound m n a b Ha Hb) | |].
    + apply (envelope_transitive W H HW HH (decode c)).
      exact (envelope_decode W H _ c HO HH Hc).
    + exact (typed_graph_cartesian_bound _ _ f (proj1 Hf) e He).
  - split; [apply EQ_refl |]. exists (decode c); split.
    + exact (envelope_decode W H _ c HO HH Hc).
    + split; [| exact Hf]. apply graph_beta; [intros x y E; apply decoding_extensional; exact E |].
      apply (universe_in_all_codes (product_code_rank m n)); exact Hc.
Qed.
Lemma global_witness_extract A e : IN e (global_code_witnesses H A) ->
  exists c f, IN c all_codes /\ EQ e (Couple c f) /\ bijection A (decode c) f.
Proof.
  intro HE. apply code_witnesses_spec in HE as [c [Hc [f [Hf [E HR]]]]].
  destruct HR as [K [HK [HD HB]]]. exists c, f; split; [exact Hc |]. split; [exact E |].
  apply (bijection_codomain_equal A K _ f); [| exact HB].
  eapply EQ_tran; [apply EQ_sym; exact (function_value _ _ _ c K all_decoding_typed HD) |].
  apply apply_set_beta; [intros x y Exy; apply decoding_extensional; exact Exy | exact Hc].
Qed.
Theorem rank_independent_code_choice
  (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) : exists s, forall m n a b,
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  exists c f, IN c (U (product_code_rank m n)) /\
    EQ (apply_set s (global_code_witnesses H (dependent_product (decode a) (fun x => decode (b x)))))
       (Couple c f) /\
    bijection (dependent_product (decode a) (fun x => decode (b x))) (decode c) f.
Proof.
  destruct (subset_choice_from_family_choice choice (Prod all_codes (global_graph_bound H))) as [s Hs].
  exists s; intros m n a b Ha Hb.
  assert (HE : IN (apply_set s (global_code_witnesses H (dependent_product (decode a) (fun x => decode (b x)))))
      (global_code_witnesses H (dependent_product (decode a) (fun x => decode (b x))))).
  { apply Hs; [apply INC_IN_Power, Comp_INC |].
    apply (global_code_witnesses_nonempty classical_logic comparison gap choice m n a b); assumption. }
  destruct (global_witness_extract _ _ HE) as [c [f [Hc [E HB]]]].
  exists c, f; split; [| split; [exact E | exact HB]].
  apply (bounded_code_admissible _ (dependent_product (decode a) (fun x => decode (b x))));
    [exact Hc | apply decoded_dependent_product_bound; assumption | exists f; exact HB].
Qed.
End Hierarchy.
Theorem global_choice_congruence H s A A' : EQ A A' ->
  EQ (apply_set s (global_code_witnesses H A)) (apply_set s (global_code_witnesses H A')).
Proof.
  intro E. apply apply_set_extensional; [apply EQ_refl |].
  apply code_witnesses_source_congruence; exact E.
Qed.
Print Assumptions bounded_code_admissible.
Print Assumptions rank_independent_code_choice.
Print Assumptions global_choice_congruence.
Check rank_independent_code_choice.

Definition global_selected_code H s A := pair_first all_codes (global_graph_bound H)
  (apply_set s (global_code_witnesses H A)).
Definition global_selected_bijection H s A := pair_second all_codes (global_graph_bound H)
  (apply_set s (global_code_witnesses H A)).
Theorem global_selector_exists (choice : family_choice) H : exists s, forall A,
  (exists e, IN e (global_code_witnesses H A)) ->
  IN (apply_set s (global_code_witnesses H A)) (global_code_witnesses H A).
Proof.
  destruct (subset_choice_from_family_choice choice (Prod all_codes (global_graph_bound H))) as [s Hs].
  exists s; intros A Hne. apply Hs; [apply INC_IN_Power, Comp_INC | exact Hne].
Qed.
Theorem global_selected_typed W H s A k :
  transitive_set W -> INC omega_codes W -> tower_envelope W H ->
  embeds A (carrier k) ->
  IN (apply_set s (global_code_witnesses H A)) (global_code_witnesses H A) ->
  IN (global_selected_code H s A) (U k) /\
  bijection A (decode (global_selected_code H s A)) (global_selected_bijection H s A).
Proof.
  intros HW HO HH HA HE.
  destruct (global_witness_extract W H HO HH A _ HE) as [c [f [Hc [E HB]]]].
  assert (Hf : IN f (global_graph_bound H)).
  { exact (proj2 (Couple_Prod_IN _ _ c f (IN_sound_left _ _ _ E (Comp_INC _ _ _ HE)))). }
  pose proof (pair_first_beta _ _ _ c f Hc Hf E) as Ec.
  pose proof (pair_second_beta _ _ _ c f Hc Hf E) as Ef.
  split.
  - apply (IN_sound_left c _ _ (EQ_sym _ _ Ec)).
    apply (bounded_code_admissible k A c Hc HA); exists f; exact HB.
  - apply (bijection_graph_equal _ _ f); [apply EQ_sym; exact Ef |].
    apply (bijection_codomain_equal _ (decode c)); [apply decoding_extensional, EQ_sym; exact Ec | exact HB].
Qed.
Theorem global_selected_congruence H s A A' : EQ A A' ->
  EQ (global_selected_code H s A) (global_selected_code H s A') /\
  EQ (global_selected_bijection H s A) (global_selected_bijection H s A').
Proof.
  intro E. split; apply apply_set_extensional; [apply EQ_refl | | apply EQ_refl |];
    apply global_choice_congruence; exact E.
Qed.
Print Assumptions global_selector_exists.
Print Assumptions global_selected_typed.
Print Assumptions global_selected_congruence.
