(** Nonempty, rank-bounded sets of coding witnesses. The cardinal principles
    remain explicit; this is not yet the complete PTS interpretation. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  CodeUniverses CountableCodes CardinalGrowth CardinalHierarchy HierarchyBounds
  CodeHierarchyBounds BoundedBijections BoundedFamilies CardinalClassification CountableDichotomy.
Import CodeUniverses.CodeUniverses.

Definition coding_targets i := family_range (U i) decode.
Theorem coding_targets_bounded i :
  EQ (coding_targets i) (bounded_family_range (carrier i) (U i) (decoding_graph i)).
Proof.
  apply EQ_sym. eapply EQ_tran; [apply decoding_bounded_range |].
  apply INC_EQ; intros K [j E]; exists j; eapply EQ_tran; [exact E | | exact E |].
  - apply decoding_graph_beta, index_member.
  - apply EQ_sym, decoding_graph_beta, index_member.
Qed.
Lemma coding_target_member i c : IN c (U i) -> IN (decode c) (coding_targets i).
Proof.
  intro Hc. destruct (IN_EXType _ _ Hc) as [j Ej]. exists j.
  apply decoding_extensional; exact Ej.
Qed.
Lemma coding_target_bound i K : IN K (coding_targets i) -> INC K (carrier i).
Proof.
  intros [j Ej] x Hx. apply (decoding_subset_bound i (pi2 (U i) j) (index_member _ j)).
  exact (IN_sound_right x _ _ Ej Hx).
Qed.
Definition product_code_rank m n := Nat.max (S m) n.
Definition witness_ambient m n := carrier (5 + product_code_rank m n).
Definition product_witnesses m n a b := eligible_bijections
  (dependent_product (decode a) (fun x => decode (b x)))
  (coding_targets (product_code_rank m n)) (iterated_power (witness_ambient m n) 4).

Lemma witness_ambient_transitive m n : transitive_set (witness_ambient m n).
Proof. apply iterated_power_transitive, omega_codes_transitive. Qed.
Lemma product_subset_ambient m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  INC (dependent_product (decode a) (fun x => decode (b x))) (witness_ambient m n).
Proof.
  intros Ha Hb. apply witness_ambient_transitive.
  apply dependent_product_level_bound; [apply omega_codes_transitive | |].
  - intros x Hx. apply (carrier_inclusion m (product_code_rank m n));
      [unfold product_code_rank; lia | exact (decoding_subset_bound m a Ha x Hx)].
  - intros x Hx y Hy. apply (carrier_inclusion n (product_code_rank m n));
      [unfold product_code_rank; lia | exact (decoding_subset_bound n (b x) (Hb x Hx) y Hy)].
Qed.
Lemma target_subset_ambient m n K :
  IN K (coding_targets (product_code_rank m n)) -> INC K (witness_ambient m n).
Proof.
  intros HK x Hx. apply (carrier_inclusion (product_code_rank m n) (5 + product_code_rank m n));
    [lia | exact (coding_target_bound _ K HK x Hx)].
Qed.
Theorem product_witnesses_nonempty
  (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  exists e, IN e (product_witnesses m n a b).
Proof.
  intros Ha Hb. destruct (decoded_product_code classical_logic comparison gap choice
    m n a b Ha Hb) as [c [Hc [f Hf]]].
  exists (Couple (decode c) f). apply eligible_bijections_complete.
  - apply witness_ambient_transitive.
  - apply product_subset_ambient; assumption.
  - apply target_subset_ambient, coding_target_member; exact Hc.
  - apply coding_target_member; exact Hc.
  - exact Hf.
Qed.
Theorem product_witnesses_rank_bound m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  IN (product_witnesses m n a b) (carrier (13 + product_code_rank m n)).
Proof.
  intros Ha Hb.
  replace (carrier (13 + product_code_rank m n)) with (iterated_power (witness_ambient m n) 8).
  - apply eligible_bijections_rank_bound; [apply witness_ambient_transitive | |].
    + apply product_subset_ambient; assumption.
    + apply target_subset_ambient.
  - unfold witness_ambient, carrier. rewrite iterated_power_add. reflexivity.
Qed.
Print Assumptions product_witnesses_nonempty.
Print Assumptions product_witnesses_rank_bound.
Check product_witnesses_nonempty.

(** Pull ordinary choice back along an extensional, set-indexed family.
    This is a graph construction, not a meta-level function choice axiom. *)
Theorem choose_extensional_family (AC : family_choice) I F :
  family_extensional F -> (forall x, IN x I -> exists y, IN y (F x)) ->
  exists g, IN g (dependent_product I F).
Proof.
  intros HF Hne. destruct (AC (family_range I F)) as [c Hc].
  - intros Y [i E]. destruct (Hne (pi2 I i) (index_member I i)) as [y Hy].
    exists y; exact (IN_sound_right y _ _ (EQ_sym _ _ E) Hy).
  - exists (graph I (fun x => apply_set c (F x))).
    apply dependent_product_introduction.
    + intros x y E. apply apply_set_extensional; [apply EQ_refl | apply HF; exact E].
    + intros x Hx. apply (apply_set_typed (family_range I F) (fun Y => Y) c (F x) Hc).
      destruct (IN_EXType I x Hx) as [i E]. exists i; apply HF; exact E.
Qed.
Print Assumptions coding_targets_bounded.
Print Assumptions choose_extensional_family.
