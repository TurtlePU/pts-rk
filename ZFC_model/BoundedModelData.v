(** Set bounds for the SAME global model data. Bounds over finite powers
    of H do not assert that global choices or the decoder are members of H.
    The explicit hierarchy and Choice premises remain visible. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes CardinalGrowth HierarchyBounds SuppliedHierarchy
  CountableDichotomy GlobalCodeChoice BoundedFormulas BoundedDecoder
  BoundedCodeSelection BoundedDecodedSelection.
Import Bounded CodeUniverses.CodeUniverses.

Definition nonemptyF {n} (Y : Fin n) : Formula n := ex Y (equal fzero fzero).
Lemma nonempty_formula_correct {n} (r : Fin n -> Ens) Y :
  holds (nonemptyF Y) r <-> exists y, IN y (r Y).
Proof.
  cbn [nonemptyF holds]. split.
  - intros [y [Hy _]]; exists y; exact Hy.
  - intros [y Hy]; exists y; split; [exact Hy | apply EQ_refl].
Qed.

Theorem bounded_subset_selector_exists : family_choice -> forall X,
  exists c, subset_choice X c /\ IN c (Power (Prod (Power X) X)).
Proof.
  intros AC X. destruct (AC (nonempty_subsets X)) as [c Hc].
  - intros Y HY; exact (IN_Comp_P _ _ _ nonempty_predicate HY).
  - exists c; split.
    + intros Y HY Hne. apply (apply_set_typed (nonempty_subsets X) (fun Y => Y) c Y Hc).
      apply IN_P_Comp; [exact nonempty_predicate | exact HY | exact Hne].
    + apply INC_IN_Power. intros e He.
      destruct (dependent_product_pair _ _ c e Hc He) as [Y [y [E [HY Hxy]]]].
      apply (IN_sound_left (Couple Y y) e _ E), Couple_IN_Prod.
      * exact (Comp_INC _ _ _ HY).
      * apply (IN_Power_INC X Y (Comp_INC _ _ _ HY)).
        exact (proj2 (proj1 (proj2 (dependent_product_elimination _ _ _ Hc)) Y y Hxy)).
Qed.

Theorem global_selector_with_bound (AC : family_choice) H :
  exists s,
    IN s (Power (Prod (Power (Prod all_codes (global_graph_bound H)))
      (Prod all_codes (global_graph_bound H)))) /\
    forall A, (exists e, IN e (global_code_witnesses H A)) ->
      IN (apply_set s (global_code_witnesses H A)) (global_code_witnesses H A).
Proof.
  destruct (bounded_subset_selector_exists AC (Prod all_codes (global_graph_bound H)))
    as [s [HS HB]]. exists s; split; [exact HB |].
  intros A Hne. apply HS; [apply INC_IN_Power, Comp_INC | exact Hne].
Qed.

Section Envelope.
Variables W H : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.

Lemma envelope_couple x y : IN x H -> IN y H -> IN (Couple x y) H.
Proof.
  intros Hx Hy. apply HH in Hx as [i Hx]; apply HH in Hy as [j Hy].
  apply HH. exists (3 + Nat.max i j). rewrite <- iterated_power_add.
  apply couple_rank_bound; [apply iterated_power_transitive; exact HW | |].
  - apply (iterated_power_inclusion W i (Nat.max i j) HW); [lia | exact Hx].
  - apply (iterated_power_inclusion W j (Nat.max i j) HW); [lia | exact Hy].
Qed.

Lemma envelope_cartesian A B : INC A H -> INC B H -> INC (Prod A B) H.
Proof.
  intros HA HB e He. destruct (IN_Prod_EXType A B e He) as [x [y E]].
  assert (Hxy : IN (Couple x y) (Prod A B)) by
    (exact (IN_sound_left e _ _ (EQ_sym _ _ E) He)).
  destruct (Couple_Prod_IN A B x y Hxy) as [Hx Hy].
  apply (IN_sound_left (Couple x y) e H E), envelope_couple; [apply HA | apply HB]; assumption.
Qed.

Lemma omega_subset_envelope : INC omega_codes H.
Proof. intros x Hx; apply HH; exists 0; apply HO; exact Hx. Qed.

Theorem bounded_decoder_in_power_envelope : IN (bounded_decoder H) (Power H).
Proof.
  apply INC_IN_Power. intros e He.
  apply (envelope_cartesian omega_codes H omega_subset_envelope (fun x Hx => Hx)).
  exact (Comp_INC _ _ _ He).
Qed.

Theorem decoded_selection_cartesian_bound s :
  IN (decoded_witness_graph H s)
    (Power (Prod (Power H) (Prod omega_codes (global_graph_bound H)))).
Proof.
  apply INC_IN_Power. intros e He.
  pose proof (Comp_INC _ _ _ He) as HE.
  destruct (IN_Prod_EXType _ _ e HE) as [A [y E]].
  assert (HP : IN (Couple A y)
    (Prod (decoded_code_sources H) (Prod omega_codes (global_graph_bound H)))) by
    (exact (IN_sound_left e _ _ (EQ_sym _ _ E) HE)).
  destruct (Couple_Prod_IN _ _ A y HP) as [HA Hy].
  apply (IN_sound_left (Couple A y) e _ E), Couple_IN_Prod;
    [exact (Comp_INC _ _ _ HA) | exact Hy].
Qed.

Theorem bounded_model_selector_exists (AC : family_choice) : exists s,
  IN s (Power (Prod (Power (Prod all_codes (global_graph_bound H)))
    (Prod all_codes (global_graph_bound H)))) /\
  IN (decoded_witness_graph H s)
    (dependent_product (decoded_code_sources H) (fun _ => Prod omega_codes (global_graph_bound H))) /\
  forall A, IN A (decoded_code_sources H) ->
    EQ (apply_set (decoded_witness_graph H s) A)
      (apply_set s (global_code_witnesses H A)).
Proof.
  destruct (global_selector_with_bound AC H) as [s [HB HS]].
  exists s; split; [exact HB |]. split.
  - exact (decoded_witness_graph_typed W H HW HO HH s HS).
  - exact (decoded_witness_graph_beta W H HW HO HH s HS).
Qed.
End Envelope.

Print Assumptions nonempty_formula_correct.
Print Assumptions bounded_subset_selector_exists.
Print Assumptions global_selector_with_bound.
Print Assumptions envelope_couple.
Print Assumptions envelope_cartesian.
Print Assumptions bounded_decoder_in_power_envelope.
Print Assumptions decoded_selection_cartesian_bound.
Print Assumptions bounded_model_selector_exists.
Check bounded_model_selector_exists.
