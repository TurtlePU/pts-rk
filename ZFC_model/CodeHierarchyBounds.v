(** Concrete bounds for the existing codes and decoding graph. These are
    Ens theorems, not a claim that sup-based existence is justified in BZC. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes CardinalGrowth CardinalHierarchy HierarchyBounds BoundedFamilies.
Import CodeUniverses.CodeUniverses.

Theorem omega_codes_transitive : transitive_set omega_codes.
Proof.
  intros x Hx y Hy. apply omega_membership in Hx as [[|n] E].
  - destruct (Vide_est_vide y (IN_sound_right y x Vide E Hy)).
  - apply omega_membership. exists n. apply IN_Sing_EQ.
    exact (IN_sound_right y x (Sing (numeral n)) E Hy).
Qed.

Theorem carrier_inclusion i j : i <= j -> INC (carrier i) (carrier j).
Proof. apply iterated_power_inclusion, omega_codes_transitive. Qed.

Lemma universe_subset_omega i : INC (U i) omega_codes.
Proof.
  intros x Hx. apply universe_membership in Hx as [c [_ E]].
  apply omega_membership. exists (key c); exact E.
Qed.
Lemma finite_subset_omega n : INC (finite_carrier n) omega_codes.
Proof.
  intros x Hx. apply finite_carrier_membership in Hx as [k [_ E]].
  apply omega_membership. exists k; exact E.
Qed.
Theorem universe_level_bound i j : INC (U i) (carrier j).
Proof.
  intros x Hx. apply (carrier_inclusion 0 j); [lia |].
  exact (universe_subset_omega i x Hx).
Qed.
Theorem decoding_subset_bound i a : IN a (U i) -> INC (decode a) (carrier i).
Proof.
  intros Ha y Hy. apply universe_membership in Ha as [c [Hc E]].
  assert (Ev : EQ (decode a) (code_value carrier c)).
  { eapply EQ_tran; [apply decoding_extensional; exact E | apply decode_repr]. }
  pose proof (IN_sound_right y _ _ Ev Hy) as Hv.
  destruct c as [n|j|j]; cbn [code_value] in Hv.
  - apply (carrier_inclusion 0 i); [lia |]. apply finite_subset_omega in Hv; exact Hv.
  - apply (carrier_inclusion j i Hc); exact Hv.
  - apply (universe_level_bound j i); exact Hv.
Qed.

Definition decoding_graph i := graph (U i) decode.
Theorem decoding_graph_typed i :
  IN (decoding_graph i) (dependent_product (U i) (fun _ => Power (carrier i))).
Proof.
  apply dependent_product_introduction.
  - intros x y E; exact (decoding_extensional carrier x y E).
  - intros a Ha. apply INC_IN_Power. apply decoding_subset_bound; exact Ha.
Qed.
Theorem decoding_graph_beta i a : IN a (U i) ->
  EQ (apply_set (decoding_graph i) a) (decode a).
Proof. apply apply_set_beta. intros x y E; exact (decoding_extensional carrier x y E). Qed.
Theorem decoding_graph_rank_bound i : IN (decoding_graph i) (carrier (5 + i)).
Proof.
  unfold decoding_graph, carrier. replace (5 + i) with (4 + S i) by lia.
  rewrite <- (iterated_power_add omega_codes (S i) 4).
  apply graph_rank_bound.
  - apply iterated_power_transitive, omega_codes_transitive.
  - apply universe_level_bound.
  - intros a Ha. apply INC_IN_Power. apply decoding_subset_bound; exact Ha.
Qed.
Theorem decoded_product_rank_bound i :
  IN (dependent_product (U i) decode) (carrier (5 + i)).
Proof.
  apply dependent_product_level_bound.
  - apply omega_codes_transitive.
  - apply universe_level_bound.
  - apply decoding_subset_bound.
Qed.
Theorem decoding_bounded_range i :
  EQ (bounded_family_range (carrier i) (U i) (decoding_graph i))
     (family_range (U i) (apply_set (decoding_graph i))).
Proof. apply bounded_family_range_equivalence, decoding_graph_typed. Qed.

Print Assumptions omega_codes_transitive.
Print Assumptions carrier_inclusion.
Print Assumptions universe_level_bound.
Print Assumptions decoding_subset_bound.
Print Assumptions decoding_graph_typed.
Print Assumptions decoding_graph_beta.
Print Assumptions decoding_graph_rank_bound.
Print Assumptions decoded_product_rank_bound.
Print Assumptions decoding_bounded_range.
Check decoding_subset_bound.
Check decoding_graph_rank_bound.
