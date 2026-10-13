(** Properties of a supplied union of finite powerset levels. No set of
    levels is constructed using sup here, and no hierarchy existence axiom
    is declared. Identification with V_{omega+omega} requires the base to
    be V_omega; that identification remains a separate foundation obligation. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalGrowth CardinalHierarchy HierarchyBounds CodeHierarchyBounds.
Import CodeUniverses.CodeUniverses.

Definition tower_envelope (W H : Ens) : Prop :=
  forall x, IN x H <-> exists n, IN x (iterated_power W n).

Lemma power_iteration_monotone W V n :
  INC W V -> INC (iterated_power W n) (iterated_power V n).
Proof.
  intro HW. induction n; [exact HW | apply Power_mon; exact IHn].
Qed.

Theorem envelope_contains_level W H n : tower_envelope W H ->
  IN (iterated_power W n) H.
Proof.
  intro HH. apply HH. exists (S n). apply INC_IN_Power. intros x Hx; exact Hx.
Qed.
Theorem envelope_transitive W H : transitive_set W -> tower_envelope W H ->
  transitive_set H.
Proof.
  intros HW HH x Hx y Hy. apply HH in Hx as [n Hx]. apply HH. exists n.
  exact (iterated_power_transitive W n HW x Hx y Hy).
Qed.
Theorem envelope_power_closed W H x : transitive_set W -> tower_envelope W H ->
  IN x H -> IN (Power x) H.
Proof.
  intros HW HH Hx. apply HH in Hx as [n Hx]. apply HH. exists (S (S n)).
  apply INC_IN_Power, Power_mon. exact (iterated_power_transitive W n HW x Hx).
Qed.

Theorem envelope_carrier W H i : INC omega_codes W -> tower_envelope W H ->
  IN (carrier i) H.
Proof.
  intros HW HH. apply HH. exists (S i). apply INC_IN_Power.
  apply power_iteration_monotone; exact HW.
Qed.

Theorem envelope_universe W H i : INC omega_codes W -> tower_envelope W H ->
  IN (U i) H.
Proof.
  intros HW HH. apply HH. exists 1. apply INC_IN_Power.
  intros x Hx. apply HW. exact (universe_subset_omega i x Hx).
Qed.

Theorem envelope_decode W H i a : INC omega_codes W -> tower_envelope W H ->
  IN a (U i) -> IN (decode a) H.
Proof.
  intros HW HH Ha. apply HH. exists (S i). apply INC_IN_Power.
  intros x Hx. apply (power_iteration_monotone omega_codes W i HW).
  exact (decoding_subset_bound i a Ha x Hx).
Qed.

Theorem envelope_decoding_graph W H i : INC omega_codes W -> tower_envelope W H ->
  IN (decoding_graph i) H.
Proof.
  intros HW HH. apply HH. exists (5 + i).
  apply (power_iteration_monotone omega_codes W (5 + i) HW).
  apply decoding_graph_rank_bound.
Qed.
Theorem envelope_decoded_product W H i : INC omega_codes W -> tower_envelope W H ->
  IN (dependent_product (U i) decode) H.
Proof.
  intros HW HH. apply HH. exists (5 + i).
  apply (power_iteration_monotone omega_codes W (5 + i) HW).
  apply decoded_product_rank_bound.
Qed.

Print Assumptions envelope_contains_level.
Print Assumptions envelope_transitive.
Print Assumptions envelope_power_closed.
Print Assumptions envelope_carrier.
Print Assumptions envelope_universe.
Print Assumptions envelope_decode.
Print Assumptions envelope_decoding_graph.
Print Assumptions envelope_decoded_product.
Check envelope_decoding_graph.
