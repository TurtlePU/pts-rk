(** A concrete powerset hierarchy and the all-rank decoding bound.
    No GCH premise is used here. Identifying these representatives with
    finite-index alephs and obtaining exact product codes is still open. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  ProductEmbedding CodeUniverses CountableCodes CardinalGrowth.
Import CodeUniverses.CodeUniverses.

Definition carrier n := iterated_power omega_codes n.
Definition decode := El carrier.
Theorem carrier_monotone i j : i <= j -> embeds (carrier i) (carrier j).
Proof. apply iterated_power_monotone. Qed.
Theorem carrier_strict i j : i < j -> ~ embeds (carrier j) (carrier i).
Proof. apply iterated_power_strict. Qed.
Theorem countable_into_carrier i : embeds omega_codes (carrier i).
Proof. apply (iterated_power_monotone omega_codes 0 i); lia. Qed.
Theorem universe_into_carrier j i : embeds (U j) (carrier i).
Proof.
  eapply embeds_transitive; [| apply countable_into_carrier].
  exists (counting_graph j). destruct (counting_bijection j) as [Hf [Hi Hs]].
  split; assumption.
Qed.
Theorem code_value_bound i c : Allowed i c -> embeds (code_value carrier c) (carrier i).
Proof.
  intro Hc. destruct c as [n|j|j]; cbn [code_value].
  - eapply embeds_transitive; [apply finite_carrier_embeds_omega | apply countable_into_carrier].
  - apply carrier_monotone; exact Hc.
  - apply universe_into_carrier.
Qed.
Theorem decoding_bound i a : IN a (U i) -> embeds (decode a) (carrier i).
Proof.
  intro Ha. apply universe_membership in Ha as [c [Hc E]].
  assert (Ev : EQ (decode a) (code_value carrier c)).
  { eapply EQ_tran; [apply decoding_extensional; exact E | apply decode_repr]. }
  eapply embeds_equal_domain; [apply EQ_sym; exact Ev | apply code_value_bound; exact Hc].
Qed.
Theorem concrete_sort_axiom i : IN (repr (sort i)) (decode (repr (sort 0))).
Proof. apply sort_axiom. Qed.
Theorem concrete_decoded_product_empty j g :
  ~ IN g (dependent_product (decode (repr (sort j))) decode).
Proof. apply decoded_sort_product_empty. Qed.

Print Assumptions carrier_monotone.
Print Assumptions carrier_strict.
Print Assumptions universe_into_carrier.
Print Assumptions code_value_bound.
Print Assumptions decoding_bound.
Print Assumptions concrete_sort_axiom.
Print Assumptions concrete_decoded_product_empty.
Check decoding_bound.
Check concrete_sort_axiom.
