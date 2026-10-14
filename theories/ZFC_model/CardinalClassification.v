(** Conditional cardinal arithmetic, not additional global axioms.
    These generic principles mention neither codes nor PTS products. Their
    derivation from a precise first-order BZC+GCH theory is still required. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetBijections ProductEmbedding
  CountableCodes CardinalGrowth CardinalHierarchy CantorBernstein CodeUniverses
  PowersetSquares CountableDichotomy BoundedChoiceSequence.
Import CodeUniverses.CodeUniverses.

Definition cardinal_comparability := forall A B : Ens, embeds A B \/ embeds B A.
Definition infinite_powerset_gap := forall K X : Ens,
  embeds omega_codes K -> embeds K X -> embeds X (Power K) ->
  embeds X K \/ embeds (Power K) X.

Lemma equinumerous_embeds A B : equinumerous A B -> embeds A B.
Proof. intros [f [HT [HI HS]]]. exists f; split; assumption. Qed.

Section Classification.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.

Theorem infinite_bounded_classification i X :
  embeds omega_codes X -> embeds X (carrier i) ->
  exists j, j <= i /\ equinumerous X (carrier j).
Proof.
  induction i as [|i IH]; intros Hinf Hbound.
  - exists 0; split; [lia |]. apply cantor_bernstein; assumption.
  - destruct (comparison X (carrier i)) as [Hbelow | Habove].
    + destruct (IH Hinf Hbelow) as [j [Hj HE]]. exists j; split; [lia | exact HE].
    + destruct (gap (carrier i) X (countable_into_carrier i) Habove Hbound)
        as [Hbelow | Htop].
      * destruct (IH Hinf Hbelow) as [j [Hj HE]]. exists j; split; [lia | exact HE].
      * exists (S i); split; [lia |]. apply cantor_bernstein; assumption.
Qed.
Theorem infinite_bounded_code i X :
  embeds omega_codes X -> embeds X (carrier i) ->
  exists a, IN a (U i) /\ equinumerous X (decode a).
Proof.
  intros Hinf Hbound.
  destruct (infinite_bounded_classification i X Hinf Hbound) as [j [Hj HE]].
  exists (repr (infinite j)); split; [apply infinite_membership; exact Hj |].
  eapply equinumerous_trans; [exact HE |].
  apply (cantor_bernstein classical_logic).
  - eapply embeds_equal_domain; [apply decode_infinite | apply embeds_reflexive].
  - eapply embeds_equal_domain; [apply EQ_sym; apply decode_infinite | apply embeds_reflexive].
Qed.
Theorem infinite_decoded_product_code m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  embeds omega_codes (dependent_product (decode a) (fun x => decode (b x))) ->
  exists c, IN c (U (Nat.max (S m) n)) /\
    equinumerous (dependent_product (decode a) (fun x => decode (b x))) (decode c).
Proof.
  intros Ha Hb Hinf. apply infinite_bounded_code; [exact Hinf |].
  apply decoded_dependent_product_bound; assumption.
Qed.
End Classification.

Theorem bounded_cardinal_code (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) i X :
  embeds X (carrier i) -> exists a, IN a (U i) /\ equinumerous X (decode a).
Proof.
  intro HX. destruct (bounded_finite_countable_from_choice classical_logic choice X)
    as [[n Hn] | [c [_ Hinf]]].
  - exists (repr (finite n)); split; [apply finite_in_every_universe |].
    eapply equinumerous_trans; [exact Hn |]. apply (cantor_bernstein classical_logic).
    + eapply embeds_equal_domain; [exact (decode_repr carrier (finite n)) | apply embeds_reflexive].
    + eapply embeds_equal_domain; [apply EQ_sym; exact (decode_repr carrier (finite n)) | apply embeds_reflexive].
  - apply (infinite_bounded_code classical_logic comparison gap i X); [| exact HX].
    exists (bounded_choice_sequence X c); exact Hinf.
Qed.
Theorem decoded_product_code (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  exists c, IN c (U (Nat.max (S m) n)) /\
    equinumerous (dependent_product (decode a) (fun x => decode (b x))) (decode c).
Proof.
  intros Ha Hb. apply (bounded_cardinal_code classical_logic comparison gap choice).
  apply decoded_dependent_product_bound; assumption.
Qed.

(** Uniqueness needs neither GCH nor cardinal comparison. *)
Theorem carrier_classification_unique X i j :
  equinumerous X (carrier i) -> equinumerous X (carrier j) -> i = j.
Proof.
  intros Hi Hj. destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - exfalso; apply (carrier_strict i j Hlt).
    eapply embeds_transitive.
    + apply equinumerous_embeds, equinumerous_sym; exact Hj.
    + apply equinumerous_embeds; exact Hi.
  - exfalso; apply (carrier_strict j i Hgt).
    eapply embeds_transitive.
    + apply equinumerous_embeds, equinumerous_sym; exact Hi.
    + apply equinumerous_embeds; exact Hj.
Qed.
Print Assumptions infinite_bounded_classification.
Print Assumptions carrier_classification_unique.
Print Assumptions infinite_bounded_code.
Print Assumptions infinite_decoded_product_code.
Check infinite_bounded_classification.
Check infinite_decoded_product_code.
Print Assumptions bounded_cardinal_code.
Print Assumptions decoded_product_code.
Check decoded_product_code.
