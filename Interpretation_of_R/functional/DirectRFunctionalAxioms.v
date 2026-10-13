(** Uniform realization of the original five functional R axiom schemes. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRPositive.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations DirectRProofs
  DirectRFunctionalTerms DirectRFunctionalBounded DirectRFunctionalAddition
  DirectRFunctionalMultiplication DirectRFunctionalCases DirectRFunctionalSeparation.
Import ListNotations.
Module FunctionalAxioms.
Import Codes Core Structural NegativeLogic FunctionalBounded FunctionalAddition
  FunctionalMultiplication FunctionalCases.
Definition bounded_atoms {k} n (d : Term nat k) :=
  map (fun i => EqAt d (lift_closed (numeral i))) (seq 0 (S n)).
Definition Bounded {k} n (d : Term nat k) := FlatOr (bounded_atoms n d).
Definition comparison_atoms {k} n (d : Term nat k) :=
  [LeAt d (lift_closed (numeral n)); LeAt (lift_closed (numeral n)) d].
Definition Comparison {k} n (d : Term nat k) := FlatOr (comparison_atoms n d).
Lemma bounded_atoms_formed {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> Forall (formed Γ) (bounded_atoms n d).
Proof.
  intro Hd. apply Forall_map, Forall_forall. intros i Hi. exists 6.
  apply equality_formation; [exact Hd |apply lift_closed_typed, Foundations.numeral_typed].
Qed.
Lemma comparison_atoms_formed {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> Forall (formed Γ) (comparison_atoms n d).
Proof.
  intro Hd. constructor; [exists 6 |constructor; [exists 6 |constructor]];
    apply order_formation; try assumption; apply lift_closed_typed, Foundations.numeral_typed.
Qed.
Lemma rename_flat {k l} (f : Fin k -> Fin l) xs :
  rename f (FlatOr xs) = FlatOr (map (rename f) xs).
Proof.
  rewrite rename_as_replace, replace_flat. f_equal. apply map_ext. intro x.
  symmetry. apply rename_as_replace.
Qed.
Lemma rename_bounded {k l} (f : Fin k -> Fin l) n d :
  rename f (Bounded n d) = Bounded n (rename f d).
Proof.
  unfold Bounded, bounded_atoms. rewrite rename_flat, map_map. f_equal.
  apply map_ext. intro i. rewrite rename_equality, rename_lift_closed. reflexivity.
Qed.
Lemma rename_comparison {k l} (f : Fin k -> Fin l) n d :
  rename f (Comparison n d) = Comparison n (rename f d).
Proof.
  unfold Comparison, comparison_atoms. rewrite rename_flat. cbn [map].
  rewrite !rename_order, !rename_lift_closed. reflexivity.
Qed.
Lemma rename_good {k l} (f : Fin k -> Fin l) d :
  rename f (GoodAt d) = GoodAt (rename f d).
Proof. unfold GoodAt. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma no_back_in_context {k} (Γ : Ctx nat k) n :
  inhabited Γ (Neg (LeAt (lift_closed (numeral (S n))) (lift_closed (numeral n)))).
Proof.
  destruct (FunctionalSeparation.no_back_realized n) as [p Hp].
  exists (lift_closed p). exact (lift_closed_typed Γ _ _ Hp).
Qed.
Theorem order_to_bounded {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) ->
  inhabited Γ (LeAt d (lift_closed (numeral n))) -> inhabited Γ (Bounded n d).
Proof.
  intros Hd Hg HO. pose proof (FunctionalTerms.admitted_observed Γ d Hd Hg) as Gd.
  apply (case_eliminate Γ n d); [exact Hd | | |apply bounded_case; assumption | |].
  - apply flat_formed, bounded_atoms_formed. exact Hd.
  - apply flat_stable, bounded_atoms_formed. exact Hd.
  - intros l Δ f i Hext Hi HE. rewrite rename_bounded.
    apply (flat_injection _ _ _ (EqAt (rename f d) (lift_closed (numeral i)))).
    + apply bounded_atoms_formed. exact (extension_domain _ _ _ _ Hext Hd).
    + unfold bounded_atoms. apply in_map_iff. exists i. split; [reflexivity |apply in_seq; lia].
    + exact HE.
  - intros l Δ f Hext HL. rewrite rename_bounded.
    pose proof (extension_domain _ _ _ _ Hext Hd) as Hd'.
    pose proof (extension_observed _ _ _ _ Hext Gd) as Gd'.
    pose proof (Positive.extension_inhabited _ _ _ _ Hext HO) as HO'.
    rewrite rename_order, rename_lift_closed in HO'.
    apply flat_from_bottom; [apply bounded_atoms_formed; exact Hd' |].
    eapply arrow_elim; [apply no_back_in_context |].
    apply (order_transitivity Δ (lift_closed (numeral (S n))) (rename f d) (lift_closed (numeral n)));
      try assumption; try (apply lift_closed_typed, Foundations.numeral_typed); apply numeral_observed.
Qed.
Lemma finite_branch_order {k} (Γ : Ctx nat k) n d i :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) -> i <= n ->
  inhabited Γ (EqAt d (lift_closed (numeral i))) -> inhabited Γ (LeAt d (lift_closed (numeral n))).
Proof.
  intros Hd Gd Hi HE.
  apply (order_transitivity Γ d (lift_closed (numeral i)) (lift_closed (numeral n)));
    try assumption; try (apply lift_closed_typed, Foundations.numeral_typed); try apply numeral_observed.
  - apply (order_congruence Γ d d d (lift_closed (numeral i))); try assumption;
      try (apply lift_closed_typed, Foundations.numeral_typed); try apply numeral_observed.
    + apply equality_reflexivity; assumption.
    + apply order_reflexivity; assumption.
  - apply ground_order. exact Hi.
Qed.
Theorem comparison {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) -> inhabited Γ (Comparison n d).
Proof.
  intros Hd Hg. pose proof (FunctionalTerms.admitted_observed Γ d Hd Hg) as Gd.
  apply (case_eliminate Γ n d); [exact Hd | | |apply bounded_case; assumption | |].
  - apply flat_formed, comparison_atoms_formed. exact Hd.
  - apply flat_stable, comparison_atoms_formed. exact Hd.
  - intros l Δ f i Hext Hi HE. rewrite rename_comparison.
    apply (flat_injection _ _ _ (LeAt (rename f d) (lift_closed (numeral n)))).
    + apply comparison_atoms_formed. exact (extension_domain _ _ _ _ Hext Hd).
    + left. reflexivity.
    + apply (finite_branch_order Δ n _ i); try assumption.
      * exact (extension_domain _ _ _ _ Hext Hd).
      * exact (extension_observed _ _ _ _ Hext Gd).
  - intros l Δ f Hext HL. rewrite rename_comparison.
    pose proof (extension_domain _ _ _ _ Hext Hd) as Hd'.
    pose proof (extension_observed _ _ _ _ Hext Gd) as Gd'.
    apply (flat_injection _ _ _ (LeAt (lift_closed (numeral n)) (rename f d))).
    + apply comparison_atoms_formed. exact Hd'.
    + right. left. reflexivity.
    + apply (order_transitivity Δ (lift_closed (numeral n)) (lift_closed (numeral (S n))) (rename f d));
        try assumption; try (apply lift_closed_typed, Foundations.numeral_typed); try apply numeral_observed.
      apply ground_order. lia.
Qed.
Theorem R4_realized n : Realizes (R4 n).
Proof.
  unfold R4. apply product_intro; [exists 3; apply Foundations.domain_formation |].
  assert (Hd : Typed (ε & Domain) V0 (lift_closed Domain)) by exact (tV (ε & Domain) fzero).
  change (inhabited (ε & Domain) (Positive.Arrows
    [GoodAt V0; LeAt V0 (lift_closed (numeral n))] (Bounded n V0))).
  apply Positive.arrows_intro.
  - constructor; [exists 12; apply good_at_formation; exact Hd |].
    constructor; [exists 6; apply order_formation; [exact Hd |apply lift_closed_typed, Foundations.numeral_typed] |constructor].
  - intros l Δ f Hext Hargs. rewrite rename_bounded. apply order_to_bounded.
    + exact (extension_domain _ _ _ _ Hext Hd).
    + rewrite <- rename_good. apply Hargs. left. reflexivity.
    + rewrite <- (rename_lift_closed f (numeral n)), <- rename_order.
      apply Hargs. right. left. reflexivity.
Qed.
Theorem R5_realized n : Realizes (R5 n).
Proof.
  unfold R5. apply product_intro; [exists 3; apply Foundations.domain_formation |].
  assert (Hd : Typed (ε & Domain) V0 (lift_closed Domain)) by exact (tV (ε & Domain) fzero).
  change (inhabited (ε & Domain) (Positive.Arrows [GoodAt V0] (Comparison n V0))).
  apply Positive.arrows_intro.
  - constructor; [exists 12; apply good_at_formation; exact Hd |constructor].
  - intros l Δ f Hext Hargs. rewrite rename_comparison. apply comparison.
    + exact (extension_domain _ _ _ _ Hext Hd).
    + rewrite <- rename_good. apply Hargs. left. reflexivity.
Qed.
Theorem all_axioms_realized a : Realizes (axiom_type a).
Proof.
  destruct a; cbn [axiom_type].
  - apply Kernel.R1_realized.
  - apply Kernel.R2_realized.
  - apply FunctionalSeparation.R3_realized. assumption.
  - apply R4_realized.
  - apply R5_realized.
Qed.
End FunctionalAxioms.
