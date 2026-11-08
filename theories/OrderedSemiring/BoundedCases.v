(** All relational R4/R5 instances under the corrected common equality,
    G15 guard and G11-difference order. The cutoff is an arbitrary nat. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryBounded.
From OrderedSemiring Require Import RigCodes NaturalOrder FiniteCuts OrderNumerals OrderCuts.
Import ListNotations.

Module BoundedCases.
Import CommonCodes Core Structural NegativeLogic FiniteCuts OrderCuts.

Definition Bounded {n} cutoff (d : Term nat n) := FlatOr (atoms cutoff d).
Definition Compare {n} cutoff (d : Term nat n) :=
  FlatOr [O d (lift_closed (Unary.numeral cutoff));
          O (lift_closed (Unary.numeral cutoff)) d].
Definition BoundEquivalence {n} cutoff (d : Term nat n) :=
  UnaryBounded.Equivalence (O d (lift_closed (Unary.numeral cutoff))) (Bounded cutoff d).

Lemma shift_bounded {n} cutoff (d : Term nat n) :
  shift (Bounded cutoff d) = Bounded cutoff (shift d).
Proof. unfold Bounded. rewrite shift_flat, shift_atoms. reflexivity. Qed.
Lemma shift_compare {n} cutoff (d : Term nat n) :
  shift (Compare cutoff d) = Compare cutoff (shift d).
Proof.
  unfold Compare. rewrite shift_flat. cbn [map].
  rewrite !shift_O, <- lift_closed_shift. reflexivity.
Qed.
Lemma shift_G {n} r (d : Term nat n) : shift (G r d) = G r (shift d).
Proof. unfold G, shift. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_bound_equivalence {n} cutoff (d : Term nat n) :
  shift (BoundEquivalence cutoff d) = BoundEquivalence cutoff (shift d).
Proof.
  unfold BoundEquivalence, UnaryBounded.Equivalence, Conj, Neg.
  rewrite !shift_arrow, shift_bounded, shift_O, <- !lift_closed_shift. reflexivity.
Qed.
Lemma good15_formation {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ (G 15 d) (𝓤 17).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ RigCodes.good_15_formation) as H.
  change (Typed Γ (lift_closed (RigCodes.Good 15))
    (Arrow (lift_closed Unary.Domain) (𝓤 17))) in H.
  exact (arrow_application _ _ _ _ _ H Hd).
Qed.
Lemma comparison_atoms_formed {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) ->
  Forall (formed Γ) [O d (lift_closed (Unary.numeral cutoff));
    O (lift_closed (Unary.numeral cutoff)) d].
Proof.
  intro Hd. repeat constructor; exists 15; apply order_formation;
    try exact Hd; apply lift_closed_typed, Unary.numeral_typed.
Qed.

Theorem bounded_to_order {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Bounded cutoff d) ->
  inhabited Γ (O d (lift_closed (Unary.numeral cutoff))).
Proof.
  intros Hd Hb. pose proof (atoms_formed Γ cutoff d Hd) as Hformed.
  eapply flat_eliminate; [exact Hformed | | |exact Hb |].
  - exists 15. apply order_formation; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - apply order_stable; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_O, <- lift_closed_shift.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
      rewrite shift_E, <- lift_closed_shift in HA.
      apply (finite_equality_to_order _ cutoff _ i); [exact Hd' |apply in_seq in Hi; lia |exact HA].
Qed.
Theorem order_to_bounded {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 15 d) ->
  inhabited Γ (O d (lift_closed (Unary.numeral cutoff))) -> inhabited Γ (Bounded cutoff d).
Proof.
  intros Hd Hg Ho. pose proof (atoms_formed Γ cutoff d Hd) as Hformed.
  eapply branches_eliminate.
  - exact Hformed.
  - apply flat_formed. exact Hformed.
  - apply flat_stable. exact Hformed.
  - apply finite_cut_in_context; assumption.
  - apply arrow_intro; [exists 15; apply tail_formation; exact Hd |].
    rewrite shift_bounded.
    pose proof (weakening RankSorts _ _ (Tail cutoff d) Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
    pose proof (newest Γ (Tail cutoff d)) as HT. rewrite shift_tail in HT.
    pose proof (inhabited_shift _ _ (Tail cutoff d) Ho) as HO. rewrite shift_O, <- lift_closed_shift in HO.
    apply flat_from_bottom; [apply atoms_formed; exact Hd' |].
    exact (large_order_contradiction _ cutoff _ Hd' HT HO).
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_bounded.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
      rewrite shift_E, <- lift_closed_shift in HA.
      apply (flat_injection _ _ _ (E (shift d) (lift_closed (Unary.numeral i)))).
      * apply atoms_formed. exact Hd'.
      * unfold atoms. apply in_map_iff. exists i. auto.
      * exact HA.
Qed.
Theorem bounded_equivalence {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 15 d) ->
  inhabited Γ (BoundEquivalence cutoff d).
Proof.
  intros Hd Hg.
  assert (HO : formed Γ (O d (lift_closed (Unary.numeral cutoff)))).
  { exists 15. apply order_formation; [exact Hd |apply lift_closed_typed, Unary.numeral_typed]. }
  assert (HB : formed Γ (Bounded cutoff d)) by (apply flat_formed, atoms_formed; exact Hd).
  apply UnaryBounded.equivalence_intro; [exact HO |exact HB | |].
  - apply arrow_intro; [exact HO |]. rewrite shift_bounded.
    apply order_to_bounded.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (inhabited_shift _ _ (O d (lift_closed (Unary.numeral cutoff))) Hg) as H.
      rewrite shift_G in H. exact H.
    + pose proof (newest Γ (O d (lift_closed (Unary.numeral cutoff)))) as H.
      rewrite shift_O, <- lift_closed_shift in H. exact H.
  - apply arrow_intro; [exact HB |]. rewrite shift_O, <- lift_closed_shift.
    apply bounded_to_order.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (newest Γ (Bounded cutoff d)) as H. rewrite shift_bounded in H. exact H.
Qed.
Definition R4 cutoff : closed_term := Π Unary.Domain
  (Arrow (G 15 V0) (BoundEquivalence cutoff V0)).
Theorem R4_realized cutoff : Realizes (R4 cutoff).
Proof.
  assert (Hd : Typed (ε & Unary.Domain) V0 (lift_closed Unary.Domain))
    by exact (tV (ε & Unary.Domain) fzero).
  unfold R4. apply product_intro; [exists 3; exact Unary.domain_formation |].
  apply arrow_intro; [exists 17; apply good15_formation; exact Hd |].
  rewrite shift_bound_equivalence. apply bounded_equivalence.
  - rewrite lift_closed_shift. apply weakening. exact Hd.
  - pose proof (newest (ε & Unary.Domain) (G 15 V0)) as H. rewrite shift_G in H. exact H.
Qed.

Lemma comparison_finite {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Unary.Domain) -> i <= cutoff ->
  inhabited Γ (E d (lift_closed (Unary.numeral i))) -> inhabited Γ (Compare cutoff d).
Proof.
  intros Hd Hi He. apply (flat_injection _ _ _ (O d (lift_closed (Unary.numeral cutoff)))).
  - apply comparison_atoms_formed. exact Hd.
  - left. reflexivity.
  - exact (finite_equality_to_order Γ cutoff d i Hd Hi He).
Qed.
Lemma comparison_large {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Tail cutoff d) ->
  inhabited Γ (Compare cutoff d).
Proof.
  intros Hd HT. apply (flat_injection _ _ _ (O (lift_closed (Unary.numeral cutoff)) d)).
  - apply comparison_atoms_formed. exact Hd.
  - right. left. reflexivity.
  - exact (large_to_order Γ cutoff d Hd HT).
Qed.
Theorem comparison_in_context {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 15 d) ->
  inhabited Γ (Compare cutoff d).
Proof.
  intros Hd Hg. pose proof (atoms_formed Γ cutoff d Hd) as Hformed.
  eapply branches_eliminate.
  - exact Hformed.
  - apply flat_formed, comparison_atoms_formed. exact Hd.
  - apply flat_stable, comparison_atoms_formed. exact Hd.
  - apply finite_cut_in_context; assumption.
  - apply arrow_intro; [exists 15; apply tail_formation; exact Hd |].
    rewrite shift_compare. apply comparison_large.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (newest Γ (Tail cutoff d)) as H. rewrite shift_tail in H. exact H.
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_compare.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
      rewrite shift_E, <- lift_closed_shift in HA.
      apply (comparison_finite _ cutoff _ i); [exact Hd' |apply in_seq in Hi; lia |exact HA].
Qed.
Definition R5 cutoff : closed_term := Π Unary.Domain (Arrow (G 15 V0) (Compare cutoff V0)).
Theorem R5_realized cutoff : Realizes (R5 cutoff).
Proof.
  assert (Hd : Typed (ε & Unary.Domain) V0 (lift_closed Unary.Domain))
    by exact (tV (ε & Unary.Domain) fzero).
  unfold R5. apply product_intro; [exists 3; exact Unary.domain_formation |].
  apply arrow_intro; [exists 17; apply good15_formation; exact Hd |].
  rewrite shift_compare. apply comparison_in_context.
  - rewrite lift_closed_shift. apply weakening. exact Hd.
  - pose proof (newest (ε & Unary.Domain) (G 15 V0)) as H. rewrite shift_G in H. exact H.
Qed.

Print Assumptions R4_realized.
Print Assumptions R5_realized.

Lemma good15_numeral {n} (Γ : Ctx nat n) k :
  inhabited Γ (G 15 (lift_closed (Unary.numeral k))).
Proof.
  rewrite <- iterate_zero. apply OrderNumerals.good_iterate_context.
  - exact RigCodes.good_successor_15_typed.
  - apply lift_closed_typed, Unary.zero_typed.
  - exists (lift_closed (RigCodes.good_zero 15)).
    exact (lift_closed_typed Γ _ _ RigCodes.good_zero_15_typed).
Qed.
Theorem false_order_numerals {n} (Γ : Ctx nat n) i j : j < i ->
  inhabited Γ (Neg (O (lift_closed (Unary.numeral i)) (lift_closed (Unary.numeral j)))).
Proof.
  intro Hij. apply arrow_intro.
  - exists 15. apply order_formation; apply lift_closed_typed, Unary.numeral_typed.
  - rewrite <- lift_closed_shift.
    eapply flat_refute with (xs:=atoms j (lift_closed (Unary.numeral i))).
    + apply order_to_bounded.
      * apply lift_closed_typed, Unary.numeral_typed.
      * apply good15_numeral.
      * pose proof (newest Γ (O (lift_closed (Unary.numeral i))
          (lift_closed (Unary.numeral j)))) as H.
        rewrite shift_O, <- !lift_closed_shift in H. exact H.
    + intros A HA. apply in_map_iff in HA. destruct HA as [k [<- Hk]].
      apply OrderNumerals.numeral_inequality. apply in_seq in Hk. lia.
Qed.
Print Assumptions false_order_numerals.
End BoundedCases.
