(** Both directions of the relational bounded-order axiom. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRUnary DirectRUnaryAxioms DirectRSeparation.
Import ListNotations.
Module UnaryBounded.
Import Codes Core Structural NegativeLogic Unary UnaryAxioms.

Definition bounded_atoms {n} cutoff (d : Term nat n) :=
  map (fun i => E d (lift_closed (Unary.numeral i))) (seq 0 (S cutoff)).
Definition Bounded {n} cutoff (d : Term nat n) := FlatOr (bounded_atoms cutoff d).
Lemma bounded_atoms_formed {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> Forall (formed Γ) (bounded_atoms cutoff d).
Proof.
  intro Hd. unfold bounded_atoms. apply Forall_map, Forall_forall. intros i Hi.
  exists 5. apply equality_in_context; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
Qed.
Lemma shift_bounded {n} cutoff (d : Term nat n) :
  shift (Bounded cutoff d) = Bounded cutoff (shift d).
Proof.
  unfold Bounded, bounded_atoms. rewrite shift_flat, map_map. f_equal.
  apply map_ext. intro i. rewrite shift_E, <- lift_closed_shift. reflexivity.
Qed.
Lemma finite_branch_order {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Unary.Domain) -> i <= cutoff ->
  inhabited Γ (E d (lift_closed (Unary.numeral i))) ->
  inhabited Γ (O d (lift_closed (Unary.numeral cutoff))).
Proof.
  intros Hd Hi [h Hh].
  pose proof (lift_closed_typed Γ _ _ (Unary.numeral_typed i)) as HiD.
  pose proof (lift_closed_typed Γ _ _ (Unary.numeral_typed cutoff)) as HcD.
  pose proof (equality_order_in_context Γ _ _ _ Hd HiD Hh) as Hdi.
  destruct (ground_order_in_context Γ i cutoff Hi) as [k Hk].
  eexists. exact (order_transitivity_in_context Γ _ _ _ _ _ Hd HiD HcD Hdi Hk).
Qed.
Lemma order_stable_in_context {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  stable Γ (O d e).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ order_stability_typed) as H.
  change (Typed Γ (lift_closed order_stability)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (Neg (Neg (O (shift V0) V0))) (O (shift V0) V0))))) in H.
  unfold Neg in H. feed H Hd. feed H He. eexists. exact H.
Qed.
Theorem bounded_to_order {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Bounded cutoff d) ->
  inhabited Γ (O d (lift_closed (Unary.numeral cutoff))).
Proof.
  intros Hd Hb. pose proof (bounded_atoms_formed Γ cutoff d Hd) as Hformed.
  eapply flat_eliminate; [exact Hformed | | |exact Hb |].
  - exists 6. apply order_in_context; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - apply order_stable_in_context; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_O, <- lift_closed_shift.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
      rewrite shift_E, <- lift_closed_shift in HA.
      apply (finite_branch_order _ cutoff _ i); [exact Hd' |apply in_seq in Hi; lia |exact HA].
Qed.
Theorem order_to_bounded {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (admitted d) ->
  inhabited Γ (O d (lift_closed (Unary.numeral cutoff))) -> inhabited Γ (Bounded cutoff d).
Proof.
  intros Hd Hg Ho. pose proof (case_atoms_formed Γ cutoff d Hd) as Hformed.
  eapply flat_eliminate; [exact Hformed | | |apply bounded_case_in_context; assumption |].
  - apply flat_formed, bounded_atoms_formed. exact Hd.
  - apply flat_stable, bounded_atoms_formed. exact Hd.
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_bounded.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
        rewrite shift_E, <- lift_closed_shift in HA.
        apply (flat_injection _ _ _ (E (shift d) (lift_closed (Unary.numeral i)))).
        -- apply bounded_atoms_formed. exact Hd'.
        -- unfold bounded_atoms. apply in_map_iff. exists i. auto.
        -- exact HA.
      * destruct Hin as [<-|[]]. rewrite shift_O, <- lift_closed_shift in HA.
        pose proof (inhabited_shift _ _ (O (lift_closed (Unary.numeral (S cutoff))) d) Ho) as Ho'.
        rewrite shift_O, <- lift_closed_shift in Ho'.
        apply flat_from_bottom; [apply bounded_atoms_formed; exact Hd' |].
        destruct HA as [h Hh]. destruct Ho' as [k Hk].
        pose proof (order_transitivity_in_context _ _ _ _ _ _
          (lift_closed_typed _ _ _ (Unary.numeral_typed (S cutoff))) Hd'
          (lift_closed_typed _ _ _ (Unary.numeral_typed cutoff)) Hh Hk) as Hback.
        eapply arrow_elim; [apply Separation.no_back_in_context |eexists; exact Hback].
Qed.

Definition Equivalence {n} (A B : Term nat n) := Conj (Arrow A B) (Arrow B A).
Lemma equivalence_intro {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed Γ B -> inhabited Γ (Arrow A B) -> inhabited Γ (Arrow B A) ->
  inhabited Γ (Equivalence A B).
Proof.
  intros HA HB Hab Hba. unfold Equivalence, Conj. apply arrow_intro.
  - apply arrow_formed; [apply arrow_formed; assumption |].
    apply arrow_formed; [apply arrow_formed; assumption |exists 1; apply bottom_in_context].
  - rewrite <- lift_closed_shift.
    pose proof (newest Γ (Arrow (Arrow A B) (Arrow (Arrow B A) (lift_closed Bottom)))) as Hk.
    normalize_shifts Hk.
    eapply arrow_elim.
    + eapply arrow_elim; [exact Hk |].
      pose proof (inhabited_shift _ _ (Arrow (Arrow A B) (Arrow (Arrow B A) (lift_closed Bottom))) Hab) as H.
      rewrite shift_arrow in H. exact H.
    + pose proof (inhabited_shift _ _ (Arrow (Arrow A B) (Arrow (Arrow B A) (lift_closed Bottom))) Hba) as H.
      rewrite shift_arrow in H. exact H.
Qed.
Definition BoundEquivalence {n} cutoff (d : Term nat n) :=
  Equivalence (O d (lift_closed (Unary.numeral cutoff))) (Bounded cutoff d).
Lemma shift_bound_equivalence {n} cutoff (d : Term nat n) :
  shift (BoundEquivalence cutoff d) = BoundEquivalence cutoff (shift d).
Proof.
  unfold BoundEquivalence, Equivalence, Conj, Neg.
  rewrite !shift_arrow, shift_bounded, shift_O, <- !lift_closed_shift. reflexivity.
Qed.
Theorem bounded_equivalence {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (admitted d) ->
  inhabited Γ (BoundEquivalence cutoff d).
Proof.
  intros Hd Hg.
  assert (HO : formed Γ (O d (lift_closed (Unary.numeral cutoff)))).
  { exists 6. apply order_in_context; [exact Hd |apply lift_closed_typed, Unary.numeral_typed]. }
  assert (HB : formed Γ (Bounded cutoff d)) by (apply flat_formed, bounded_atoms_formed; exact Hd).
  apply equivalence_intro; [exact HO |exact HB | |].
  - apply arrow_intro; [exact HO |]. rewrite shift_bounded.
    apply order_to_bounded.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (inhabited_shift _ _ (O d (lift_closed (Unary.numeral cutoff))) Hg) as H.
      unfold shift in H. rewrite rename_admitted in H. exact H.
    + pose proof (newest Γ (O d (lift_closed (Unary.numeral cutoff)))) as H.
      rewrite shift_O, <- lift_closed_shift in H. exact H.
  - apply arrow_intro; [exact HB |]. rewrite shift_O, <- lift_closed_shift.
    apply bounded_to_order.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (newest Γ (Bounded cutoff d)) as H. rewrite shift_bounded in H. exact H.
Qed.
Definition R4 cutoff : closed_term := Π Unary.Domain (Arrow (admitted V0) (BoundEquivalence cutoff V0)).
Theorem R4_realized cutoff : Realizes (R4 cutoff).
Proof.
  assert (Hd : Typed (ε & Unary.Domain) V0 (lift_closed Unary.Domain))
    by exact (tV (ε & Unary.Domain) fzero).
  assert (H : inhabited (ε & Unary.Domain) (Arrow (admitted V0) (BoundEquivalence cutoff V0))).
  { apply arrow_intro.
    - exists 12. apply admitted_formation_in_context. exact Hd.
    - rewrite shift_bound_equivalence. apply bounded_equivalence.
      + rewrite lift_closed_shift. exact (weakening RankSorts _ _ (admitted V0) Hd).
      + pose proof (newest (ε & Unary.Domain) (admitted V0)) as Hg.
        unfold shift in Hg. rewrite rename_admitted in Hg. exact Hg. }
  destruct H as [p Hp]. exists (lam Unary.Domain p). exact (tLam Unary.domain_formation Hp).
Qed.
End UnaryBounded.
