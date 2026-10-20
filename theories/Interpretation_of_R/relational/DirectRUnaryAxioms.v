(** Relational axiom witnesses for the harmonized unary interpretation. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural DirectRLogic.
From Interpretation_of_R.relational Require Import DirectRUnary.
Import ListNotations.

Module UnaryAxioms.
Import CommonCodes Core Structural NegativeLogic Unary.

Lemma rename_case {m n} (f : Fin m -> Fin n) cutoff d :
  rename f (Case cutoff d) = Case cutoff (rename f d).
Proof. rewrite !rename_as_replace, replace_case. reflexivity. Qed.
Lemma rename_admitted {m n} (f : Fin m -> Fin n) d :
  rename f (admitted d) = admitted (rename f d).
Proof. unfold admitted. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma rename_order {m n} (f : Fin m -> Fin n) d e :
  rename f (O d e) = O (rename f d) (rename f e).
Proof. unfold O. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma admitted_formation_in_context {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ (admitted d) (𝓤 12).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ Unary.good_formation) as H.
  change (Typed Γ (lift_closed Unary.Good) (Arrow (lift_closed Unary.Domain) (𝓤 12))) in H.
  exact (arrow_application _ _ _ _ _ H Hd).
Qed.
Lemma bounded_case_in_context {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (admitted d) ->
  inhabited Γ (Case cutoff d).
Proof.
  intros Hd [g Hg]. destruct (bounded_case_realized cutoff) as [p Hp].
  pose proof (lift_closed_typed Γ _ _ Hp) as H.
  unfold lift_closed at 2 in H. unfold bounded_case_type in H.
  rewrite rename_product, rename_arrow, rename_admitted, rename_case in H.
  change (Typed Γ (lift_closed p)
    (Π (lift_closed Unary.Domain) (Arrow (admitted V0) (Case cutoff V0)))) in H.
  pose proof (tApp H Hd) as H1.
  unfold subst in H1. rewrite replace_arrow, replace_case in H1.
  unary_substitution H1.
  eexists. exact (arrow_application _ _ _ _ _ H1 Hg).
Qed.
Lemma ground_order_in_context {n} (Γ : Ctx nat n) i j : i <= j ->
  inhabited Γ (O (lift_closed (Unary.numeral i)) (lift_closed (Unary.numeral j))).
Proof.
  intro Hij. destruct (ground_order_realized i j Hij) as [p Hp].
  exists (lift_closed p). pose proof (lift_closed_typed Γ _ _ Hp) as H.
  unfold lift_closed at 2 in H. rewrite rename_order in H. exact H.
Qed.

Definition Compare {n} cutoff (d : Term nat n) :=
  FlatOr [O d (lift_closed (Unary.numeral cutoff));
          O (lift_closed (Unary.numeral cutoff)) d].
Lemma comparison_atoms_formed {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) ->
  Forall (formed Γ) [O d (lift_closed (Unary.numeral cutoff));
                    O (lift_closed (Unary.numeral cutoff)) d].
Proof.
  intro Hd. repeat constructor; exists 6; apply order_in_context;
    try exact Hd; apply lift_closed_typed, Unary.numeral_typed.
Qed.
Lemma shift_compare {n} cutoff (d : Term nat n) :
  shift (Compare cutoff d) = Compare cutoff (shift d).
Proof.
  unfold Compare. rewrite shift_flat. cbn [map].
  rewrite !shift_O, <- lift_closed_shift. reflexivity.
Qed.
Lemma comparison_finite {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Unary.Domain) -> i <= cutoff ->
  inhabited Γ (E d (lift_closed (Unary.numeral i))) -> inhabited Γ (Compare cutoff d).
Proof.
  intros Hd Hi [h Hh].
  pose proof (lift_closed_typed Γ _ _ (Unary.numeral_typed i)) as HiD.
  pose proof (lift_closed_typed Γ _ _ (Unary.numeral_typed cutoff)) as HcD.
  pose proof (equality_order_in_context Γ _ _ _ Hd HiD Hh) as Hdi.
  destruct (ground_order_in_context Γ i cutoff Hi) as [k Hk].
  apply (flat_injection n Γ _ (O d (lift_closed (Unary.numeral cutoff)))).
  - apply comparison_atoms_formed. exact Hd.
  - left. reflexivity.
  - eexists. exact (order_transitivity_in_context Γ _ _ _ _ _ Hd HiD HcD Hdi Hk).
Qed.
Lemma comparison_large {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) ->
  inhabited Γ (O (lift_closed (Unary.numeral (S cutoff))) d) ->
  inhabited Γ (Compare cutoff d).
Proof.
  intros Hd [h Hh].
  pose proof (lift_closed_typed Γ _ _ (Unary.numeral_typed cutoff)) as HcD.
  pose proof (lift_closed_typed Γ _ _ (Unary.numeral_typed (S cutoff))) as HsD.
  destruct (ground_order_in_context Γ cutoff (S cutoff) (Nat.le_succ_diag_r cutoff)) as [k Hk].
  apply (flat_injection n Γ _ (O (lift_closed (Unary.numeral cutoff)) d)).
  - apply comparison_atoms_formed. exact Hd.
  - right. left. reflexivity.
  - eexists. exact (order_transitivity_in_context Γ _ _ _ _ _ HcD HsD Hd Hk Hh).
Qed.
Theorem comparison_in_context {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (admitted d) ->
  inhabited Γ (Compare cutoff d).
Proof.
  intros Hd Hg. pose proof (case_atoms_formed Γ cutoff d Hd) as Hformed.
  eapply flat_eliminate.
  - exact Hformed.
  - apply flat_formed, comparison_atoms_formed. exact Hd.
  - apply flat_stable, comparison_atoms_formed. exact Hd.
  - apply bounded_case_in_context; assumption.
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_compare.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'.
      rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
        rewrite shift_E, <- lift_closed_shift in HA.
        apply (comparison_finite _ cutoff _ i); [exact Hd' | apply in_seq in Hi; lia | exact HA].
      * destruct Hin as [<-|[]]. rewrite shift_O, <- lift_closed_shift in HA.
        apply comparison_large; assumption.
Qed.

Definition R5 cutoff : closed_term :=
  Π Unary.Domain (Arrow (admitted V0) (Compare cutoff V0)).
Theorem R5_realized cutoff : Realizes (R5 cutoff).
Proof.
  assert (Hd : Typed (ε & Unary.Domain) V0 (lift_closed Unary.Domain))
    by exact (tV (ε & Unary.Domain) fzero).
  assert (H : inhabited (ε & Unary.Domain) (Arrow (admitted V0) (Compare cutoff V0))).
  { apply arrow_intro.
    - exists 12. apply admitted_formation_in_context. exact Hd.
    - rewrite shift_compare. apply comparison_in_context.
      + rewrite lift_closed_shift. exact (weakening RankSorts _ _ (admitted V0) Hd).
      + pose proof (newest (ε & Unary.Domain) (admitted V0)) as Hg.
        unfold shift in Hg. rewrite rename_admitted in Hg. exact Hg. }
  destruct H as [p Hp]. exists (lam Unary.Domain p). exact (tLam Unary.domain_formation Hp).
Qed.
End UnaryAxioms.
