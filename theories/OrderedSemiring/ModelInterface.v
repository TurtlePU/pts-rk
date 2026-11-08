(** Native-context interface for the independent first-order translation.
    Only the carrier/constructors are shared with Unary; E, O and Good differ. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary.
From OrderedSemiring Require Import RigCodes ObservationEquality NaturalOrder FiniteCuts.
Import ListNotations.
Module Model.
Import CommonCodes Core Structural NegativeLogic.
Definition Domain := Unary.Domain.
Definition zero := Unary.zero.
Definition successor := Unary.successor.
Definition numeral := Unary.numeral.
Definition domain_formation := Unary.domain_formation.
Definition zero_typed := Unary.zero_typed.
Definition successor_in_context := @Unary.successor_in_context.
Definition good_zero := RigCodes.good_zero 15.
Definition good_successor := RigCodes.good_successor 15.
Definition good_zero_typed := RigCodes.good_zero_15_typed.
Definition good_successor_typed := RigCodes.good_successor_15_typed.
Definition equality_reflexivity := ObservationEquality.reflexivity.
Definition equality_reflexivity_typed := ObservationEquality.reflexivity_typed.
Definition equality_stability := ObservationEquality.stability.
Definition equality_stability_typed := ObservationEquality.stability_typed.
Definition E {n} (d e : Term nat n) :=
  app (app (lift_closed ObservationEquality.Equality) d) e.
Definition O {n} (d e : Term nat n) :=
  app (app (lift_closed NaturalOrder.Order) d) e.
Definition admitted {n} (d : Term nat n) := app (lift_closed (RigCodes.Good 15)) d.
Definition reverse (op : closed_term) := close
  (nlams [(100,NClosed Domain);(101,NClosed Domain)]
    (napps (NClosed op) [NVar 101;NVar 100])) eq_refl.
Definition addition := reverse Unary.addition.
Definition multiplication := reverse Unary.multiplication.
Lemma addition_typed : Typed ε addition (Arrow Domain (Arrow Domain Domain)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_typed : Typed ε multiplication (Arrow Domain (Arrow Domain Domain)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_in_context {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ (E d e) (𝓤 7).
Proof. apply FiniteCuts.equality_formation. Qed.
Lemma order_in_context {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ (O d e) (𝓤 15).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ NaturalOrder.order_formation) as H.
  change (Typed Γ (lift_closed NaturalOrder.Order)
    (Arrow (lift_closed Domain) (Arrow (lift_closed Domain) (𝓤 15)))) in H.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hd) He).
Qed.
Lemma admitted_formation_in_context {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Domain) -> Typed Γ (admitted d) (𝓤 17).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ RigCodes.good_15_formation) as H.
  change (Typed Γ (lift_closed (RigCodes.Good 15))
    (Arrow (lift_closed Domain) (𝓤 17))) in H.
  exact (arrow_application _ _ _ _ _ H Hd).
Qed.
Ltac model_substitution H :=
  unfold E, O, admitted in H; structural_substitution_in H.
Ltac feed H Hu :=
  let J := fresh "Happ" in pose proof (tApp H Hu) as J;
  model_substitution J; clear H; rename J into H.
Ltac feed_arrow H Hu := Unary.feed_arrow H Hu.
Lemma order_stable_in_context {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) -> stable Γ (O d e).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ NaturalOrder.stability_typed) as H.
  change (Typed Γ (lift_closed NaturalOrder.stability)
    (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (Neg (Neg (O (shift V0) V0))) (O (shift V0) V0))))) in H.
  unfold Neg in H. feed H Hd. feed H He. eexists. exact H.
Qed.
Print Assumptions admitted_formation_in_context.
Print Assumptions order_stable_in_context.
End Model.
