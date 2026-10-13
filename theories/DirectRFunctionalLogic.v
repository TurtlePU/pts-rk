(** Negative atomic stability for the arithmetic-expression interpretation. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRCheck DirectRStructural DirectRLogic DirectRFoundations.
Import ListNotations.
Module FunctionalLogic.
Import Codes Core Structural NegativeLogic.
Definition observation_arguments : list named := map (fun field => NVar (fst field)) observation_fields.
Definition fold_at d := napps d [NVar 0; NVar 1; NVar 2; NVar 3; NVar 4].
Definition nAtomicStable (relation : closed_term) (raw_relation : nat) :=
  let R := napps (NClosed relation) [NVar 20; NVar 21] in
  nlams [(20,nDomain); (21,nDomain); (24,nArrow (nArrow R nBottom) nBottom)]
    (nAbstractObs
      (NLam 25 (napps (NVar raw_relation) [fold_at (NVar 20); fold_at (NVar 21)])
        (NApp (NVar 24) (NLam 26 R
          (napps (NVar 26) (observation_arguments ++ [NVar 25])))))).
Definition equality_stability := close (nAtomicStable Equality 6) eq_refl.
Definition order_stability := close (nAtomicStable Order 7) eq_refl.
Definition equality_stability_type :=
  Π Domain (Π (lift_closed Domain)
    (Arrow (Neg (Neg (EqAt (shift V0) V0))) (EqAt (shift V0) V0))).
Definition order_stability_type :=
  Π Domain (Π (lift_closed Domain)
    (Arrow (Neg (Neg (LeAt (shift V0) V0))) (LeAt (shift V0) V0))).
Theorem equality_stability_typed : Typed ε equality_stability equality_stability_type.
Proof. RkCheck.certify_with 4096. Qed.
Theorem order_stability_typed : Typed ε order_stability order_stability_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_stable {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) -> stable Γ (EqAt d e).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ equality_stability_typed) as H.
  change (Typed Γ (lift_closed equality_stability)
    (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (Neg (Neg (EqAt (shift V0) V0))) (EqAt (shift V0) V0))))) in H.
  unfold Neg in H. Foundations.feed_object H Hd. Foundations.feed_object H He. eexists. exact H.
Qed.
Lemma order_stable {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) -> stable Γ (LeAt d e).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ order_stability_typed) as H.
  change (Typed Γ (lift_closed order_stability)
    (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (Neg (Neg (LeAt (shift V0) V0))) (LeAt (shift V0) V0))))) in H.
  unfold Neg in H. Foundations.feed_object H Hd. Foundations.feed_object H He. eexists. exact H.
Qed.
End FunctionalLogic.
