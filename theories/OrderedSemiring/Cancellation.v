(** Cancellation and zero reflection use retained G7 evidence inside
    G11 induction. No positive domain evidence is projected from a
    negative conjunction or negative disjunction. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From OrderedSemiring Require Import RigCodes DomainClosure ObservationEquality
  ArithmeticCongruence RetainedInduction SemiringLaws SuccessorSeparation.
Import ListNotations.

Module Cancellation.
Import CommonCodes Core ObservationEquality ArithmeticCongruence SemiringLaws.

Definition good_add7 x y gx gy :=
  napps (NClosed (DomainClosure.good_addition 7)) [x;y;gx;gy].
Definition injective x y gx gy h :=
  napps (NClosed SuccessorSeparation.successor_injectivity) [x;y;gx;gy;h].
Definition nonzero x gx h :=
  napps (NClosed SuccessorSeparation.successor_nonzero) [x;gx;h].
Definition explode x y b := napps (NClosed stability)
  [x;y;NLam 164 (nNeg (nEq x y)) b].

(** Explicit stability of an implication whose result is equality. *)
Definition implication_stable A x y :=
  NLam 160 (nNeg (nNeg (nArrow A (nEq x y))))
    (NLam 161 A
      (napps (NClosed stability) [x;y;
        NLam 162 (nNeg (nEq x y))
          (NApp (NVar 160) (NLam 163 (nArrow A (nEq x y))
            (NApp (NVar 162) (NApp (NVar 163) (NVar 161)))))])).
Definition retained_imp x gx (A l r : named -> named) base
    (step : named -> named -> named -> named) :=
  napps (NClosed RetainedInduction.rank8_proof)
    [NLam 150 nD (nArrow (A (NVar 150)) (nEq (l (NVar 150)) (r (NVar 150))));
     NLam 150 nD (implication_stable (A (NVar 150)) (l (NVar 150)) (r (NVar 150)));
     base;
     nlams [(150,nD);(152,nG (NVar 150));
       (151,nArrow (A (NVar 150)) (nEq (l (NVar 150)) (r (NVar 150))))]
       (step (NVar 150) (NVar 152) (NVar 151));x;gx].

Definition cancel_fields := raw3 ++
  [(110,g11 (NVar 100));(111,nG (NVar 101));(112,nG (NVar 102))].
Definition cancel_premise u := nEq (add u (NVar 101)) (add u (NVar 102)).
Definition nCancelLeft := nlams cancel_fields
  (retained_imp (NVar 100) (NVar 110) cancel_premise
    (fun _ => NVar 101) (fun _ => NVar 102)
    (NLam 153 (cancel_premise nZ) (NVar 153))
    (fun u gu ih => NLam 153 (cancel_premise (suc u))
      (NApp ih (injective (add u (NVar 101)) (add u (NVar 102))
        (good_add7 u (NVar 101) gu (NVar 111))
        (good_add7 u (NVar 102) gu (NVar 112)) (NVar 153))))).
Definition addition_cancellation_left := close nCancelLeft eq_refl.
Definition addition_cancellation_left_type := close
  (npis cancel_fields (nArrow (cancel_premise (NVar 100))
    (nEq (NVar 101) (NVar 102)))) eq_refl.
Definition cancel_left a x y ga gx gy h :=
  napps (NClosed addition_cancellation_left) [a;x;y;ga;gx;gy;h].

Definition zero_sum_fields := raw2 ++ [(110,g11 (NVar 100));(111,nG (NVar 101))].
Definition zero_sum_premise u := nEq (add u (NVar 101)) nZ.
Definition nZeroSumLeft := nlams zero_sum_fields
  (retained_imp (NVar 100) (NVar 110) zero_sum_premise (fun u => u) (fun _ => nZ)
    (NLam 153 (zero_sum_premise nZ) (refl nZ))
    (fun u gu ih => NLam 153 (zero_sum_premise (suc u))
      (explode (suc u) nZ
        (nonzero (add u (NVar 101)) (good_add7 u (NVar 101) gu (NVar 111)) (NVar 153))))).
Definition zero_sum_left := close nZeroSumLeft eq_refl.
Definition zero_sum_left_type := close
  (npis zero_sum_fields (nArrow (zero_sum_premise (NVar 100))
    (nEq (NVar 100) nZ))) eq_refl.
Definition sum_zero_left x y gx gy h :=
  napps (NClosed zero_sum_left) [x;y;gx;gy;h].

Definition nZeroSumRight := nlams
  (raw2 ++ [(110,nG (NVar 100));(111,g11 (NVar 101));
           (113,nEq (add (NVar 100) (NVar 101)) nZ)])
  (sum_zero_left (NVar 101) (NVar 100) (NVar 111) (NVar 110)
    (trans (add (NVar 101) (NVar 100)) (add (NVar 100) (NVar 101)) nZ
      (add_comm (NVar 101) (NVar 100) (lower (NVar 101) (NVar 111)) (NVar 110))
      (NVar 113))).
Definition zero_sum_right := close nZeroSumRight eq_refl.
Definition zero_sum_right_type := close
  (npis (raw2 ++ [(110,nG (NVar 100));(111,g11 (NVar 101))])
    (nArrow (nEq (add (NVar 100) (NVar 101)) nZ) (nEq (NVar 101) nZ))) eq_refl.

(** Both branches return Void; no sum is eliminated into positive evidence. *)
Definition nOr A B := nArrow (nNeg A) (nArrow (nNeg B) nVoid).
Definition zero_factor x y := nOr (nEq x nZ) (nEq y nZ).
Definition product_premise u y := nEq (mul u y) nZ.
Definition product_property u y := nArrow (product_premise u y) (zero_factor u y).
Definition product_property_stable u y :=
  nlams [(160,nNeg (nNeg (product_property u y)));(161,product_premise u y);
          (162,nNeg (nEq u nZ));(163,nNeg (nEq y nZ))]
    (NApp (NVar 160) (NLam 164 (product_property u y)
      (napps (NVar 164) [NVar 161;NVar 162;NVar 163]))).
Definition nNoZeroProduct := nlams guarded11_2
  (napps (NClosed RetainedInduction.rank9_proof)
    [NLam 150 nD (product_property (NVar 150) (NVar 101));
     NLam 150 nD (product_property_stable (NVar 150) (NVar 101));
     nlams [(153,product_premise nZ (NVar 101));
             (154,nNeg (nEq nZ nZ));(155,nNeg (nEq (NVar 101) nZ))]
       (NApp (NVar 154) (refl nZ));
     nlams [(150,nD);(152,nG (NVar 150));(151,product_property (NVar 150) (NVar 101));
             (153,product_premise (suc (NVar 150)) (NVar 101));
             (154,nNeg (nEq (suc (NVar 150)) nZ));(155,nNeg (nEq (NVar 101) nZ))]
       (NApp (NVar 155)
         (sum_zero_left (NVar 101) (mul (NVar 150) (NVar 101)) (NVar 111)
           (good_mul7 (NVar 150) (NVar 101) (NVar 152) (lower (NVar 101) (NVar 111)))
           (NVar 153)));
     NVar 100;NVar 110]).
Definition no_zero_product := close nNoZeroProduct eq_refl.
Definition no_zero_product_type := close
  (npis guarded11_2 (product_property (NVar 100) (NVar 101))) eq_refl.

Lemma addition_cancellation_left_typed :
  Typed ε addition_cancellation_left addition_cancellation_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma zero_sum_left_typed : Typed ε zero_sum_left zero_sum_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma zero_sum_right_typed : Typed ε zero_sum_right zero_sum_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma no_zero_product_typed : Typed ε no_zero_product no_zero_product_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions addition_cancellation_left_typed.
Print Assumptions zero_sum_left_typed.
Print Assumptions zero_sum_right_typed.
Print Assumptions no_zero_product_typed.
End Cancellation.
