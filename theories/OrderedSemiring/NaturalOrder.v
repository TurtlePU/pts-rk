(** The draft's inherited order. Differences have G11, not G15.
    These first primitives do not yet establish antisymmetry or monotonicity. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary.
From OrderedSemiring Require Import RigCodes ObservationEquality.
Import ListNotations.
Module NaturalOrder.
Import CommonCodes Core ObservationEquality.

Definition difference x y := NPi 120 nD
  (nArrow (NApp (RigCodes.nGood 11) (NVar 120))
    (nArrow (nEq (napps nA [NVar 120;x]) y) nVoid)).
Definition nOrder := nlams [(100,nD);(101,nD)]
  (nNeg (difference (NVar 100) (NVar 101))).
Definition Order := close nOrder eq_refl.
Definition nO x y := napps (NClosed Order) [x;y].
Definition nStrict := nlams [(100,nD);(101,nD)]
  (nConj (nO (NVar 100) (NVar 101)) (nNeg (nEq (NVar 100) (NVar 101)))).
Definition Strict := close nStrict eq_refl.

Definition reflexivity := close
  (nlams [(100,nD);(110,difference (NVar 100) (NVar 100))]
    (napps (NVar 110) [nZ; RigCodes.nGoodZero 11;
      NApp (NClosed ObservationEquality.reflexivity) (NVar 100)])) eq_refl.
Definition reflexivity_type := close
  (NPi 100 nD (nO (NVar 100) (NVar 100))) eq_refl.
Definition zero_least := close
  (nlams [(100,nD);(101,NApp (RigCodes.nGood 11) (NVar 100));
    (110,difference nZ (NVar 100))]
    (napps (NVar 110) [NVar 100;NVar 101;
      NApp (NClosed ObservationEquality.reflexivity) (NVar 100)])) eq_refl.
Definition zero_least_type := close
  (npis [(100,nD);(101,NApp (RigCodes.nGood 11) (NVar 100))]
    (nO nZ (NVar 100))) eq_refl.
Definition stability := close
  (nlams [(100,nD);(101,nD);(102,nNeg (nNeg (nO (NVar 100) (NVar 101))));
    (110,difference (NVar 100) (NVar 101))]
    (NApp (NVar 102) (NLam 111 (nO (NVar 100) (NVar 101))
      (NApp (NVar 111) (NVar 110))))) eq_refl.
Definition stability_type := close
  (npis [(100,nD);(101,nD)]
    (nArrow (nNeg (nNeg (nO (NVar 100) (NVar 101))))
      (nO (NVar 100) (NVar 101)))) eq_refl.
Definition witness_intro := close
  (nlams [(100,nD);(101,nD);(102,nD);
    (103,NApp (RigCodes.nGood 11) (NVar 102));
    (104,nEq (napps nA [NVar 102;NVar 100]) (NVar 101));
    (110,difference (NVar 100) (NVar 101))]
    (napps (NVar 110) [NVar 102;NVar 103;NVar 104])) eq_refl.
Definition witness_intro_type := close
  (npis [(100,nD);(101,nD);(102,nD);
    (103,NApp (RigCodes.nGood 11) (NVar 102));
    (104,nEq (napps nA [NVar 102;NVar 100]) (NVar 101))]
    (nO (NVar 100) (NVar 101))) eq_refl.

Lemma order_formation : Typed ε Order
  (Arrow Unary.Domain (Arrow Unary.Domain (𝓤 15))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma strict_formation : Typed ε Strict
  (Arrow Unary.Domain (Arrow Unary.Domain (𝓤 17))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma reflexivity_typed : Typed ε reflexivity reflexivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma zero_least_typed : Typed ε zero_least zero_least_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma stability_typed : Typed ε stability stability_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma witness_intro_typed : Typed ε witness_intro witness_intro_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions order_formation.
Print Assumptions strict_formation.
Print Assumptions reflexivity_typed.
Print Assumptions zero_least_typed.
Print Assumptions stability_typed.
Print Assumptions witness_intro_typed.
End NaturalOrder.
