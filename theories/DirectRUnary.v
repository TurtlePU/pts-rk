(** Unary presentation from the harmonized note, Theorem 4 (label [main]).
    This is distinct from Codes.Domain and the functional Theorem 7.
    All certificates below conclude the original PTS typing judgment. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context DirectRCodes DirectRKernel DirectRCheck.
Import ListNotations.

Module Unary.
Import Codes Core.

Definition bot := NClosed Bottom.
Definition neg A := nArrow A bot.
Definition conj A B := neg (nArrow A (nArrow B bot)).
Definition iff A B := conj (nArrow A B) (nArrow B A).
Definition fields : list (nat * named) :=
  [(0, NSort 1); (1, NVar 0); (2, nArrow (NVar 0) (NVar 0))].
Definition nDomain := npis fields (NVar 0).
Definition nZero := nlams fields (NVar 1).
Definition fold d := napps d [NVar 0; NVar 1; NVar 2].
Definition nSucc := NLam 20 nDomain
  (nlams fields (NApp (NVar 2) (fold (NVar 20)))).
Definition nAdd := nlams [(20,nDomain); (21,nDomain)]
  (nlams fields (napps (NVar 20) [NVar 0; fold (NVar 21); NVar 2])).
Definition nMul := nlams [(20,nDomain); (21,nDomain)]
  (nlams fields (napps (NVar 20) [NVar 0; NVar 1;
    NLam 60 (NVar 0) (napps (NVar 21) [NVar 0; NVar 60; NVar 2])])).

Definition motive := nArrow nDomain (NSort 10).
Definition successor_case := NPi 50 nDomain
  (nArrow (NApp (NVar 40) (NVar 50))
    (NApp (NVar 40) (NApp nSucc (NVar 50)))).
Definition good_fields :=
  [(40,motive); (41,NApp (NVar 40) nZero); (42,successor_case)].
Definition nGood := NLam 20 nDomain
  (npis good_fields (NApp (NVar 40) (NVar 20))).
Definition nGoodZero := nlams good_fields (NVar 41).
Definition nGoodSucc := nlams [(20,nDomain); (23,NApp nGood (NVar 20))]
  (nlams good_fields (napps (NVar 42) [NVar 20;
    napps (NVar 23) [NVar 40; NVar 41; NVar 42]])).

Definition nEquality := nlams [(20,nDomain); (21,nDomain)]
  (NPi 30 (nArrow nDomain (NSort 1))
    (iff (neg (NApp (NVar 30) (NVar 20)))
         (neg (NApp (NVar 30) (NVar 21))))).
Definition observation_fields := fields ++
  [(3,nArrow (NVar 0) (NSort 4));
   (4,NApp (NVar 3) (NVar 1));
   (5,NPi 50 (NVar 0) (nArrow (NApp (NVar 3) (NVar 50))
      (NApp (NVar 3) (NApp (NVar 2) (NVar 50)))))].
Definition nObserved := NLam 20 nDomain
  (npis observation_fields (NApp (NVar 3) (fold (NVar 20)))).
Definition upward := NPi 50 (NVar 0)
  (nArrow (NApp (NVar 3) (NVar 50))
    (nArrow (neg (NApp (NVar 30) (NVar 50)))
      (neg (NApp (NVar 30) (NApp (NVar 2) (NVar 50)))))).
Definition nOrder := nlams [(20,nDomain); (21,nDomain)]
  (npis observation_fields (NPi 30 (nArrow (NVar 0) (NSort 1))
    (nArrow upward (nArrow (neg (NApp (NVar 30) (fold (NVar 20))))
      (neg (NApp (NVar 30) (fold (NVar 21)))))))).
Definition nOrderRefl := NLam 20 nDomain
  (nlams observation_fields (nlams [(30,nArrow (NVar 0) (NSort 1));
    (31,upward); (32,neg (NApp (NVar 30) (fold (NVar 20))))] (NVar 32))).
Definition nAdmittedOrderRefl := nlams [(20,nDomain); (23,NApp nGood (NVar 20))]
  (NApp nOrderRefl (NVar 20)).

Definition Domain := close nDomain eq_refl.
Definition zero := close nZero eq_refl.
Definition successor := close nSucc eq_refl.
Definition addition := close nAdd eq_refl.
Definition multiplication := close nMul eq_refl.
Definition Good := close nGood eq_refl.
Definition Equality := close nEquality eq_refl.
Definition Observed := close nObserved eq_refl.
Definition Order := close nOrder eq_refl.
Definition good_zero := close nGoodZero eq_refl.
Definition good_successor := close nGoodSucc eq_refl.
Definition order_reflexivity := close nOrderRefl eq_refl.
Definition admitted_order_reflexivity := close nAdmittedOrderRefl eq_refl.

Lemma domain_formation : Typed ε Domain (𝓤 3).
Proof. RkCheck.certify_with 4096. Qed.
Lemma zero_typed : Typed ε zero Domain.
Proof. RkCheck.certify_with 4096. Qed.
Lemma successor_typed : Typed ε successor (Arrow Domain Domain).
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_typed : Typed ε addition (Arrow Domain (Arrow Domain Domain)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_typed : Typed ε multiplication (Arrow Domain (Arrow Domain Domain)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_formation : Typed ε Good (Arrow Domain (𝓤 12)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_formation : Typed ε Equality (Arrow Domain (Arrow Domain (𝓤 5))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_formation : Typed ε Observed (Arrow Domain (𝓤 6)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_formation : Typed ε Order (Arrow Domain (Arrow Domain (𝓤 6))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_zero_typed : Typed ε good_zero (app Good zero).
Proof. RkCheck.certify_with 4096. Qed.
Definition good_successor_type := close
  (NPi 20 nDomain (nArrow (NApp nGood (NVar 20))
    (NApp nGood (NApp nSucc (NVar 20))))) eq_refl.
Lemma good_successor_typed : Typed ε good_successor good_successor_type.
Proof. RkCheck.certify_with 4096. Qed.
Definition order_reflexivity_type := close
  (NPi 20 nDomain (napps nOrder [NVar 20; NVar 20])) eq_refl.
Definition rho_translation := close
  (NPi 20 nDomain (nArrow (NApp nGood (NVar 20))
    (napps nOrder [NVar 20; NVar 20]))) eq_refl.
Lemma order_reflexivity_typed : Typed ε order_reflexivity order_reflexivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma rho_realized : Typed ε admitted_order_reflexivity rho_translation.
Proof. RkCheck.certify_with 4096. Qed.

(** These foundations are not Theorem 4: separation, bounded cases, axiom
    realization, deduction preservation, and source non-derivability remain. *)
End Unary.
