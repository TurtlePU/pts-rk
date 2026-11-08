(** The corrected ordered-rig draft: one carrier, indexed induction budgets.
    The index is the motive rank, not the rank of the certificate itself. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From Interpretation_of_R.relational Require Import DirectRUnary.
Import ListNotations.

Module RigCodes.
Import CommonCodes Core.
Definition nDomain := Unary.nDomain.
Definition nZero := Unary.nZero.
Definition nSucc := Unary.nSucc.
Definition nAdd := Unary.nAdd.
Definition nMul := Unary.nMul.
Definition bot := NClosed Bottom.
Definition neg A := nArrow A bot.
Definition conj A B := neg (nArrow A (nArrow B bot)).
Definition nEta := NLam 20 nDomain
  (nlams Unary.fields (Unary.fold (NVar 20))).

Definition motive r := nArrow nDomain (NSort r).
Definition successor_case := Unary.successor_case.
Definition good_fields r :=
  [(40,motive r); (41,NApp (NVar 40) nZero); (42,successor_case)].
Definition nGood r := NLam 20 nDomain
  (npis (good_fields r) (NApp (NVar 40) (NVar 20))).
Definition nGoodZero r := nlams (good_fields r) (NVar 41).
Definition nGoodSucc r := nlams [(20,nDomain);(23,NApp (nGood r) (NVar 20))]
  (nlams (good_fields r) (napps (NVar 42) [NVar 20;
    napps (NVar 23) [NVar 40;NVar 41;NVar 42]])).
Definition Good r := close (nGood r) eq_refl.
Definition good_zero r := close (nGoodZero r) eq_refl.
Definition good_successor r := close (nGoodSucc r) eq_refl.
Definition good_successor_type r := close
  (npis [(20,nDomain);(23,NApp (nGood r) (NVar 20))]
    (NApp (nGood r) (NApp nSucc (NVar 20)))) eq_refl.

(** Linear-size exact-rank lifts; there is no cumulative-sort rule. *)
Fixpoint J r : closed_term :=
  match r with 0 => 𝓤 0 | S k => Arrow (J k) (𝓤 0) end.
Definition j r : closed_term :=
  match r with 0 => 𝓤 0 | S k => lam (J k) (𝓤 0) end.
Lemma J_formation r : Typed ε (J r) (𝓤 r).
Proof.
  induction r as [|r IH]; cbn [J].
  - apply tU.
  - change (Typed ε (Arrow (J r) (𝓤 0)) (𝓤 (Nat.max (S r) 0))).
    unfold Arrow. apply (tPi IH). apply tU.
Qed.
Lemma j_typed r : Typed ε (j r) (J r).
Proof.
  destruct r as [|r]; cbn [j J]; [apply tU |].
  apply (tLam (J_formation r)). apply tU.
Qed.
Definition nJ r := NClosed (J r).
Definition nJproof r := NClosed (j r).
Definition nLift r A := nArrow (nJ (Nat.pred r)) A.

Definition nLower t r := nlams
  [(100,nDomain); (101,NApp (nGood t) (NVar 100))]
  (nlams (good_fields r)
    (NApp (napps (NVar 101)
      [NLam 102 nDomain (nLift t (NApp (NVar 40) (NVar 102)));
       NLam 103 (nJ (Nat.pred t)) (NVar 41);
       nlams [(104,nDomain);
              (105,nLift t (NApp (NVar 40) (NVar 104)));
              (103,nJ (Nat.pred t))]
         (napps (NVar 42) [NVar 104;NApp (NVar 105) (NVar 103)])])
      (nJproof (Nat.pred t)))).
Definition lowering t r := close (nLower t r) eq_refl.
Definition lowering_type t r := close
  (NPi 100 nDomain (nArrow (NApp (nGood t) (NVar 100))
    (NApp (nGood r) (NVar 100)))) eq_refl.

Lemma good_7_formation : Typed ε (Good 7) (Arrow Unary.Domain (𝓤 9)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_11_formation : Typed ε (Good 11) (Arrow Unary.Domain (𝓤 13)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_15_formation : Typed ε (Good 15) (Arrow Unary.Domain (𝓤 17)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_zero_7_typed : Typed ε (good_zero 7) (app (Good 7) Unary.zero).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_zero_11_typed : Typed ε (good_zero 11) (app (Good 11) Unary.zero).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_zero_15_typed : Typed ε (good_zero 15) (app (Good 15) Unary.zero).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_successor_7_typed : Typed ε (good_successor 7) (good_successor_type 7).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_successor_11_typed : Typed ε (good_successor 11) (good_successor_type 11).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_successor_15_typed : Typed ε (good_successor 15) (good_successor_type 15).
Proof. RkCheck.certify_with 4096. Qed.
Lemma lower_15_11_typed : Typed ε (lowering 15 11) (lowering_type 15 11).
Proof. RkCheck.certify_with 4096. Qed.
Lemma lower_11_7_typed : Typed ε (lowering 11 7) (lowering_type 11 7).
Proof. RkCheck.certify_with 4096. Qed.
Lemma lower_15_7_typed : Typed ε (lowering 15 7) (lowering_type 15 7).
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions J_formation.
Print Assumptions j_typed.
Print Assumptions good_15_formation.
Print Assumptions lower_15_11_typed.
Print Assumptions lower_11_7_typed.
End RigCodes.
