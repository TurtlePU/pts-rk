(** Generic commutative unital semiring equations for G11-admitted Church
    numerals, in the original PTS and the fixed diagonal-observer equality. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From OrderedSemiring Require Import RigCodes DomainClosure ObservationEquality
  ArithmeticCongruence RetainedInduction.
Import ListNotations.

Module SemiringLaws.
Import CommonCodes Core ObservationEquality ArithmeticCongruence.
Definition one := suc nZ.
Definition g11 x := NApp (RigCodes.nGood 11) x.
Definition lower x gx := napps (NClosed (RigCodes.lowering 11 7)) [x;gx].
Definition sym x y h := napps (NClosed symmetry) [x;y;h].
Definition eq_ind (x gx : named) (l r : named -> named) base (step : named -> named -> named) :=
  napps gx [NLam 150 nD (nEq (l (NVar 150)) (r (NVar 150)));base;
    nlams [(150,nD);(151,nEq (l (NVar 150)) (r (NVar 150)))]
      (step (NVar 150) (NVar 151))].
Definition retained_eq x gx (l r : named -> named) base
    (step : named -> named -> named -> named) :=
  napps (NClosed RetainedInduction.rank7_proof)
    [NLam 150 nD (nEq (l (NVar 150)) (r (NVar 150)));
     NLam 150 nD (napps (NClosed stability) [l (NVar 150);r (NVar 150)]);
     base;
     nlams [(150,nD);(152,nG (NVar 150));
             (151,nEq (l (NVar 150)) (r (NVar 150)))]
       (step (NVar 150) (NVar 152) (NVar 151));x;gx].
Definition raw1 := [(100,nD)].
Definition raw2 := [(100,nD);(101,nD)].
Definition raw3 := [(100,nD);(101,nD);(102,nD)].
Definition guarded1 := raw1 ++ [(110,nG (NVar 100))].
Definition guarded2 := raw2 ++ [(110,nG (NVar 100));(111,nG (NVar 101))].
Definition guarded11_2 := raw2 ++ [(110,g11 (NVar 100));(111,g11 (NVar 101))].
Definition guarded11_3 := raw3 ++
  [(110,g11 (NVar 100));(111,g11 (NVar 101));(112,g11 (NVar 102))].

(** The two additive units and the left multiplicative unit hold through
    observational eta insensitivity, without adding eta conversion. *)
Definition addition_zero_left := close (nlams raw1 (refl (NVar 100))) eq_refl.
Definition addition_zero_left_type := close
  (npis raw1 (nEq (add nZ (NVar 100)) (NVar 100))) eq_refl.
Definition addition_zero_right := addition_zero_left.
Definition addition_zero_right_type := close
  (npis raw1 (nEq (add (NVar 100) nZ) (NVar 100))) eq_refl.
Definition multiplication_one_left := addition_zero_left.
Definition multiplication_one_left_type := close
  (npis raw1 (nEq (mul one (NVar 100)) (NVar 100))) eq_refl.
Definition multiplication_zero_left := close (nlams raw1 (refl nZ)) eq_refl.
Definition multiplication_zero_left_type := close
  (npis raw1 (nEq (mul nZ (NVar 100)) nZ)) eq_refl.

Definition addition_associativity := close
  (nlams raw3 (refl (add (add (NVar 100) (NVar 101)) (NVar 102)))) eq_refl.
Definition addition_associativity_type := close
  (npis raw3 (nEq (add (add (NVar 100) (NVar 101)) (NVar 102))
    (add (NVar 100) (add (NVar 101) (NVar 102))))) eq_refl.
Definition multiplication_associativity := close
  (nlams raw3 (refl (mul (mul (NVar 100) (NVar 101)) (NVar 102)))) eq_refl.
Definition multiplication_associativity_type := close
  (npis raw3 (nEq (mul (mul (NVar 100) (NVar 101)) (NVar 102))
    (mul (NVar 100) (mul (NVar 101) (NVar 102))))) eq_refl.
Definition distribution_first := close
  (nlams raw3 (refl (mul (add (NVar 100) (NVar 101)) (NVar 102)))) eq_refl.
Definition distribution_first_type := close
  (npis raw3 (nEq (mul (add (NVar 100) (NVar 101)) (NVar 102))
    (add (mul (NVar 100) (NVar 102)) (mul (NVar 101) (NVar 102))))) eq_refl.
Definition addition_successor_left := close
  (nlams raw2 (refl (suc (add (NVar 100) (NVar 101))))) eq_refl.
Definition addition_successor_left_type := close
  (npis raw2 (nEq (add (suc (NVar 100)) (NVar 101))
    (suc (add (NVar 100) (NVar 101))))) eq_refl.
Definition multiplication_successor_left := close
  (nlams raw2 (refl (add (NVar 101) (mul (NVar 100) (NVar 101))))) eq_refl.
Definition multiplication_successor_left_type := close
  (npis raw2 (nEq (mul (suc (NVar 100)) (NVar 101))
    (add (NVar 101) (mul (NVar 100) (NVar 101))))) eq_refl.

Definition nAddSuccRight := nlams (raw2 ++ [(110,nG (NVar 100))])
  (eq_ind (NVar 100) (NVar 110)
    (fun u => add u (suc (NVar 101))) (fun u => suc (add u (NVar 101)))
    (refl (suc (NVar 101)))
    (fun u ih => succ_cong (add u (suc (NVar 101))) (suc (add u (NVar 101))) ih)).
Definition addition_successor_right := close nAddSuccRight eq_refl.
Definition addition_successor_right_type := close
  (npis (raw2 ++ [(110,nG (NVar 100))])
    (nEq (add (NVar 100) (suc (NVar 101)))
      (suc (add (NVar 100) (NVar 101))))) eq_refl.
Definition add_succ_right x y gx := napps (NClosed addition_successor_right) [x;y;gx].

Definition nAddComm := nlams guarded2
  (eq_ind (NVar 100) (NVar 110)
    (fun u => add u (NVar 101)) (fun u => add (NVar 101) u)
    (refl (NVar 101))
    (fun u ih => trans (suc (add u (NVar 101))) (suc (add (NVar 101) u))
      (add (NVar 101) (suc u))
      (succ_cong (add u (NVar 101)) (add (NVar 101) u) ih)
      (sym (add (NVar 101) (suc u)) (suc (add (NVar 101) u))
        (add_succ_right (NVar 101) u (NVar 111))))).
Definition addition_commutativity := close nAddComm eq_refl.
Definition addition_commutativity_type := close
  (npis guarded2 (nEq (add (NVar 100) (NVar 101)) (add (NVar 101) (NVar 100)))) eq_refl.
Definition add_comm x y gx gy := napps (NClosed addition_commutativity) [x;y;gx;gy].

Definition nMulZeroRight := nlams guarded1
  (eq_ind (NVar 100) (NVar 110) (fun u => mul u nZ) (fun _ => nZ)
    (refl nZ) (fun _ ih => ih)).
Definition multiplication_zero_right := close nMulZeroRight eq_refl.
Definition multiplication_zero_right_type := close
  (npis guarded1 (nEq (mul (NVar 100) nZ) nZ)) eq_refl.
Definition mul_zero_right x gx := napps (NClosed multiplication_zero_right) [x;gx].
Definition nMulOneRight := nlams guarded1
  (eq_ind (NVar 100) (NVar 110) (fun u => mul u one) (fun u => u)
    (refl nZ) (fun u ih => succ_cong (mul u one) u ih)).
Definition multiplication_one_right := close nMulOneRight eq_refl.
Definition multiplication_one_right_type := close
  (npis guarded1 (nEq (mul (NVar 100) one) (NVar 100))) eq_refl.

Lemma addition_zero_left_typed : Typed ε addition_zero_left addition_zero_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_zero_right_typed : Typed ε addition_zero_right addition_zero_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_one_left_typed : Typed ε multiplication_one_left multiplication_one_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_zero_left_typed : Typed ε multiplication_zero_left multiplication_zero_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_associativity_typed : Typed ε addition_associativity addition_associativity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_associativity_typed : Typed ε multiplication_associativity multiplication_associativity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma distribution_first_typed : Typed ε distribution_first distribution_first_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_successor_left_typed : Typed ε addition_successor_left addition_successor_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_successor_left_typed : Typed ε multiplication_successor_left multiplication_successor_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_successor_right_typed : Typed ε addition_successor_right addition_successor_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_commutativity_typed : Typed ε addition_commutativity addition_commutativity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_zero_right_typed : Typed ε multiplication_zero_right multiplication_zero_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_one_right_typed : Typed ε multiplication_one_right multiplication_one_right_type.
Proof. RkCheck.certify_with 4096. Qed.

(** The retained lower certificate is used only for the interchange of
    the induction variable with the fixed right argument. *)
Definition mul_succ_step y gy u gu ih :=
  trans (suc (add y (mul u (suc y))))
    (suc (add y (add u (mul u y))))
    (suc (add u (add y (mul u y))))
    (succ_cong (add y (mul u (suc y))) (add y (add u (mul u y)))
      (add_second y (mul u (suc y)) (add u (mul u y)) gy ih))
    (succ_cong (add y (add u (mul u y))) (add u (add y (mul u y)))
      (add_first (add y u) (add u y) (mul u y) (add_comm y u gy gu))).
Definition nMulSuccRight := nlams
  (raw2 ++ [(110,g11 (NVar 100));(111,nG (NVar 101))])
  (retained_eq (NVar 100) (NVar 110)
    (fun u => mul u (suc (NVar 101)))
    (fun u => add u (mul u (NVar 101)))
    (refl nZ) (mul_succ_step (NVar 101) (NVar 111))).
Definition multiplication_successor_right := close nMulSuccRight eq_refl.
Definition multiplication_successor_right_type := close
  (npis (raw2 ++ [(110,g11 (NVar 100));(111,nG (NVar 101))])
    (nEq (mul (NVar 100) (suc (NVar 101)))
      (add (NVar 100) (mul (NVar 100) (NVar 101))))) eq_refl.
Definition mul_succ_right x y gx gy :=
  napps (NClosed multiplication_successor_right) [x;y;gx;gy].

Definition nMulComm := nlams guarded11_2
  (retained_eq (NVar 100) (NVar 110)
    (fun u => mul u (NVar 101)) (fun u => mul (NVar 101) u)
    (sym (mul (NVar 101) nZ) nZ
      (mul_zero_right (NVar 101) (lower (NVar 101) (NVar 111))))
    (fun u gu ih =>
      trans (add (NVar 101) (mul u (NVar 101)))
        (add (NVar 101) (mul (NVar 101) u))
        (mul (NVar 101) (suc u))
        (add_second (NVar 101) (mul u (NVar 101)) (mul (NVar 101) u)
          (lower (NVar 101) (NVar 111)) ih)
        (sym (mul (NVar 101) (suc u)) (add (NVar 101) (mul (NVar 101) u))
          (mul_succ_right (NVar 101) u (NVar 111) gu)))).
Definition multiplication_commutativity := close nMulComm eq_refl.
Definition multiplication_commutativity_type := close
  (npis guarded11_2
    (nEq (mul (NVar 100) (NVar 101)) (mul (NVar 101) (NVar 100)))) eq_refl.
Definition mul_comm x y gx gy :=
  napps (NClosed multiplication_commutativity) [x;y;gx;gy].
Definition good_add11 x y gx gy :=
  napps (NClosed (DomainClosure.good_addition 11)) [x;y;gx;gy].
Definition good_mul7 x y gx gy :=
  napps (NClosed (DomainClosure.good_multiplication 7)) [x;y;gx;gy].

Definition distribution_second_body x y z gx gy gz :=
  trans (mul x (add y z)) (add (mul y x) (mul z x))
    (add (mul x y) (mul x z))
    (mul_comm x (add y z) gx (good_add11 y z gy gz))
    (trans (add (mul y x) (mul z x)) (add (mul x y) (mul z x))
      (add (mul x y) (mul x z))
      (add_first (mul y x) (mul x y) (mul z x) (mul_comm y x gy gx))
      (add_second (mul x y) (mul z x) (mul x z)
        (good_mul7 x y (lower x gx) (lower y gy)) (mul_comm z x gz gx))).
Definition nDistributeSecond := nlams guarded11_3
  (distribution_second_body (NVar 100) (NVar 101) (NVar 102)
    (NVar 110) (NVar 111) (NVar 112)).
Definition distribution_second := close nDistributeSecond eq_refl.
Definition distribution_second_type := close
  (npis guarded11_3 (nEq (mul (NVar 100) (add (NVar 101) (NVar 102)))
    (add (mul (NVar 100) (NVar 101)) (mul (NVar 100) (NVar 102))))) eq_refl.

Lemma multiplication_successor_right_typed :
  Typed ε multiplication_successor_right multiplication_successor_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_commutativity_typed :
  Typed ε multiplication_commutativity multiplication_commutativity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma distribution_second_typed : Typed ε distribution_second distribution_second_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions addition_commutativity_typed.
Print Assumptions multiplication_zero_right_typed.
Print Assumptions multiplication_one_right_typed.
Print Assumptions multiplication_successor_right_typed.
Print Assumptions multiplication_commutativity_typed.
Print Assumptions distribution_second_typed.
End SemiringLaws.
