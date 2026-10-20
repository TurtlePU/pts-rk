(** Arithmetic congruence for the exact diagonal-observer equality.
    All induction is through the supplied rank-seven certificate. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From OrderedSemiring Require Import RigCodes ObservationEquality.
Import ListNotations.

Module ArithmeticCongruence.
Import CommonCodes Core ObservationEquality.
Definition nG d := NApp (RigCodes.nGood 7) d.
Definition add x y := napps nA [x;y].
Definition mul x y := napps nM [x;y].
Definition suc x := NApp nS x.
Definition refl x := NApp (NClosed reflexivity) x.
Definition trans x y z h k := napps (NClosed transitivity) [x;y;z;h;k].
Definition succ_cong x y h := napps (NClosed successor_congruence) [x;y;h].
Definition add_first x y z h :=
  napps (NClosed addition_congruence_first) [x;y;z;h].

Definition nAddCongSecond := nlams [(100,nD);(101,nD);(102,nD);
  (110,nG (NVar 100));(111,nEq (NVar 101) (NVar 102))]
  (napps (NVar 110)
    [NLam 120 nD (nEq (add (NVar 120) (NVar 101)) (add (NVar 120) (NVar 102)));
     NVar 111;
     nlams [(120,nD);(121,nEq (add (NVar 120) (NVar 101))
                            (add (NVar 120) (NVar 102)))]
       (succ_cong (add (NVar 120) (NVar 101)) (add (NVar 120) (NVar 102)) (NVar 121))]).
Definition addition_congruence_second := close nAddCongSecond eq_refl.
Definition addition_congruence_second_type := close
  (npis [(100,nD);(101,nD);(102,nD);(110,nG (NVar 100));
          (111,nEq (NVar 101) (NVar 102))]
    (nEq (add (NVar 100) (NVar 101)) (add (NVar 100) (NVar 102)))) eq_refl.
Definition add_second x y z gx h :=
  napps (NClosed addition_congruence_second) [x;y;z;gx;h].

Definition fold_at y a := napps y [obsX;a;NVar 204].
Definition lift7 A := RigCodes.nLift 7 A.
Definition j6 := RigCodes.nJproof 6.
Definition J6 := RigCodes.nJ 6.

(** Reusable scoped builders. Their only free observation variables belong
    to observation_fields; 130--132 are local induction variables. *)
Definition fold_relation (y gy a b h : named) := napps gy
  [NLam 130 nD (lift7 (obsR (fold_at (NVar 130) a) (fold_at (NVar 130) b)));
   NLam 132 J6 h;
   nlams [(130,nD);(131,lift7 (obsR (fold_at (NVar 130) a) (fold_at (NVar 130) b)));
           (132,J6)]
     (napps (NVar 213) [fold_at (NVar 130) a;fold_at (NVar 130) b;
       NApp (NVar 131) j6]);j6].
Definition fold_fixed (y gy a h : named) := napps gy
  [NLam 130 nD (lift7 (obsR (fold_at (NVar 130) a) a));
   NLam 132 J6 (NApp (NVar 210) a);
   nlams [(130,nD);(131,lift7 (obsR (fold_at (NVar 130) a) a));(132,J6)]
     (napps (NVar 212) [obsF (fold_at (NVar 130) a);obsF a;a;
       napps (NVar 213) [fold_at (NVar 130) a;a;NApp (NVar 131) j6];h]);j6].

Definition nFoldRelation := nlams [(100,nD);(110,nG (NVar 100))]
  (nlams observation_fields
    (nlams [(240,obsX);(241,obsX);(242,obsR (NVar 240) (NVar 241))]
      (fold_relation (NVar 100) (NVar 110) (NVar 240) (NVar 241) (NVar 242)))).
Definition fold_congruence := close nFoldRelation eq_refl.
Definition fold_congruence_type := close
  (npis [(100,nD);(110,nG (NVar 100))]
    (npis observation_fields
      (npis [(240,obsX);(241,obsX);(242,obsR (NVar 240) (NVar 241))]
        (obsR (fold_at (NVar 100) (NVar 240)) (fold_at (NVar 100) (NVar 241)))))) eq_refl.
Definition nFoldFixed := nlams [(100,nD);(110,nG (NVar 100))]
  (nlams observation_fields
    (nlams [(240,obsX);(242,obsR (obsF (NVar 240)) (NVar 240))]
      (fold_fixed (NVar 100) (NVar 110) (NVar 240) (NVar 242)))).
Definition fold_fixed_point := close nFoldFixed eq_refl.
Definition fold_fixed_point_type := close
  (npis [(100,nD);(110,nG (NVar 100))]
    (npis observation_fields
      (npis [(240,obsX);(242,obsR (obsF (NVar 240)) (NVar 240))]
        (obsR (fold_at (NVar 100) (NVar 240)) (NVar 240))))) eq_refl.

(** Re-observe with the f-iterator supplied by the right factor. *)
Definition multiplication_observation_args y gy := map (fun p =>
  if Nat.eqb (fst p) 204 then NLam 240 obsX (fold_at y (NVar 240))
  else if Nat.eqb (fst p) 213 then
    nlams [(240,obsX);(241,obsX);(242,obsR (NVar 240) (NVar 241))]
      (fold_relation y gy (NVar 240) (NVar 241) (NVar 242))
  else if Nat.eqb (fst p) 215 then
    NLam 243 (NSort 1)
      (fold_fixed y gy (NApp (NVar 203) (NVar 243)) (NApp (NVar 215) (NVar 243)))
  else NVar (fst p)) observation_fields.
Definition nMulCongFirst := nlams [(100,nD);(101,nD);(102,nD);
  (110,nG (NVar 102));(111,nEq (NVar 100) (NVar 101))]
  (nlams observation_fields
    (napps (NVar 111) (multiplication_observation_args (NVar 102) (NVar 110)))).
Definition multiplication_congruence_first := close nMulCongFirst eq_refl.
Definition multiplication_congruence_first_type := close
  (npis [(100,nD);(101,nD);(102,nD);(110,nG (NVar 102));
          (111,nEq (NVar 100) (NVar 101))]
    (nEq (mul (NVar 100) (NVar 102)) (mul (NVar 101) (NVar 102)))) eq_refl.
Definition mul_first x y z gz h :=
  napps (NClosed multiplication_congruence_first) [x;y;z;gz;h].

Definition nMulCongSecond := nlams [(100,nD);(101,nD);(102,nD);
  (110,nG (NVar 100));(112,nG (NVar 102));(111,nEq (NVar 101) (NVar 102))]
  (napps (NVar 110)
    [NLam 120 nD (nEq (mul (NVar 120) (NVar 101)) (mul (NVar 120) (NVar 102)));
     refl nZ;
     nlams [(120,nD);(121,nEq (mul (NVar 120) (NVar 101))
                            (mul (NVar 120) (NVar 102)))]
       (trans (add (NVar 101) (mul (NVar 120) (NVar 101)))
              (add (NVar 102) (mul (NVar 120) (NVar 101)))
              (add (NVar 102) (mul (NVar 120) (NVar 102)))
          (add_first (NVar 101) (NVar 102) (mul (NVar 120) (NVar 101)) (NVar 111))
          (add_second (NVar 102) (mul (NVar 120) (NVar 101))
            (mul (NVar 120) (NVar 102)) (NVar 112) (NVar 121)))]).
Definition multiplication_congruence_second := close nMulCongSecond eq_refl.
Definition multiplication_congruence_second_type := close
  (npis [(100,nD);(101,nD);(102,nD);(110,nG (NVar 100));
          (112,nG (NVar 102));(111,nEq (NVar 101) (NVar 102))]
    (nEq (mul (NVar 100) (NVar 101)) (mul (NVar 100) (NVar 102)))) eq_refl.
Definition mul_second x y z gx gz h :=
  napps (NClosed multiplication_congruence_second) [x;y;z;gx;gz;h].

Lemma addition_congruence_second_typed :
  Typed ε addition_congruence_second addition_congruence_second_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma fold_congruence_typed : Typed ε fold_congruence fold_congruence_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma fold_fixed_point_typed : Typed ε fold_fixed_point fold_fixed_point_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_congruence_first_typed :
  Typed ε multiplication_congruence_first multiplication_congruence_first_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_congruence_second_typed :
  Typed ε multiplication_congruence_second multiplication_congruence_second_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions addition_congruence_second_typed.
Print Assumptions fold_congruence_typed.
Print Assumptions fold_fixed_point_typed.
Print Assumptions multiplication_congruence_first_typed.
Print Assumptions multiplication_congruence_second_typed.
End ArithmeticCongruence.
