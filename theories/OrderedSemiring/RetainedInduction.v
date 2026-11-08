(** Lemma 2 of the supplied ordered-rig note: induction retaining a
    lower certificate. Each public witness concludes original PTS typing.
    Stability, zero and step are bound inputs, not new global assumptions. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck.
From OrderedSemiring Require Import RigCodes.
Import ListNotations.

Module RetainedInduction.
Import CommonCodes Core RigCodes.

Definition value u := NApp (NVar 100) u.
Definition lower u := NApp (nGood 7) u.
Definition invariant u := conj (lower u) (value u).
Definition handler u := nArrow (lower u) (nArrow (value u) bot).
Definition stable_family := NPi 110 nDomain
  (nArrow (neg (neg (value (NVar 110)))) (value (NVar 110))).
Definition guarded_step := NPi 110 nDomain
  (nArrow (lower (NVar 110))
    (nArrow (value (NVar 110)) (value (NApp nSucc (NVar 110))))).
Definition fields rank :=
  [(100,nArrow nDomain (NSort rank));
   (101,stable_family); (102,value nZero); (103,guarded_step);
   (104,nDomain); (105,NApp (nGood 11) (NVar 104))].

Definition invariant_zero := NLam 112 (handler nZero)
  (napps (NVar 112) [nGoodZero 7;NVar 102]).
Definition invariant_successor :=
  nlams [(110,nDomain); (111,invariant (NVar 110));
    (112,handler (NApp nSucc (NVar 110)))]
    (NApp (NVar 111)
      (nlams [(113,lower (NVar 110)); (114,value (NVar 110))]
        (napps (NVar 112)
          [napps (nGoodSucc 7) [NVar 110;NVar 113];
           napps (NVar 103) [NVar 110;NVar 113;NVar 114]]))).
Definition nRetainedInduction rank := nlams (fields rank)
  (napps (NVar 101)
    [NVar 104;
     NLam 115 (neg (value (NVar 104)))
       (napps (NVar 105)
         [NLam 110 nDomain (invariant (NVar 110));
          invariant_zero; invariant_successor;
          nlams [(113,lower (NVar 104)); (114,value (NVar 104))]
            (NApp (NVar 115) (NVar 114))])]).
Definition nRetainedInductionType rank :=
  npis (fields rank) (value (NVar 104)).

Definition rank7_proof := close (nRetainedInduction 7) eq_refl.
Definition rank7_type := close (nRetainedInductionType 7) eq_refl.
Definition rank8_proof := close (nRetainedInduction 8) eq_refl.
Definition rank8_type := close (nRetainedInductionType 8) eq_refl.
Definition rank9_proof := close (nRetainedInduction 9) eq_refl.
Definition rank9_type := close (nRetainedInductionType 9) eq_refl.

Theorem rank7_typed : Typed ε rank7_proof rank7_type.
Proof. RkCheck.certify_with 4096. Qed.
Theorem rank8_typed : Typed ε rank8_proof rank8_type.
Proof. RkCheck.certify_with 4096. Qed.
Theorem rank9_typed : Typed ε rank9_proof rank9_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions rank7_typed.
Print Assumptions rank8_typed.
Print Assumptions rank9_typed.
End RetainedInduction.
