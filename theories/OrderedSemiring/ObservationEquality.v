(** The state-indexed diagonal-observer equality of the corrected rig note.
    The nine certificates belong to the observation telescope; they are
    parameters of each observation, not global axioms of the PTS. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary.
Import ListNotations.

Module ObservationEquality.
Import CommonCodes Core.

Definition nD := NClosed Unary.Domain.
Definition nZ := NClosed Unary.zero.
Definition nS := NClosed Unary.successor.
Definition nA := NClosed Unary.addition.
Definition nM := NClosed Unary.multiplication.
Definition nVoid := NClosed Bottom.
Definition nNeg A := nArrow A nVoid.
Definition nConj A B := nNeg (nArrow A (nArrow B nVoid)).
Definition nT A B := nConj (nArrow (nNeg A) (nNeg B))
                            (nArrow (nNeg B) (nNeg A)).
Definition nTType := close
  (nlams [(320,NSort 1);(321,NSort 1)] (nT (NVar 320) (NVar 321))) eq_refl.

Definition nTRfl := NLam 320 (NSort 1)
  (NLam 330 (nArrow (nArrow (nNeg (NVar 320)) (nNeg (NVar 320)))
    (nArrow (nArrow (nNeg (NVar 320)) (nNeg (NVar 320))) nVoid))
    (napps (NVar 330) [NLam 335 (nNeg (NVar 320)) (NVar 335);
                       NLam 335 (nNeg (NVar 320)) (NVar 335)])).
Definition nTSym := nlams [(320,NSort 1);(321,NSort 1);
  (323,nT (NVar 320) (NVar 321));
  (330,nArrow (nArrow (nNeg (NVar 321)) (nNeg (NVar 320)))
    (nArrow (nArrow (nNeg (NVar 320)) (nNeg (NVar 321))) nVoid))]
  (NApp (NVar 323)
    (nlams [(331,nArrow (nNeg (NVar 320)) (nNeg (NVar 321)));
            (332,nArrow (nNeg (NVar 321)) (nNeg (NVar 320)))]
      (napps (NVar 330) [NVar 332;NVar 331]))).
Definition nTTrans := nlams [(320,NSort 1);(321,NSort 1);(322,NSort 1);
  (323,nT (NVar 320) (NVar 321));(324,nT (NVar 321) (NVar 322));
  (330,nArrow (nArrow (nNeg (NVar 320)) (nNeg (NVar 322)))
    (nArrow (nArrow (nNeg (NVar 322)) (nNeg (NVar 320))) nVoid))]
  (NApp (NVar 323)
    (nlams [(331,nArrow (nNeg (NVar 320)) (nNeg (NVar 321)));
            (332,nArrow (nNeg (NVar 321)) (nNeg (NVar 320)))]
      (NApp (NVar 324)
        (nlams [(333,nArrow (nNeg (NVar 321)) (nNeg (NVar 322)));
                (334,nArrow (nNeg (NVar 322)) (nNeg (NVar 321)))]
          (napps (NVar 330)
            [NLam 335 (nNeg (NVar 320)) (NApp (NVar 333) (NApp (NVar 331) (NVar 335)));
             NLam 335 (nNeg (NVar 322)) (NApp (NVar 332) (NApp (NVar 334) (NVar 335)))]))))).

Definition obsX := NVar 200.
Definition obsR x y := napps (NVar 201) [x;y].
Definition obsF x := NApp (NVar 204) x.
Definition obsD w k := napps (NVar 205) [w;k].
Definition obsP x := NApp (NVar 206) x.
Definition obsFold x := napps x [obsX;NVar 202;NVar 204].
Definition obsKType := nArrow (NSort 1) obsX.
Definition observation_data :=
  [(200,NSort 1); (201,nArrow obsX (nArrow obsX (NSort 5)));
   (202,obsX); (203,obsKType); (204,nArrow obsX obsX);
   (205,nArrow obsX (nArrow obsKType obsX));
   (206,nArrow obsX (NSort 1))].
Definition observation_certificates :=
  [(210,NPi 220 obsX (obsR (NVar 220) (NVar 220)));
   (211,npis [(220,obsX);(221,obsX)]
      (nArrow (obsR (NVar 220) (NVar 221)) (obsR (NVar 221) (NVar 220))));
   (212,npis [(220,obsX);(221,obsX);(222,obsX)]
      (nArrow (obsR (NVar 220) (NVar 221))
        (nArrow (obsR (NVar 221) (NVar 222)) (obsR (NVar 220) (NVar 222)))));
   (213,npis [(220,obsX);(221,obsX)]
      (nArrow (obsR (NVar 220) (NVar 221))
        (obsR (obsF (NVar 220)) (obsF (NVar 221)))));
   (214,npis [(220,obsX);(223,obsKType);(224,obsKType)]
      (nArrow (NPi 225 (NSort 1)
        (obsR (NApp (NVar 223) (NVar 225)) (NApp (NVar 224) (NVar 225))))
        (obsR (obsD (NVar 220) (NVar 223)) (obsD (NVar 220) (NVar 224)))));
   (215,NPi 225 (NSort 1)
      (obsR (obsF (NApp (NVar 203) (NVar 225))) (NApp (NVar 203) (NVar 225))));
   (216,NPi 220 obsX (obsR (obsD (NVar 220) (NVar 203)) (NVar 220)));
   (217,npis [(220,obsX);(221,obsX)]
      (obsR (obsD (NVar 220) (NLam 225 (NSort 1) (NVar 221))) (NVar 221)));
   (218,npis [(220,obsX);(221,obsX)]
      (nArrow (obsR (NVar 220) (NVar 221))
        (nT (obsP (NVar 220)) (obsP (NVar 221)))))].
Definition observation_fields := observation_data ++ observation_certificates.
Definition observation_args := map (fun p => NVar (fst p)) observation_fields.
Definition nEquality := nlams [(100,nD);(101,nD)]
  (npis observation_fields
    (nT (obsP (obsFold (NVar 100))) (obsP (obsFold (NVar 101))))).
Definition Equality := close nEquality eq_refl.
Definition nEq x y := napps (NClosed Equality) [x;y].

Definition nRefl := NLam 100 nD (nlams observation_fields
  (NApp nTRfl (obsP (obsFold (NVar 100))))).
Definition reflexivity := close nRefl eq_refl.
Definition reflexivity_type := close
  (NPi 100 nD (nEq (NVar 100) (NVar 100))) eq_refl.
Definition nSym := nlams [(100,nD);(101,nD);(110,nEq (NVar 100) (NVar 101))]
  (nlams observation_fields
    (napps nTSym [obsP (obsFold (NVar 100));obsP (obsFold (NVar 101));
      napps (NVar 110) observation_args])).
Definition symmetry := close nSym eq_refl.
Definition symmetry_type := close
  (npis [(100,nD);(101,nD)]
    (nArrow (nEq (NVar 100) (NVar 101)) (nEq (NVar 101) (NVar 100)))) eq_refl.
Definition nTrans := nlams [(100,nD);(101,nD);(102,nD);
  (110,nEq (NVar 100) (NVar 101));(111,nEq (NVar 101) (NVar 102))]
  (nlams observation_fields
    (napps nTTrans [obsP (obsFold (NVar 100));obsP (obsFold (NVar 101));
      obsP (obsFold (NVar 102)); napps (NVar 110) observation_args;
      napps (NVar 111) observation_args])).
Definition transitivity := close nTrans eq_refl.
Definition transitivity_type := close
  (npis [(100,nD);(101,nD);(102,nD)]
    (nArrow (nEq (NVar 100) (NVar 101))
      (nArrow (nEq (NVar 101) (NVar 102)) (nEq (NVar 100) (NVar 102))))) eq_refl.

Definition nStable := nlams [(100,nD);(101,nD);
  (110,nNeg (nNeg (nEq (NVar 100) (NVar 101))))]
  (nlams observation_fields
    (NLam 230 (nArrow
      (nArrow (nNeg (obsP (obsFold (NVar 100)))) (nNeg (obsP (obsFold (NVar 101)))))
      (nArrow (nArrow (nNeg (obsP (obsFold (NVar 101))))
        (nNeg (obsP (obsFold (NVar 100))))) nVoid))
      (NApp (NVar 110) (NLam 111 (nEq (NVar 100) (NVar 101))
        (NApp (napps (NVar 111) observation_args) (NVar 230)))))).
Definition stability := close nStable eq_refl.
Definition stability_type := close
  (npis [(100,nD);(101,nD)]
    (nArrow (nNeg (nNeg (nEq (NVar 100) (NVar 101))))
      (nEq (NVar 100) (NVar 101)))) eq_refl.

(** Re-observe with p composed with f. All eight other certificates persist;
    the last certificate composes f-congruence with the original p bridge. *)
Definition successor_observation_args :=
  map (fun p =>
    if Nat.eqb (fst p) 206 then NLam 220 obsX (obsP (obsF (NVar 220)))
    else if Nat.eqb (fst p) 218 then
      nlams [(220,obsX);(221,obsX);(222,obsR (NVar 220) (NVar 221))]
        (napps (NVar 218) [obsF (NVar 220);obsF (NVar 221);
          napps (NVar 213) [NVar 220;NVar 221;NVar 222]])
    else NVar (fst p)) observation_fields.
Definition nSuccCong := nlams [(100,nD);(101,nD);(110,nEq (NVar 100) (NVar 101))]
  (nlams observation_fields (napps (NVar 110) successor_observation_args)).
Definition successor_congruence := close nSuccCong eq_refl.
Definition successor_congruence_type := close
  (npis [(100,nD);(101,nD)]
    (nArrow (nEq (NVar 100) (NVar 101))
      (nEq (NApp nS (NVar 100)) (NApp nS (NVar 101))))) eq_refl.

(** Eta expansion is not a conversion rule. Applying either side to the
    observation arguments gives beta-identical terms, hence an E proof. *)
Definition nEta := NLam 100 nD (nlams [(200,NSort 1);(202,NVar 200);
  (204,nArrow (NVar 200) (NVar 200))] (obsFold (NVar 100))).
Definition eta_equality := reflexivity.
Definition eta_equality_type := close
  (NPi 100 nD (nEq (NApp nEta (NVar 100)) (NVar 100))) eq_refl.

(** Addition in its first argument changes only the seed of the observer. *)
Definition nAddCongFirst := nlams [(100,nD);(101,nD);(102,nD);
  (110,nEq (NVar 100) (NVar 101))]
  (nlams observation_fields
    (napps (NVar 110) (map (fun p =>
      if Nat.eqb (fst p) 202 then obsFold (NVar 102)
      else NVar (fst p)) observation_fields))).
Definition addition_congruence_first := close nAddCongFirst eq_refl.
Definition addition_congruence_first_type := close
  (npis [(100,nD);(101,nD);(102,nD)]
    (nArrow (nEq (NVar 100) (NVar 101))
      (nEq (napps nA [NVar 100;NVar 102]) (napps nA [NVar 101;NVar 102])))) eq_refl.

Lemma truth_equivalence_formation :
  Typed ε nTType (Arrow (𝓤 1) (Arrow (𝓤 1) (𝓤 5))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_formation :
  Typed ε Equality (Arrow Unary.Domain (Arrow Unary.Domain (𝓤 7))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma reflexivity_typed : Typed ε reflexivity reflexivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma symmetry_typed : Typed ε symmetry symmetry_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma transitivity_typed : Typed ε transitivity transitivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma stability_typed : Typed ε stability stability_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma successor_congruence_typed : Typed ε successor_congruence successor_congruence_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma eta_equality_typed : Typed ε eta_equality eta_equality_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_congruence_first_typed :
  Typed ε addition_congruence_first addition_congruence_first_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions equality_formation.
Print Assumptions reflexivity_typed.
Print Assumptions symmetry_typed.
Print Assumptions transitivity_typed.
Print Assumptions stability_typed.
Print Assumptions successor_congruence_typed.
Print Assumptions eta_equality_typed.
Print Assumptions addition_congruence_first_typed.
End ObservationEquality.
