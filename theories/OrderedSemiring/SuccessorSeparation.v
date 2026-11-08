(** Concrete separating and delayed observations for the SAME equality.
    These are supplied native terms, not additional observation axioms. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary.
From OrderedSemiring Require Import RigCodes ObservationEquality.
Import ListNotations.

Module SuccessorSeparation.
Import CommonCodes Core ObservationEquality.

Definition nTFwd := nlams [(600,NSort 1);(601,NSort 1);
  (602,nT (NVar 600) (NVar 601));(603,nNeg (NVar 600));(604,NVar 601)]
  (NApp (NVar 602)
    (nlams [(605,nArrow (nNeg (NVar 600)) (nNeg (NVar 601)));
            (606,nArrow (nNeg (NVar 601)) (nNeg (NVar 600)))]
      (napps (NVar 605) [NVar 603;NVar 604]))).
Definition nTBwd := nlams [(600,NSort 1);(601,NSort 1);
  (602,nT (NVar 600) (NVar 601));(603,nNeg (NVar 601));(604,NVar 600)]
  (NApp (NVar 602)
    (nlams [(605,nArrow (nNeg (NVar 600)) (nNeg (NVar 601)));
            (606,nArrow (nNeg (NVar 601)) (nNeg (NVar 600)))]
      (napps (NVar 606) [NVar 603;NVar 604]))).

Definition sepX := nArrow (NSort 1) (nArrow (NSort 1) (NSort 1)).
Definition sepValue v a b := napps v [a;b].
Definition sepR v w := npis [(602,NSort 1);(603,NSort 1)]
  (nT (sepValue v (NVar 602) (NVar 603))
      (sepValue w (NVar 602) (NVar 603))).
Definition sepRelation := nlams [(600,sepX);(601,sepX)] (sepR (NVar 600) (NVar 601)).
Definition sepZero := nlams [(602,NSort 1);(603,NSort 1)] (NVar 602).
Definition sepK := nlams [(604,NSort 1);(602,NSort 1);(603,NSort 1)] (NVar 604).
Definition sepF := nlams [(600,sepX);(602,NSort 1);(603,NSort 1)]
  (sepValue (NVar 600) (NVar 603) (NVar 603)).
Definition sepD := nlams [(600,sepX);(601,nArrow (NSort 1) sepX);
  (602,NSort 1);(603,NSort 1)]
  (napps (NVar 601) [sepValue (NVar 600) (NVar 602) (NVar 603);NVar 602;NVar 603]).
Definition sepP := NLam 600 sepX (sepValue (NVar 600) (NClosed Top) nVoid).

Definition sepRefl := nlams [(600,sepX);(602,NSort 1);(603,NSort 1)]
  (NApp nTRfl (sepValue (NVar 600) (NVar 602) (NVar 603))).
Definition sepSym := nlams [(600,sepX);(601,sepX);(604,sepR (NVar 600) (NVar 601));
  (602,NSort 1);(603,NSort 1)]
  (napps nTSym [sepValue (NVar 600) (NVar 602) (NVar 603);
    sepValue (NVar 601) (NVar 602) (NVar 603);napps (NVar 604) [NVar 602;NVar 603]]).
Definition sepTrans := nlams [(600,sepX);(601,sepX);(607,sepX);
  (604,sepR (NVar 600) (NVar 601));(605,sepR (NVar 601) (NVar 607));
  (602,NSort 1);(603,NSort 1)]
  (napps nTTrans [sepValue (NVar 600) (NVar 602) (NVar 603);
    sepValue (NVar 601) (NVar 602) (NVar 603);
    sepValue (NVar 607) (NVar 602) (NVar 603);
    napps (NVar 604) [NVar 602;NVar 603];napps (NVar 605) [NVar 602;NVar 603]]).
Definition sepFCong := nlams [(600,sepX);(601,sepX);(604,sepR (NVar 600) (NVar 601));
  (602,NSort 1);(603,NSort 1)] (napps (NVar 604) [NVar 603;NVar 603]).
Definition sepDCong := nlams [(600,sepX);(601,nArrow (NSort 1) sepX);
  (607,nArrow (NSort 1) sepX);
  (604,NPi 608 (NSort 1) (sepR (NApp (NVar 601) (NVar 608)) (NApp (NVar 607) (NVar 608))));
  (602,NSort 1);(603,NSort 1)]
  (napps (NVar 604) [sepValue (NVar 600) (NVar 602) (NVar 603);NVar 602;NVar 603]).
Definition sepFK := nlams [(604,NSort 1);(602,NSort 1);(603,NSort 1)]
  (NApp nTRfl (NVar 604)).
Definition sepDK := sepRefl.
Definition sepDC := nlams [(600,sepX);(601,sepX);(602,NSort 1);(603,NSort 1)]
  (NApp nTRfl (sepValue (NVar 601) (NVar 602) (NVar 603))).
Definition sepPBridge := nlams [(600,sepX);(601,sepX);(604,sepR (NVar 600) (NVar 601))]
  (napps (NVar 604) [NClosed Top;nVoid]).
Definition separating_args :=
  [sepX;sepRelation;sepZero;sepK;sepF;sepD;sepP;
   sepRefl;sepSym;sepTrans;sepFCong;sepDCong;sepFK;sepDK;sepDC;sepPBridge].
Definition sepFold n := napps n [sepX;sepZero;sepF].
Definition sepOut n := NApp sepP (sepFold n).

(** One native application checks the entire data-and-certificate telescope. *)
Definition nSeparateSpecialize := nlams [(100,nD);(101,nD);(110,nEq (NVar 100) (NVar 101))]
  (napps (NVar 110) separating_args).
Definition separating_specialization := close nSeparateSpecialize eq_refl.
Definition separating_specialization_type := close
  (npis [(100,nD);(101,nD)] (nArrow (nEq (NVar 100) (NVar 101))
    (nT (sepOut (NVar 100)) (sepOut (NVar 101))))) eq_refl.

Definition nonzero_test n := nT (sepOut (NApp nS n)) nVoid.
Definition nSuccessorZeroTest := nlams [(100,nD);(110,NApp (RigCodes.nGood 7) (NVar 100))]
  (NApp
    (napps (NVar 110)
      [NLam 640 nD (RigCodes.nLift 7 (nonzero_test (NVar 640)));
       NLam 642 (RigCodes.nJ 6) (NApp nTRfl nVoid);
       nlams [(640,nD);(641,RigCodes.nLift 7 (nonzero_test (NVar 640)));
              (642,RigCodes.nJ 6)] (NApp (NVar 641) (NVar 642))])
    (RigCodes.nJproof 6)).
Definition successor_zero_test := close nSuccessorZeroTest eq_refl.
Definition successor_zero_test_type := close
  (NPi 100 nD (nArrow (NApp (RigCodes.nGood 7) (NVar 100))
    (nonzero_test (NVar 100)))) eq_refl.
Definition nSuccessorNonzero := nlams [(100,nD);
  (110,NApp (RigCodes.nGood 7) (NVar 100));(120,nEq (NApp nS (NVar 100)) nZ)]
  (napps nTFwd [sepOut (NApp nS (NVar 100));NClosed Top;
    napps (NVar 120) separating_args;
    napps nTBwd [sepOut (NApp nS (NVar 100));nVoid;
      napps nSuccessorZeroTest [NVar 100;NVar 110];NLam 650 nVoid (NVar 650)];
    NClosed top_proof]).
Definition successor_nonzero := close nSuccessorNonzero eq_refl.
Definition successor_nonzero_type := close
  (NPi 100 nD (nArrow (NApp (RigCodes.nGood 7) (NVar 100))
    (nArrow (nEq (NApp nS (NVar 100)) nZ) nVoid))) eq_refl.

Lemma separating_specialization_typed :
  Typed ε separating_specialization separating_specialization_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma successor_zero_test_typed : Typed ε successor_zero_test successor_zero_test_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma successor_nonzero_typed : Typed ε successor_nonzero successor_nonzero_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions separating_specialization_typed.
Print Assumptions successor_zero_test_typed.
Print Assumptions successor_nonzero_typed.

(** The delayed observer stays at carrier rank one because U : U_0.
    Each diagonal is indexed by its supplied state. *)
Definition delayedX := nArrow (NSort 1) obsX.
Definition delayedKType := nArrow (NSort 1) delayedX.
Definition delayedConst v := NLam 727 (NSort 1) v.
Definition delayedR v w := NPi 725 (NSort 1)
  (obsR (NApp v (NVar 725)) (NApp w (NVar 725))).
Definition delayedRelation := nlams [(700,delayedX);(701,delayedX)]
  (delayedR (NVar 700) (NVar 701)).
Definition delayedK := NLam 704 (NSort 1)
  (delayedConst (NApp (NVar 203) (NVar 704))).
Definition delayedF := NLam 700 delayedX
  (delayedConst (obsD (NVar 202)
    (NLam 726 (NSort 1) (obsF (NApp (NVar 700) (NVar 726)))))).
Definition delayedD := nlams [(700,delayedX);(701,delayedKType);(725,NSort 1)]
  (obsD (NApp (NVar 700) (NVar 725))
    (NLam 726 (NSort 1) (napps (NVar 701) [NVar 726;NVar 725]))).
Definition delayedP := NLam 700 delayedX (obsP (NApp (NVar 700) (NClosed Top))).
Definition delayedRefl := nlams [(700,delayedX);(725,NSort 1)]
  (NApp (NVar 210) (NApp (NVar 700) (NVar 725))).
Definition delayedSym := nlams [(700,delayedX);(701,delayedX);
  (710,delayedR (NVar 700) (NVar 701));(725,NSort 1)]
  (napps (NVar 211) [NApp (NVar 700) (NVar 725);NApp (NVar 701) (NVar 725);
    NApp (NVar 710) (NVar 725)]).
Definition delayedTrans := nlams [(700,delayedX);(701,delayedX);(702,delayedX);
  (710,delayedR (NVar 700) (NVar 701));(711,delayedR (NVar 701) (NVar 702));
  (725,NSort 1)]
  (napps (NVar 212) [NApp (NVar 700) (NVar 725);NApp (NVar 701) (NVar 725);
    NApp (NVar 702) (NVar 725);NApp (NVar 710) (NVar 725);NApp (NVar 711) (NVar 725)]).
Definition delayedFCong := nlams [(700,delayedX);(701,delayedX);
  (710,delayedR (NVar 700) (NVar 701));(725,NSort 1)]
  (napps (NVar 214) [NVar 202;
    NLam 726 (NSort 1) (obsF (NApp (NVar 700) (NVar 726)));
    NLam 726 (NSort 1) (obsF (NApp (NVar 701) (NVar 726)));
    NLam 726 (NSort 1) (napps (NVar 213)
      [NApp (NVar 700) (NVar 726);NApp (NVar 701) (NVar 726);NApp (NVar 710) (NVar 726)])]).
Definition delayedDCong := nlams [(700,delayedX);(701,delayedKType);(702,delayedKType);
  (710,NPi 726 (NSort 1)
    (delayedR (NApp (NVar 701) (NVar 726)) (NApp (NVar 702) (NVar 726))));
  (725,NSort 1)]
  (napps (NVar 214) [NApp (NVar 700) (NVar 725);
    NLam 726 (NSort 1) (napps (NVar 701) [NVar 726;NVar 725]);
    NLam 726 (NSort 1) (napps (NVar 702) [NVar 726;NVar 725]);
    NLam 726 (NSort 1) (napps (NVar 710) [NVar 726;NVar 725])]).
Definition delayedFK := nlams [(704,NSort 1);(725,NSort 1)]
  (napps (NVar 212)
    [obsD (NVar 202) (delayedConst (obsF (NApp (NVar 203) (NVar 704))));
     obsF (NApp (NVar 203) (NVar 704));NApp (NVar 203) (NVar 704);
     napps (NVar 217) [NVar 202;obsF (NApp (NVar 203) (NVar 704))];
     NApp (NVar 215) (NVar 704)]).
(** The pointwise eta expansion of k is compared by d-congruence and
    reflexivity before applying d_k. It is never converted by eta. *)
Definition delayedDK := nlams [(700,delayedX);(725,NSort 1)]
  (napps (NVar 212)
    [obsD (NApp (NVar 700) (NVar 725))
       (NLam 726 (NSort 1) (NApp (NVar 203) (NVar 726)));
     obsD (NApp (NVar 700) (NVar 725)) (NVar 203);NApp (NVar 700) (NVar 725);
     napps (NVar 214) [NApp (NVar 700) (NVar 725);
       NLam 726 (NSort 1) (NApp (NVar 203) (NVar 726));NVar 203;
       NLam 726 (NSort 1) (NApp (NVar 210) (NApp (NVar 203) (NVar 726)))];
     NApp (NVar 216) (NApp (NVar 700) (NVar 725))]).
Definition delayedDC := nlams [(700,delayedX);(701,delayedX);(725,NSort 1)]
  (napps (NVar 217) [NApp (NVar 700) (NVar 725);NApp (NVar 701) (NVar 725)]).
Definition delayedPBridge := nlams [(700,delayedX);(701,delayedX);
  (710,delayedR (NVar 700) (NVar 701))]
  (napps (NVar 218) [NApp (NVar 700) (NClosed Top);NApp (NVar 701) (NClosed Top);
    NApp (NVar 710) (NClosed Top)]).
Definition delayed_args :=
  [delayedX;delayedRelation;NVar 203;delayedK;delayedF;delayedD;delayedP;
   delayedRefl;delayedSym;delayedTrans;delayedFCong;delayedDCong;
   delayedFK;delayedDK;delayedDC;delayedPBridge].
Definition delayedFold n := napps n [delayedX;NVar 203;delayedF].
Definition delayedOut n := NApp delayedP (delayedFold n).
Definition nDelayedSpecialize := nlams [(100,nD);(101,nD);(110,nEq (NVar 100) (NVar 101))]
  (nlams observation_fields (napps (NVar 110) delayed_args)).
Definition delayed_specialization := close nDelayedSpecialize eq_refl.
Definition delayed_specialization_type := close
  (npis [(100,nD);(101,nD)] (nArrow (nEq (NVar 100) (NVar 101))
    (npis observation_fields (nT (delayedOut (NVar 100)) (delayedOut (NVar 101)))))) eq_refl.

Lemma delayed_specialization_typed : Typed ε delayed_specialization delayed_specialization_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition simulation_at n := NPi 725 (NSort 1)
  (obsR (NApp (delayedFold (NApp nS n)) (NVar 725)) (obsFold n)).
Definition simulation_zero := NLam 725 (NSort 1)
  (napps (NVar 212)
    [obsD (NVar 202) (NLam 726 (NSort 1) (obsF (NApp (NVar 203) (NVar 726))));
     obsD (NVar 202) (NVar 203);NVar 202;
     napps (NVar 214) [NVar 202;
       NLam 726 (NSort 1) (obsF (NApp (NVar 203) (NVar 726)));NVar 203;
       NLam 726 (NSort 1) (NApp (NVar 215) (NVar 726))];
     NApp (NVar 216) (NVar 202)]).
Definition simulation_step := nlams [(640,nD);
  (641,RigCodes.nLift 7 (simulation_at (NVar 640)));(642,RigCodes.nJ 6);(725,NSort 1)]
  (napps (NVar 212)
    [obsD (NVar 202) (NLam 726 (NSort 1)
       (obsF (NApp (delayedFold (NApp nS (NVar 640))) (NVar 726))));
     obsD (NVar 202) (delayedConst (obsF (obsFold (NVar 640))));
     obsF (obsFold (NVar 640));
     napps (NVar 214) [NVar 202;
       NLam 726 (NSort 1) (obsF (NApp (delayedFold (NApp nS (NVar 640))) (NVar 726)));
       delayedConst (obsF (obsFold (NVar 640)));
       NLam 726 (NSort 1) (napps (NVar 213)
         [NApp (delayedFold (NApp nS (NVar 640))) (NVar 726);obsFold (NVar 640);
          napps (NVar 641) [NVar 642;NVar 726]])];
     napps (NVar 217) [NVar 202;obsF (obsFold (NVar 640))]]).
Definition nSimulation := nlams [(100,nD);(110,NApp (RigCodes.nGood 7) (NVar 100))]
  (nlams observation_fields
    (NApp (napps (NVar 110)
      [NLam 640 nD (RigCodes.nLift 7 (simulation_at (NVar 640)));
       NLam 642 (RigCodes.nJ 6) simulation_zero;simulation_step]) (RigCodes.nJproof 6))).
Definition simulation := close nSimulation eq_refl.
Definition simulation_type := close
  (npis ([(100,nD);(110,NApp (RigCodes.nGood 7) (NVar 100))] ++ observation_fields)
    (simulation_at (NVar 100))) eq_refl.
Lemma simulation_typed : Typed ε simulation simulation_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition nAlpha := nlams [(100,nD);(110,NApp (RigCodes.nGood 7) (NVar 100))]
  (nlams observation_fields
    (napps (NVar 218)
      [NApp (delayedFold (NApp nS (NVar 100))) (NClosed Top);obsFold (NVar 100);
       napps nSimulation ([NVar 100;NVar 110] ++ observation_args ++ [NClosed Top])])).
Definition alpha_at n g := napps nAlpha ([n;g] ++ observation_args).
Definition nSuccessorInjectivity := nlams [(100,nD);(101,nD);
  (110,NApp (RigCodes.nGood 7) (NVar 100));(111,NApp (RigCodes.nGood 7) (NVar 101));
  (120,nEq (NApp nS (NVar 100)) (NApp nS (NVar 101)))]
  (nlams observation_fields
    (napps nTTrans [obsP (obsFold (NVar 100));delayedOut (NApp nS (NVar 100));obsP (obsFold (NVar 101));
      napps nTSym [delayedOut (NApp nS (NVar 100));obsP (obsFold (NVar 100));
        alpha_at (NVar 100) (NVar 110)];
      napps nTTrans [delayedOut (NApp nS (NVar 100));delayedOut (NApp nS (NVar 101));obsP (obsFold (NVar 101));
        napps (NVar 120) delayed_args;alpha_at (NVar 101) (NVar 111)]])).
Definition successor_injectivity := close nSuccessorInjectivity eq_refl.
Definition successor_injectivity_type := close
  (npis [(100,nD);(101,nD)]
    (nArrow (NApp (RigCodes.nGood 7) (NVar 100))
      (nArrow (NApp (RigCodes.nGood 7) (NVar 101))
        (nArrow (nEq (NApp nS (NVar 100)) (NApp nS (NVar 101)))
          (nEq (NVar 100) (NVar 101)))))) eq_refl.
Lemma successor_injectivity_typed : Typed ε successor_injectivity successor_injectivity_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions delayed_specialization_typed.
Print Assumptions simulation_typed.
Print Assumptions successor_injectivity_typed.
End SuccessorSeparation.
