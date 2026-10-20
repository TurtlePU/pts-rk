(** Total functional graphs and the six Robinson equations under the same
    G15 guard and diagonal-observer equality. Q3 is deliberately absent. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From OrderedSemiring Require Import RigCodes DomainClosure ObservationEquality
  ArithmeticCongruence SuccessorSeparation.
Import ListNotations.

Module Graphs.
Import CommonCodes Core ObservationEquality ArithmeticCongruence.

(** Source recursion is on the second argument, so its operations reverse
    the arguments of the seed-first Church operators. *)
Definition source_add x y := add y x.
Definition source_mul x y := mul y x.
Definition nAddGraph x y z := nEq (source_add x y) z.
Definition nMulGraph x y z := nEq (source_mul x y) z.
Definition g15 x := NApp (RigCodes.nGood 15) x.
Definition raw1 := [(100,nD)].
Definition raw2 := [(100,nD);(101,nD)].
Definition guarded1 := raw1 ++ [(110,g15 (NVar 100))].
Definition guarded2 := [(100,nD);(110,g15 (NVar 100));
  (101,nD);(111,g15 (NVar 101))].
Definition lower7 x gx := napps (NClosed (RigCodes.lowering 15 7)) [x;gx].
Definition good_source_add x y gx gy :=
  napps (NClosed (DomainClosure.good_addition 15)) [y;x;gy;gx].
Definition good_source_mul x y gx gy :=
  napps (NClosed (DomainClosure.good_multiplication 15)) [y;x;gy;gx].

(** The output certificate stays inside the negative existential's
    continuation; no positive existential elimination is used. *)
Definition existence_continuation (op : named -> named -> named) (x y : named) :=
  npis [(102,nD);(112,g15 (NVar 102))]
    (nArrow (nEq (op x y) (NVar 102)) nVoid).
Definition nExistence op x y := nNeg (existence_continuation op x y).
Definition nGraphTotality (op : named -> named -> named)
    (good_op : named -> named -> named -> named -> named) :=
  nlams (guarded2 ++ [(120,existence_continuation op (NVar 100) (NVar 101))])
    (napps (NVar 120)
      [op (NVar 100) (NVar 101);
       good_op (NVar 100) (NVar 101) (NVar 110) (NVar 111);
       refl (op (NVar 100) (NVar 101))]).
Definition addition_totality := close (nGraphTotality source_add good_source_add) eq_refl.
Definition multiplication_totality := close (nGraphTotality source_mul good_source_mul) eq_refl.
Definition addition_totality_type := close
  (npis guarded2 (nExistence source_add (NVar 100) (NVar 101))) eq_refl.
Definition multiplication_totality_type := close
  (npis guarded2 (nExistence source_mul (NVar 100) (NVar 101))) eq_refl.

Definition functionality_fields op :=
  raw2 ++ [(102,nD);(103,nD);
    (120,nEq (op (NVar 100) (NVar 101)) (NVar 102));
    (121,nEq (op (NVar 100) (NVar 101)) (NVar 103))].
Definition nFunctionality op := nlams (functionality_fields op)
  (trans (NVar 102) (op (NVar 100) (NVar 101)) (NVar 103)
    (napps (NClosed symmetry) [op (NVar 100) (NVar 101);NVar 102;NVar 120])
    (NVar 121)).
Definition addition_functionality := close (nFunctionality source_add) eq_refl.
Definition multiplication_functionality := close (nFunctionality source_mul) eq_refl.
Definition addition_functionality_type := close
  (npis (functionality_fields source_add) (nEq (NVar 102) (NVar 103))) eq_refl.
Definition multiplication_functionality_type := close
  (npis (functionality_fields source_mul) (nEq (NVar 102) (NVar 103))) eq_refl.

Lemma addition_totality_typed : Typed ε addition_totality addition_totality_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_totality_typed : Typed ε multiplication_totality multiplication_totality_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_functionality_typed : Typed ε addition_functionality addition_functionality_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_functionality_typed : Typed ε multiplication_functionality multiplication_functionality_type.
Proof. RkCheck.certify_with 4096. Qed.

(** Every axiom uses G15, including successor cancellation/nonzeroness.
    Their G7 certificates are obtained by the already checked lowering map. *)
Definition q1 := close
  (nlams (guarded2 ++ [(120,nEq (suc (NVar 100)) (suc (NVar 101)))])
    (napps (NClosed SuccessorSeparation.successor_injectivity)
      [NVar 100;NVar 101;lower7 (NVar 100) (NVar 110);
       lower7 (NVar 101) (NVar 111);NVar 120])) eq_refl.
Definition q1_type := close (npis guarded2
  (nArrow (nEq (suc (NVar 100)) (suc (NVar 101))) (nEq (NVar 100) (NVar 101)))) eq_refl.
Definition q2 := close
  (nlams (guarded1 ++ [(120,nEq (suc (NVar 100)) nZ)])
    (napps (NClosed SuccessorSeparation.successor_nonzero)
      [NVar 100;lower7 (NVar 100) (NVar 110);NVar 120])) eq_refl.
Definition q2_type := close (npis guarded1 (nNeg (nEq (suc (NVar 100)) nZ))) eq_refl.

(** Q4 uses observational eta insensitivity. The remaining three displayed
    equations are beta identities; all lambda annotations are retained. *)
Definition q4 := close (nlams guarded1 (refl (NVar 100))) eq_refl.
Definition q4_type := close
  (npis guarded1 (nEq (source_add (NVar 100) nZ) (NVar 100))) eq_refl.
Definition q5 := close
  (nlams guarded2 (refl (suc (source_add (NVar 100) (NVar 101))))) eq_refl.
Definition q5_type := close
  (npis guarded2 (nEq (source_add (NVar 100) (suc (NVar 101)))
    (suc (source_add (NVar 100) (NVar 101))))) eq_refl.
Definition q6 := close (nlams guarded1 (refl nZ)) eq_refl.
Definition q6_type := close (npis guarded1 (nEq (source_mul (NVar 100) nZ) nZ)) eq_refl.
Definition q7 := close
  (nlams guarded2 (refl (source_add (source_mul (NVar 100) (NVar 101)) (NVar 100)))) eq_refl.
Definition q7_type := close
  (npis guarded2 (nEq (source_mul (NVar 100) (suc (NVar 101)))
    (source_add (source_mul (NVar 100) (NVar 101)) (NVar 100)))) eq_refl.

Lemma q1_typed : Typed ε q1 q1_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma q2_typed : Typed ε q2 q2_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma q4_typed : Typed ε q4 q4_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma q5_typed : Typed ε q5 q5_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma q6_typed : Typed ε q6 q6_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma q7_typed : Typed ε q7 q7_type.
Proof. RkCheck.certify_with 4096. Qed.

Inductive six_axiom := Q1 | Q2 | Q4 | Q5 | Q6 | Q7.
Definition axiom_type a : closed_term :=
  match a with
  | Q1 => q1_type | Q2 => q2_type | Q4 => q4_type
  | Q5 => q5_type | Q6 => q6_type | Q7 => q7_type
  end.
Definition axiom_witness a : closed_term :=
  match a with Q1 => q1 | Q2 => q2 | Q4 => q4 | Q5 => q5 | Q6 => q6 | Q7 => q7 end.
Theorem all_six_axioms_typed a :
  @typ nat RankSorts 0 ε (axiom_witness a) (axiom_type a).
Proof.
  destruct a; cbn [axiom_witness axiom_type];
    [exact q1_typed|exact q2_typed|exact q4_typed|exact q5_typed|exact q6_typed|exact q7_typed].
Qed.

Print Assumptions addition_totality_typed.
Print Assumptions multiplication_totality_typed.
Print Assumptions addition_functionality_typed.
Print Assumptions multiplication_functionality_typed.
Print Assumptions all_six_axioms_typed.
End Graphs.
