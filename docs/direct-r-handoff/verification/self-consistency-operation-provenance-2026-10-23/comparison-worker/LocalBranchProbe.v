From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From PTSrk.SelfConsistency Require Import InternalComparisonGraph AgreementBase.
Import ListNotations CommonCodes Core InternalComparisonGraph.InternalComparisonGraph.
Definition atom_agreement t := close (agree_atom t) (ltac:(destruct t; reflexivity)).
Definition atom_agreement_type t := close (NPi 201 C
  (Same (Compare (NClosed (IC.atom t)) (NVar 201) (AtomZip t (NVar 201))) (Test t (NVar 201))))
  (ltac:(destruct t; reflexivity)).
Lemma atom_agreement_typed t : Typed ε (atom_agreement t) (atom_agreement_type t).
Proof. destruct t; RkCheck.certify_with 1024. Qed.
Definition pair_atom_agreement t := close (agree_pair_atom t) (ltac:(destruct t; reflexivity)).
Definition pair_atom_agreement_type t := close (npis [(201,C);(202,C)]
  (Same (Compare (Pair (NVar 201) (NVar 202)) (NClosed (IC.atom t))
    (PairAtomZip t (NVar 201) (NVar 202))) (NClosed (GT.point false))))
  (ltac:(destruct t; reflexivity)).
Lemma pair_atom_agreement_typed t : Typed ε (pair_atom_agreement t) (pair_atom_agreement_type t).
Proof. destruct t; RkCheck.certify_with 1024. Qed.
Definition pair_agreement := close agree_pair eq_refl.
Definition pair_agreement_type := close (npis (pair_args++
  [(209,Same (Compare (NVar 201) (NVar 203) (NVar 205)) (NVar 207));
   (210,Same (Compare (NVar 202) (NVar 204) (NVar 206)) (NVar 208))])
  (Same (Compare (Pair (NVar 201) (NVar 202)) (Pair (NVar 203) (NVar 204))
     (PairZip (NVar 201) (NVar 202) (NVar 203) (NVar 204) (NVar 205) (NVar 206)))
    (And (NVar 207) (NVar 208)))) eq_refl.
Lemma pair_agreement_typed : Typed ε pair_agreement pair_agreement_type.
Proof. RkCheck.certify_with 2048. Qed.
