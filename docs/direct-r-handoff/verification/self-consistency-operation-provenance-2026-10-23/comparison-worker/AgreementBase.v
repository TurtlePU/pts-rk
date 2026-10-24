From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From PTSrk.SelfConsistency Require Import InternalComparisonGraph.
Import ListNotations.
Import CommonCodes Core InternalComparisonGraph.InternalComparisonGraph.
Definition agree_motive := nlams [(201,C);(202,C);(203,Zip (NVar 201) (NVar 202));(204,B)]
  (Same (Compare (NVar 201) (NVar 202) (NVar 203)) (NVar 204)).
Definition agree_atom t := nlams [(201,C);(600,nArrow B (NSort 1));
  (601,NApp (NVar 600) (Compare (NClosed (IC.atom t)) (NVar 201) (AtomZip t (NVar 201))))]
  (NVar 601).
Definition agree_pair_atom t := nlams [(201,C);(202,C);(600,nArrow B (NSort 1));
  (601,NApp (NVar 600) (Compare (Pair (NVar 201) (NVar 202)) (NClosed (IC.atom t))
    (PairAtomZip t (NVar 201) (NVar 202))))] (NVar 601).
Definition agree_pair := nlams (pair_args ++
  [(209,Same (Compare (NVar 201) (NVar 203) (NVar 205)) (NVar 207));
   (210,Same (Compare (NVar 202) (NVar 204) (NVar 206)) (NVar 208));
   (600,nArrow B (NSort 1));
   (601,NApp (NVar 600) (Compare (Pair (NVar 201) (NVar 202)) (Pair (NVar 203) (NVar 204))
     (PairZip (NVar 201) (NVar 202) (NVar 203) (NVar 204) (NVar 205) (NVar 206))))])
   (napps (NVar 210)
    [NLam 602 B (NApp (NVar 600) (And (NVar 207) (NVar 602)));
     napps (NVar 209)
      [NLam 602 B (NApp (NVar 600)
        (And (NVar 602) (Compare (NVar 202) (NVar 204) (NVar 206)))); NVar 601]]).
Definition agree_args := indices ++[(4,Trace (NVar 0) (NVar 1) (NVar 2) (NVar 3))].
Definition agreement_type := close (npis agree_args
  (Same (Compare (NVar 0) (NVar 1) (NVar 2)) (NVar 3))) eq_refl.
Definition agreement := close (nlams agree_args
  (napps (NVar 4) ([agree_motive] ++map agree_atom IC.tags ++ map agree_pair_atom IC.tags ++[agree_pair]))) eq_refl.
Theorem agreement_type_sorted : Typed ε agreement_type (𝓤 7).
Proof. RkCheck.certify_with 2048. Qed.
