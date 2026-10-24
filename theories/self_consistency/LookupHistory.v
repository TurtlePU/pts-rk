(** One fixed-rank relation for arbitrarily long histories of structural
    lookup segments. Its constructors do not assume the final low lookup. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalPaths.
Import ListNotations.
Module LookupHistory.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalPaths.InternalPaths.

Definition segment_rule := npis
  [(11, C); (18, C); (12, C); (19, C); (20, C);
   (16, High (NVar 11) (NVar 18) (NVar 12));
   (17, R (NVar 12) (NVar 19) (NVar 20))]
  (R (NVar 11) (Plug (NVar 18) (NVar 19)) (NVar 20)).
Definition history_fields := [(30, nArrow C (nArrow C (nArrow C (NSort 7))));
  (31, root_rule); (32, segment_rule)].
Definition history := close (nlams [(0, C); (1, C); (2, C)]
  (npis history_fields (R (NVar 0) (NVar 1) (NVar 2)))) Logic.eq_refl.
Definition Hist a p v := napps (NClosed history) [a; p; v].
Theorem history_sorted : Typed ε history
  (Arrow carrier (Arrow carrier (Arrow carrier (𝓤 10)))).
Proof. RkCheck.certify_with 512. Qed.

Definition history_root_type := close
  (npis [(0, C); (3, G (NVar 0))] (Hist (NVar 0) stop (NVar 0))) Logic.eq_refl.
Definition history_root := close
  (nlams ([(0, C); (3, G (NVar 0))] ++ history_fields)
    (napps (NVar 31) [NVar 0; NVar 3])) Logic.eq_refl.
Theorem history_root_typed : Typed ε history_root history_root_type.
Proof. RkCheck.certify_with 512. Qed.

Definition segment_arguments := [(0, C); (1, C); (2, C); (3, C); (4, C);
  (5, High (NVar 0) (NVar 1) (NVar 2));
  (6, Hist (NVar 2) (NVar 3) (NVar 4))].
Definition history_step_type := close (npis segment_arguments
  (Hist (NVar 0) (Plug (NVar 1) (NVar 3)) (NVar 4))) Logic.eq_refl.
Definition history_step := close
  (nlams (segment_arguments ++ history_fields)
    (napps (NVar 32) [NVar 0; NVar 1; NVar 2; NVar 3; NVar 4; NVar 5;
      napps (NVar 6) [NVar 30; NVar 31; NVar 32]])) Logic.eq_refl.
Theorem history_step_typed : Typed ε history_step history_step_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem history_step_sorted : Typed ε history_step_type (𝓤 11).
Proof. RkCheck.certify_with 512. Qed.

(** The invariant is the EXISTING Look_5, rank 7. Every segment uses the
    independently specified Look_6. All ranks are independent of length. *)
Definition soundness_type := close
  (npis [(0, C); (1, C); (2, C); (3, Hist (NVar 0) (NVar 1) (NVar 2))]
    (Look (NVar 0) (NVar 1) (NVar 2))) Logic.eq_refl.
Definition soundness := close
  (nlams [(0, C); (1, C); (2, C); (3, Hist (NVar 0) (NVar 1) (NVar 2))]
    (napps (NVar 3) [NClosed InternalResources.lookup;
      NClosed lookup_root; NClosed composition])) Logic.eq_refl.
Theorem soundness_type_sorted : Typed ε soundness_type (𝓤 11).
Proof. RkCheck.certify_with 512. Qed.
Theorem soundness_typed : Typed ε soundness soundness_type.
Proof. RkCheck.certify_with 512. Qed.
End LookupHistory.
