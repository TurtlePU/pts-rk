(** Consumer-directed transport on arbitrary represented lookups.
    These are GENERIC modular laws, not a source soundness invariant.
    Their local predicate laws are explicit arguments, never new guards or
    assumptions about lookup functionality, constructor inversion or typing. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import InternalCarrier InternalResources
  LookupHistory.
Import ListNotations.

Module RelationalTransport.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources LookupHistory.LookupHistory.

Definition predicate_at x := NApp (NVar 10) x.
(** Exact rank 4 for the consumer predicate.  Its implication motive below
    has exact rank 5, the unchanged Look_5 elimination level. *)
Definition downward_rule (left : bool) := npis
  [(11, C); (12, C); (16, G (NVar (if left then 12 else 11)))]
  (nArrow (predicate_at (node (NVar 11) (NVar 12)))
    (predicate_at (NVar (if left then 11 else 12)))).
Definition downward_fields := [(10, nArrow C (NSort 4));
  (13, downward_rule true); (14, downward_rule false)].
Definition lookup_arguments := [(0, C); (1, C); (2, C);
  (3, Look (NVar 0) (NVar 1) (NVar 2))].
Definition history_arguments := [(0, C); (1, C); (2, C);
  (3, Hist (NVar 0) (NVar 1) (NVar 2))].

Definition downward_motive := nlams [(11, C); (18, C); (19, C)]
  (nArrow (predicate_at (NVar 11)) (predicate_at (NVar 19))).
Definition downward_root := nlams [(11, C); (16, G (NVar 11));
  (40, predicate_at (NVar 11))] (NVar 40).
Definition downward_step (left : bool) := nlams
  [(11, C); (12, C); (18, C); (19, C);
   (16, G (NVar (if left then 12 else 11)));
   (17, nArrow (predicate_at (NVar (if left then 11 else 12)))
     (predicate_at (NVar 19)));
   (40, predicate_at (node (NVar 11) (NVar 12)))]
  (NApp (NVar 17)
    (napps (NVar (if left then 13 else 14))
      [NVar 11; NVar 12; NVar 16; NVar 40])).

Definition lookup_preservation_type := close
  (npis (downward_fields ++ lookup_arguments)
    (nArrow (predicate_at (NVar 0)) (predicate_at (NVar 2)))) Logic.eq_refl.
Definition lookup_preservation := close
  (nlams (downward_fields ++ lookup_arguments ++ [(4, predicate_at (NVar 0))])
    (napps (NVar 3) [downward_motive; downward_root;
      downward_step true; downward_step false; NVar 4])) Logic.eq_refl.
Theorem lookup_preservation_type_sorted : Typed ε lookup_preservation_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.
Theorem lookup_preservation_typed : Typed ε lookup_preservation lookup_preservation_type.
Proof. RkCheck.certify_with 512. Qed.

Definition history_preservation_type := close
  (npis (downward_fields ++ history_arguments)
    (nArrow (predicate_at (NVar 0)) (predicate_at (NVar 2)))) Logic.eq_refl.
Definition history_preservation := close
  (nlams (downward_fields ++ history_arguments ++ [(4, predicate_at (NVar 0))])
    (napps (NClosed lookup_preservation)
      [NVar 10; NVar 13; NVar 14; NVar 0; NVar 1; NVar 2;
       napps (NClosed soundness) [NVar 0; NVar 1; NVar 2; NVar 3];
       NVar 4])) Logic.eq_refl.
Theorem history_preservation_type_sorted : Typed ε history_preservation_type (𝓤 11).
Proof. RkCheck.certify_with 512. Qed.
Theorem history_preservation_typed : Typed ε history_preservation history_preservation_type.
Proof. RkCheck.certify_with 512. Qed.

(** Dual negative safety for UPWARD-closed predicates.  A bad selected
    value would transport to a bad resource and contradict the supplied
    resource refutation.  No arbitrary-rank ex-falso or double-negation
    elimination is used: the output is literal Bottom. *)
Definition rejects x := nArrow (predicate_at x) (NClosed Bottom).
Definition extension_safety_type := close
  (npis (growth_fields ++ [(0, C); (1, C);
     (2, Ext (NVar 0) (NVar 1)); (3, rejects (NVar 1))])
    (rejects (NVar 0))) Logic.eq_refl.
Definition extension_safety := close
  (nlams (growth_fields ++ [(0, C); (1, C);
     (2, Ext (NVar 0) (NVar 1)); (3, rejects (NVar 1));
     (4, predicate_at (NVar 0))])
    (NApp (NVar 3) (napps (NVar 2)
      [NVar 10; NVar 13; NVar 14; NVar 4]))) Logic.eq_refl.
Theorem extension_safety_type_sorted : Typed ε extension_safety_type (𝓤 7).
Proof. RkCheck.certify_with 512. Qed.
Theorem extension_safety_typed : Typed ε extension_safety extension_safety_type.
Proof. RkCheck.certify_with 512. Qed.

Definition lookup_safety_type := close
  (npis (growth_fields ++ lookup_arguments ++ [(4, rejects (NVar 0))])
    (rejects (NVar 2))) Logic.eq_refl.
Definition lookup_safety := close
  (nlams (growth_fields ++ lookup_arguments ++ [(4, rejects (NVar 0));
     (5, predicate_at (NVar 2))])
    (napps (NClosed extension_safety)
      [NVar 10; NVar 13; NVar 14; NVar 2; NVar 0;
       napps (NClosed lookup_extension) [NVar 0; NVar 1; NVar 2; NVar 3];
       NVar 4; NVar 5])) Logic.eq_refl.
Theorem lookup_safety_type_sorted : Typed ε lookup_safety_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.
Theorem lookup_safety_typed : Typed ε lookup_safety lookup_safety_type.
Proof. RkCheck.certify_with 512. Qed.

Definition history_safety_type := close
  (npis (growth_fields ++ history_arguments ++ [(4, rejects (NVar 0))])
    (rejects (NVar 2))) Logic.eq_refl.
Definition history_safety := close
  (nlams (growth_fields ++ history_arguments ++ [(4, rejects (NVar 0));
     (5, predicate_at (NVar 2))])
    (napps (NClosed lookup_safety)
      [NVar 10; NVar 13; NVar 14; NVar 0; NVar 1; NVar 2;
       napps (NClosed soundness) [NVar 0; NVar 1; NVar 2; NVar 3];
       NVar 4; NVar 5])) Logic.eq_refl.
Theorem history_safety_type_sorted : Typed ε history_safety_type (𝓤 11).
Proof. RkCheck.certify_with 512. Qed.
Theorem history_safety_typed : Typed ε history_safety history_safety_type.
Proof. RkCheck.certify_with 512. Qed.

End RelationalTransport.
