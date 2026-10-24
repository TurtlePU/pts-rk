(** A concrete negative consumer of resource lookup.  Absence means that
    one independently specified seed cannot extend into a resource; it is
    NOT source rejection, normalization or consistency.  Propagation uses
    transitivity, not unique lookup results or matching-constructor inversion. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources ResourceSeparation LookupHistory.
Import ListNotations.
Module OccurrenceSafety.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources ResourceSeparation.ResourceSeparation
  LookupHistory.LookupHistory.

Definition absent := close (nlams [(0, C); (1, C)]
  (nArrow (Ext (NVar 0) (NVar 1)) no)) Logic.eq_refl.
Definition Absent seed resource := napps (NClosed absent) [seed; resource].
Theorem absent_sorted : Typed ε absent (Arrow carrier (Arrow carrier (𝓤 7))).
Proof. RkCheck.certify_with 512. Qed.

Definition extension_arguments := [(0, C); (1, C); (2, C);
  (3, Ext (NVar 1) (NVar 2)); (4, Absent (NVar 0) (NVar 2))].
Definition extension_safety_type := close (npis extension_arguments
  (Absent (NVar 0) (NVar 1))) Logic.eq_refl.
Definition extension_safety := close
  (nlams (extension_arguments ++ [(5, Ext (NVar 0) (NVar 1))])
    (NApp (NVar 4) (napps (NClosed extension_trans)
      [NVar 0; NVar 1; NVar 2; NVar 5; NVar 3]))) Logic.eq_refl.
Theorem extension_safety_type_sorted : Typed ε extension_safety_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.
Theorem extension_safety_typed : Typed ε extension_safety extension_safety_type.
Proof. RkCheck.certify_with 512. Qed.

Definition lookup_arguments := [(0, C); (1, C); (2, C); (3, C);
  (4, Look (NVar 1) (NVar 2) (NVar 3)); (5, Absent (NVar 0) (NVar 1))].
Definition lookup_safety_type := close (npis lookup_arguments
  (Absent (NVar 0) (NVar 3))) Logic.eq_refl.
Definition lookup_safety := close (nlams lookup_arguments
  (napps (NClosed extension_safety) [NVar 0; NVar 3; NVar 1;
    napps (NClosed lookup_extension) [NVar 1; NVar 2; NVar 3; NVar 4]; NVar 5])) Logic.eq_refl.
Theorem lookup_safety_type_sorted : Typed ε lookup_safety_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.
Theorem lookup_safety_typed : Typed ε lookup_safety lookup_safety_type.
Proof. RkCheck.certify_with 512. Qed.

Definition history_arguments := [(0, C); (1, C); (2, C); (3, C);
  (4, Hist (NVar 1) (NVar 2) (NVar 3)); (5, Absent (NVar 0) (NVar 1))].
Definition history_safety_type := close (npis history_arguments
  (Absent (NVar 0) (NVar 3))) Logic.eq_refl.
Definition history_safety := close (nlams history_arguments
  (napps (NClosed lookup_safety) [NVar 0; NVar 1; NVar 2; NVar 3;
    napps (NClosed soundness) [NVar 1; NVar 2; NVar 3; NVar 4]; NVar 5])) Logic.eq_refl.
Theorem history_safety_type_sorted : Typed ε history_safety_type (𝓤 11).
Proof. RkCheck.certify_with 512. Qed.
Theorem history_safety_typed : Typed ε history_safety history_safety_type.
Proof. RkCheck.certify_with 512. Qed.

(** Closed, nonvacuous base instances.  Stop is the existing type-valued
    observation: Top at NZero, Bottom at every other leaf and every pair.
    A positive inhabited rank-3 padding type provides an exact rank-4
    extension motive; no arbitrary-rank ex-falso is needed. *)
Definition Unit3 := nArrow C yes.
Definition unit3 := NLam 80 C yes_proof.
Definition NotStop x := nArrow (stop_test x) no.
Definition avoids_stop x := nArrow Unit3 (NotStop x).
Definition avoids_growth (left : bool) := nlams
  [(11, C); (12, C); (16, G (NVar (if left then 12 else 11)));
   (17, avoids_stop (NVar (if left then 11 else 12)));
   (40, Unit3); (41, no)] (NVar 41).
Definition separate_arguments := [(0, C); (1, C);
  (2, Ext (NVar 0) (NVar 1)); (3, NotStop (NVar 0)); (4, stop_test (NVar 1))].
Definition stop_separation_type := close (npis separate_arguments no) Logic.eq_refl.
Definition stop_separation := close (nlams separate_arguments
  (napps (NVar 2) [NLam 20 C (avoids_stop (NVar 20));
    avoids_growth true; avoids_growth false;
    NLam 40 Unit3 (NVar 3); unit3; NVar 4])) Logic.eq_refl.
Theorem stop_separation_type_sorted : Typed ε stop_separation_type (𝓤 7).
Proof. RkCheck.certify_with 512. Qed.
Theorem stop_separation_typed : Typed ε stop_separation stop_separation_type.
Proof. RkCheck.certify_with 512. Qed.

Definition stop_absence_type := close
  (npis [(0, C); (1, NotStop (NVar 0))] (Absent (NVar 0) stop)) Logic.eq_refl.
Definition stop_absence := close
  (nlams [(0, C); (1, NotStop (NVar 0)); (2, Ext (NVar 0) stop)]
    (napps (NClosed stop_separation) [NVar 0; stop; NVar 2; NVar 1; yes_proof])) Logic.eq_refl.
Theorem stop_absence_typed : Typed ε stop_absence stop_absence_type.
Proof. RkCheck.certify_with 512. Qed.

Definition pair_absence_type := close
  (npis [(0, C); (1, C)] (Absent (node (NVar 0) (NVar 1)) stop)) Logic.eq_refl.
Definition pair_absence := close (nlams [(0, C); (1, C)]
  (napps (NClosed stop_absence)
    [node (NVar 0) (NVar 1); NLam 41 no (NVar 41)])) Logic.eq_refl.
Theorem pair_absence_typed : Typed ε pair_absence pair_absence_type.
Proof. RkCheck.certify_with 512. Qed.

Definition atom_absence_type t := close (Absent (NClosed (atom t)) stop) Logic.eq_refl.
Definition atom_absence t := close (napps (NClosed stop_absence)
  [NClosed (atom t); NLam 41 no (NVar 41)]) Logic.eq_refl.
Theorem nonzero_atom_absence_typed t : t <> NZero ->
  Typed ε (atom_absence t) (atom_absence_type t).
Proof. destruct t; intro H; try contradiction; RkCheck.certify_with 512. Qed.
End OccurrenceSafety.
