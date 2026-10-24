(** Tag-insensitive SUBTREE capacity. This is deliberately stronger than
    numerical size comparison, not a normalization-resource oracle. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalPaths LookupHistory.
Import ListNotations.
Module InternalCapacity.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalPaths.InternalPaths LookupHistory.LookupHistory.

Definition shape := close (nlams ([(0, C)] ++ fields)
  (napps (NVar 0) ([NVar 90] ++ map (fun _ => NVar 100) tags ++ [NVar 91]))) Logic.eq_refl.
Definition Sh x := NApp (NClosed shape) x.
Theorem shape_typed : Typed ε shape (Arrow carrier carrier).
Proof. RkCheck.certify_with 256. Qed.
Definition shape_guard_type := close
  (npis [(0, C); (1, G (NVar 0))] (G (Sh (NVar 0)))) Logic.eq_refl.
Definition shape_pair := nlams [(201, C); (202, C);
  (203, NApp (NVar 200) (Sh (NVar 201)));
  (204, NApp (NVar 200) (Sh (NVar 202)))]
  (napps (NVar 205) [Sh (NVar 201); Sh (NVar 202); NVar 203; NVar 204]).
Definition shape_guard := close
  (nlams ([(0, C); (1, G (NVar 0))] ++ guard_fields)
    (napps (NVar 1) ([NLam 206 C (NApp (NVar 200) (Sh (NVar 206)))] ++
      map (fun _ => NVar 300) tags ++ [shape_pair]))) Logic.eq_refl.
Theorem shape_guard_typed : Typed ε shape_guard shape_guard_type.
Proof. RkCheck.certify_with 512. Qed.

Definition capacity := close (nlams [(0, C); (1, C)]
  (Ext (Sh (NVar 0)) (Sh (NVar 1)))) Logic.eq_refl.
Definition Cap x y := napps (NClosed capacity) [x; y].
Theorem capacity_sorted : Typed ε capacity (Arrow carrier (Arrow carrier (𝓤 6))).
Proof. RkCheck.certify_with 512. Qed.
Definition reflexivity_type := close (NPi 0 C (Cap (NVar 0) (NVar 0))) Logic.eq_refl.
Definition reflexivity := close (NLam 0 C
  (NApp (NClosed extension_refl) (Sh (NVar 0)))) Logic.eq_refl.
Theorem reflexivity_typed : Typed ε reflexivity reflexivity_type.
Proof. RkCheck.certify_with 512. Qed.
Definition transitivity_type := close
  (npis [(0, C); (1, C); (2, C); (3, Cap (NVar 0) (NVar 1));
    (4, Cap (NVar 1) (NVar 2))] (Cap (NVar 0) (NVar 2))) Logic.eq_refl.
Definition transitivity := close
  (nlams [(0, C); (1, C); (2, C); (3, Cap (NVar 0) (NVar 1));
    (4, Cap (NVar 1) (NVar 2))]
    (napps (NClosed extension_trans) [Sh (NVar 0); Sh (NVar 1); Sh (NVar 2); NVar 3; NVar 4])) Logic.eq_refl.
Theorem transitivity_typed : Typed ε transitivity transitivity_type.
Proof. RkCheck.certify_with 512. Qed.

Definition shape_growth (left : bool) := nlams [(11, C); (12, C);
  (16, G (NVar (if left then 12 else 11)));
  (17, NApp (NVar 10) (Sh (NVar (if left then 11 else 12))))]
  (napps (NVar (if left then 13 else 14)) [Sh (NVar 11); Sh (NVar 12);
    napps (NClosed shape_guard) [NVar (if left then 12 else 11); NVar 16]; NVar 17]).
Definition extension_capacity_type := close
  (npis [(0, C); (1, C); (2, Ext (NVar 0) (NVar 1))]
    (Cap (NVar 0) (NVar 1))) Logic.eq_refl.
Definition extension_capacity := close
  (nlams ([(0, C); (1, C); (2, Ext (NVar 0) (NVar 1))] ++ growth_fields ++
    [(15, NApp (NVar 10) (Sh (NVar 0)))])
    (napps (NVar 2) [NLam 20 C (NApp (NVar 10) (Sh (NVar 20)));
      shape_growth true; shape_growth false; NVar 15])) Logic.eq_refl.
Theorem extension_capacity_typed : Typed ε extension_capacity extension_capacity_type.
Proof. RkCheck.certify_with 512. Qed.

Definition join_type (left : bool) := close
  (npis [(0, C); (1, C); (2, G (NVar (if left then 1 else 0)))]
    (Cap (NVar (if left then 0 else 1)) (node (NVar 0) (NVar 1))))
  (ltac:(destruct left; reflexivity)).
Definition join (left : bool) := close
  (nlams [(0, C); (1, C); (2, G (NVar (if left then 1 else 0)))]
    (napps (NClosed extension_capacity)
      [NVar (if left then 0 else 1); node (NVar 0) (NVar 1);
       napps (NClosed (if left then join_left else join_right)) [NVar 0; NVar 1; NVar 2]]))
  (ltac:(destruct left; reflexivity)).
Theorem join_typed side : Typed ε (join side) (join_type side).
Proof. destruct side; RkCheck.certify_with 512. Qed.
Definition lookup_capacity_type := close
  (npis [(0, C); (1, C); (2, C); (3, Look (NVar 0) (NVar 1) (NVar 2))]
    (Cap (NVar 2) (NVar 0))) Logic.eq_refl.
Definition lookup_capacity := close
  (nlams [(0, C); (1, C); (2, C); (3, Look (NVar 0) (NVar 1) (NVar 2))]
    (napps (NClosed extension_capacity) [NVar 2; NVar 0;
      napps (NClosed lookup_extension) [NVar 0; NVar 1; NVar 2; NVar 3]])) Logic.eq_refl.
Theorem lookup_capacity_typed : Typed ε lookup_capacity lookup_capacity_type.
Proof. RkCheck.certify_with 512. Qed.
Definition history_capacity_type := close
  (npis [(0, C); (1, C); (2, C); (3, Hist (NVar 0) (NVar 1) (NVar 2))]
    (Cap (NVar 2) (NVar 0))) Logic.eq_refl.
Definition history_capacity := close
  (nlams [(0, C); (1, C); (2, C); (3, Hist (NVar 0) (NVar 1) (NVar 2))]
    (napps (NClosed lookup_capacity) [NVar 0; NVar 1; NVar 2;
      napps (NClosed soundness) [NVar 0; NVar 1; NVar 2; NVar 3]])) Logic.eq_refl.
Theorem history_capacity_typed : Typed ε history_capacity history_capacity_type.
Proof. RkCheck.certify_with 512. Qed.
End InternalCapacity.
