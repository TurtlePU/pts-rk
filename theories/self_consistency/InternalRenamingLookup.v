(** Binder-indexed lookup for one FIXED relational renaming environment.
    The depth and target bound are explicit binary codes.  No output Index
    conclusion occurs in a rule; all-output boundedness is a proved fold.
    A bounded source-index shift is supplied as an independent instance. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalBinary InternalScope.
Import ListNotations.

Module InternalRenamingLookup.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalBinary.InternalBinary
  InternalScope.InternalScope.

Definition FType := nArrow C (nArrow C (NSort 12)).
Definition FBound base f := npis [(10, C); (11, C);
  (12, napps f [NVar 10; NVar 11])] (Index base (NVar 11)).
Definition LR n k i j := napps (NVar 70) [n; k; i; j].
Definition base_rule := npis [(12, C); (13, C);
  (18, napps (NVar 0) [NVar 12; NVar 13])]
  (LR (NVar 1) stop (NVar 12) (NVar 13)).
Definition zero_arguments := [(10, C); (14, C); (11, C); (15, C);
  (20, Succ (NVar 10) (NVar 14)); (21, Succ (NVar 11) (NVar 15))].
Definition zero_rule := npis zero_arguments
  (LR (NVar 14) (NVar 15) stop stop).
Definition step_codes := [(10, C); (11, C); (12, C); (13, C);
  (14, C); (15, C); (16, C); (17, C)].
Definition step_edges := [(20, Succ (NVar 10) (NVar 14));
  (21, Succ (NVar 11) (NVar 15)); (22, Succ (NVar 12) (NVar 16));
  (23, Succ (NVar 13) (NVar 17))].
Definition step_rule := npis
  (step_codes ++ [(18, LR (NVar 10) (NVar 11) (NVar 12) (NVar 13))] ++ step_edges)
  (LR (NVar 14) (NVar 15) (NVar 16) (NVar 17)).
Definition ren_at_fields :=
  [(70, nArrow C (nArrow C (nArrow C (nArrow C (NSort 10)))));
   (71, base_rule); (72, zero_rule); (73, step_rule)].
Definition ren_at_arguments := [(0, FType); (1, C); (2, C); (3, C); (4, C); (5, C)].
Definition ren_at := close (nlams ren_at_arguments
  (npis ren_at_fields (LR (NVar 2) (NVar 3) (NVar 4) (NVar 5)))) eq_refl.
Definition RenAt f base target depth i j :=
  napps (NClosed ren_at) [f; base; target; depth; i; j].
Definition ren_at_sort_type := close
  (npis ren_at_arguments (NSort 14)) eq_refl.
Theorem ren_at_sorted : Typed ε ren_at ren_at_sort_type.
Proof. RkCheck.certify_with 1024. Qed.

Definition ren_at_base_arguments := [(0, FType); (1, C); (12, C); (13, C);
  (18, napps (NVar 0) [NVar 12; NVar 13])].
Definition ren_at_base_type := close (npis ren_at_base_arguments
  (RenAt (NVar 0) (NVar 1) (NVar 1) stop (NVar 12) (NVar 13))) eq_refl.
Definition ren_at_base := close (nlams (ren_at_base_arguments ++ ren_at_fields)
  (napps (NVar 71) [NVar 12; NVar 13; NVar 18])) eq_refl.
Theorem ren_at_base_type_sorted : Typed ε ren_at_base_type (𝓤 14).
Proof. RkCheck.certify_with 1024. Qed.
Theorem ren_at_base_typed : Typed ε ren_at_base ren_at_base_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition ren_at_zero_type := close
  (npis ([(0, FType); (1, C)] ++ zero_arguments)
    (RenAt (NVar 0) (NVar 1) (NVar 14) (NVar 15) stop stop)) eq_refl.
Definition ren_at_zero := close
  (nlams ([(0, FType); (1, C)] ++ zero_arguments ++ ren_at_fields)
    (napps (NVar 72) [NVar 10; NVar 14; NVar 11; NVar 15; NVar 20; NVar 21])) eq_refl.
Theorem ren_at_zero_type_sorted : Typed ε ren_at_zero_type (𝓤 14).
Proof. RkCheck.certify_with 1024. Qed.
Theorem ren_at_zero_typed : Typed ε ren_at_zero ren_at_zero_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition ren_at_step_arguments := [(0, FType); (1, C)] ++ step_codes ++
  [(18, RenAt (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 13))] ++ step_edges.
Definition ren_at_step_type := close (npis ren_at_step_arguments
  (RenAt (NVar 0) (NVar 1) (NVar 14) (NVar 15) (NVar 16) (NVar 17))) eq_refl.
Definition ren_at_step := close (nlams (ren_at_step_arguments ++ ren_at_fields)
  (napps (NVar 73) [NVar 10; NVar 11; NVar 12; NVar 13;
    NVar 14; NVar 15; NVar 16; NVar 17;
    napps (NVar 18) [NVar 70; NVar 71; NVar 72; NVar 73];
    NVar 20; NVar 21; NVar 22; NVar 23])) eq_refl.
Theorem ren_at_step_type_sorted : Typed ε ren_at_step_type (𝓤 15).
Proof. RkCheck.certify_with 1024. Qed.
Theorem ren_at_step_typed : Typed ε ren_at_step ren_at_step_type.
Proof. RkCheck.certify_with 8192. Qed.

(** The exact rank-10 motive is Index(currentTarget,output). Neither source
    index inversion nor functionality of F or binary successor is needed. *)
Definition bound_motive := nlams [(10, C); (11, C); (12, C); (13, C)]
  (Index (NVar 10) (NVar 13)).
Definition bound_base := nlams [(12, C); (13, C);
  (18, napps (NVar 0) [NVar 12; NVar 13])]
  (napps (NVar 6) [NVar 12; NVar 13; NVar 18]).
Definition bound_zero := nlams zero_arguments
  (napps (NClosed index_zero) [NVar 10; NVar 14; NVar 20]).
Definition bound_step := nlams
  (step_codes ++ [(18, Index (NVar 10) (NVar 13))] ++ step_edges)
  (napps (NClosed index_step)
    [NVar 10; NVar 13; NVar 14; NVar 17; NVar 18; NVar 20; NVar 23]).
Definition bound_arguments := ren_at_arguments ++
  [(6, FBound (NVar 1) (NVar 0));
   (7, RenAt (NVar 0) (NVar 1) (NVar 2) (NVar 3) (NVar 4) (NVar 5))].
Definition ren_at_bound_type := close (npis bound_arguments
  (Index (NVar 2) (NVar 5))) eq_refl.
Definition ren_at_bound := close (nlams bound_arguments
  (napps (NVar 7) [bound_motive; bound_base; bound_zero; bound_step])) eq_refl.
Theorem ren_at_bound_type_sorted : Typed ε ren_at_bound_type (𝓤 15).
Proof. RkCheck.certify_with 2048. Qed.
Theorem ren_at_bound_typed : Typed ε ren_at_bound ren_at_bound_type.
Proof. RkCheck.certify_with 8192. Qed.

(** This instance restricts an ordinary successor relation to source-valid
    indices. Its sole constructor contains no target Index premise. *)
Definition shift_rule := npis [(12, C); (13, C);
  (18, Index (NVar 0) (NVar 12)); (19, Succ (NVar 12) (NVar 13))]
  (napps (NVar 70) [NVar 12; NVar 13]).
Definition shift_fields := [(70, nArrow C (nArrow C (NSort 10))); (71, shift_rule)].
Definition bounded_shift := close (nlams [(0, C); (1, C); (2, C)]
  (npis shift_fields (napps (NVar 70) [NVar 1; NVar 2]))) eq_refl.
Definition ShiftEnv source := NApp (NClosed bounded_shift) source.
Definition ShiftF source i j := napps (ShiftEnv source) [i; j].
Theorem bounded_shift_sorted : Typed ε bounded_shift
  (Arrow carrier (Arrow carrier (Arrow carrier (𝓤 12)))).
Proof. RkCheck.certify_with 1024. Qed.
Definition bounded_shift_intro_arguments := [(0, C); (1, C); (2, C);
  (3, Index (NVar 0) (NVar 1)); (4, Succ (NVar 1) (NVar 2))].
Definition bounded_shift_intro_type := close (npis bounded_shift_intro_arguments
  (ShiftF (NVar 0) (NVar 1) (NVar 2))) eq_refl.
Definition bounded_shift_intro := close
  (nlams (bounded_shift_intro_arguments ++ shift_fields)
    (napps (NVar 71) [NVar 1; NVar 2; NVar 3; NVar 4])) eq_refl.
Theorem bounded_shift_intro_type_sorted : Typed ε bounded_shift_intro_type (𝓤 12).
Proof. RkCheck.certify_with 1024. Qed.
Theorem bounded_shift_intro_typed : Typed ε bounded_shift_intro bounded_shift_intro_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition bounded_shift_bound_arguments :=
  [(0, C); (1, C); (2, Succ (NVar 0) (NVar 1))].
Definition bounded_shift_bound_type := close (npis bounded_shift_bound_arguments
  (FBound (NVar 1) (ShiftEnv (NVar 0)))) eq_refl.
Definition bounded_shift_bound_case := nlams [(12, C); (13, C);
  (18, Index (NVar 0) (NVar 12)); (19, Succ (NVar 12) (NVar 13))]
  (napps (NClosed index_step)
    [NVar 0; NVar 12; NVar 1; NVar 13; NVar 18; NVar 2; NVar 19]).
Definition bounded_shift_bound := close
  (nlams (bounded_shift_bound_arguments ++ [(10, C); (11, C);
    (12, ShiftF (NVar 0) (NVar 10) (NVar 11))])
    (napps (NVar 12) [nlams [(20, C); (21, C)] (Index (NVar 1) (NVar 21));
      bounded_shift_bound_case])) eq_refl.
Theorem bounded_shift_bound_type_sorted : Typed ε bounded_shift_bound_type (𝓤 13).
Proof. RkCheck.certify_with 1024. Qed.
Theorem bounded_shift_bound_typed : Typed ε bounded_shift_bound bounded_shift_bound_type.
Proof. RkCheck.certify_with 8192. Qed.
End InternalRenamingLookup.
