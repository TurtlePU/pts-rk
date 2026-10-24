(** Internal root functionality and leaf/step separation, without external
    normalization, parametricity or a Bottom-emptiness oracle. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalPaths.
Import ListNotations.

Module ResourceSeparation.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalPaths.InternalPaths.

Definition yes := NClosed Top.
Definition no := NClosed Bottom.
Definition yes_proof := NClosed top_proof.
(** Type-valued observations use the existing fold at X = U1 : U0.
    They are ordinary PTS definitions, not extra eliminators. *)
Definition stop_test x := napps x ([NSort 1] ++
  map (fun t => match t with NZero => yes | _ => no end) tags ++
  [nlams [(70, NSort 1); (71, NSort 1)] no]).
Definition atom_test x := napps x ([NSort 1] ++
  map (fun _ => yes) tags ++ [nlams [(70, NSort 1); (71, NSort 1)] no]).
Definition root_claim (reverse : bool) a p v := nArrow (stop_test p)
  (if reverse then Eq v a else Eq a v).
Definition root_motive reverse := nlams [(11, C); (18, C); (19, C)]
  (nArrow Unit4 (root_claim reverse (NVar 11) (NVar 18) (NVar 19))).
Definition root_base := nlams [(11, C); (16, G (NVar 11));
  (40, Unit4); (41, yes)] (InternalPaths.eq_refl (NVar 11)).
Definition root_step (reverse left : bool) := nlams
  [(11, C); (12, C); (18, C); (19, C);
   (16, G (NVar (if left then 12 else 11)));
   (17, nArrow Unit4 (root_claim reverse
     (NVar (if left then 11 else 12)) (NVar 18) (NVar 19)));
   (40, Unit4); (41, no); (60, nArrow C (NSort 0));
   (61, NApp (NVar 60) (if reverse then NVar 19 else node (NVar 11) (NVar 12)))]
  (NApp (NVar 41) (NApp (NVar 60)
    (if reverse then node (NVar 11) (NVar 12) else NVar 19))).
Definition root_arguments := [(0, C); (1, C); (2, C);
  (3, Look (NVar 0) (NVar 1) (NVar 2))].
Definition root_equation_type reverse := close
  (npis root_arguments (root_claim reverse (NVar 0) (NVar 1) (NVar 2)))
  (ltac:(destruct reverse; reflexivity)).
Definition root_equation reverse := close
  (nlams root_arguments (napps (NVar 3)
    [root_motive reverse; root_base; root_step reverse true;
     root_step reverse false; unit4])) (ltac:(destruct reverse; reflexivity)).
Theorem root_equation_typed reverse :
  Typed ε (root_equation reverse) (root_equation_type reverse).
Proof. destruct reverse; RkCheck.certify_with 512. Qed.
Theorem root_equation_sorted reverse : Typed ε (root_equation_type reverse) (𝓤 8).
Proof. destruct reverse; RkCheck.certify_with 512. Qed.

Definition root_functional_type := close
  (npis [(0, C); (1, C); (2, C);
    (3, Look (NVar 0) stop (NVar 1)); (4, Look (NVar 0) stop (NVar 2))]
    (Eq (NVar 1) (NVar 2))) Logic.eq_refl.
Definition root_functional := close
  (nlams [(0, C); (1, C); (2, C);
    (3, Look (NVar 0) stop (NVar 1)); (4, Look (NVar 0) stop (NVar 2));
    (60, nArrow C (NSort 0)); (61, NApp (NVar 60) (NVar 1))]
    (napps (NClosed (root_equation false)) [NVar 0; stop; NVar 2; NVar 4;
      yes_proof; NVar 60;
      napps (NClosed (root_equation true)) [NVar 0; stop; NVar 1; NVar 3;
        yes_proof; NVar 60; NVar 61]])) Logic.eq_refl.
Theorem root_functional_typed : Typed ε root_functional root_functional_type.
Proof. RkCheck.certify_with 512. Qed.

(** Any leaf-like resource forces a stop-like path. This is a statement
    about arbitrary represented inputs, not just standard quotations. *)
Definition leaf_claim a p := nArrow (atom_test a) (stop_test p).
Definition leaf_motive := nlams [(11, C); (18, C); (19, C)]
  (nArrow Unit4 (leaf_claim (NVar 11) (NVar 18))).
Definition leaf_base := nlams [(11, C); (16, G (NVar 11));
  (40, Unit4); (41, atom_test (NVar 11))] yes_proof.
Definition leaf_step (left : bool) := nlams
  [(11, C); (12, C); (18, C); (19, C);
   (16, G (NVar (if left then 12 else 11)));
   (17, nArrow Unit4 (leaf_claim (NVar (if left then 11 else 12)) (NVar 18)));
   (40, Unit4); (41, no)] (NVar 41).
Definition leaf_path_type := close (npis root_arguments
  (leaf_claim (NVar 0) (NVar 1))) Logic.eq_refl.
Definition leaf_path := close (nlams root_arguments
  (napps (NVar 3) [leaf_motive; leaf_base; leaf_step true; leaf_step false; unit4])) Logic.eq_refl.
Theorem leaf_path_typed : Typed ε leaf_path leaf_path_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem leaf_path_sorted : Typed ε leaf_path_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.

Definition leaf_step_rejection_type (left : bool) := close
  (npis [(0, C); (1, C); (2, C); (3, atom_test (NVar 0));
    (4, Look (NVar 0) ((if left then left_path else right_path) (NVar 1)) (NVar 2))] no)
  (ltac:(destruct left; reflexivity)).
Definition leaf_step_rejection (left : bool) := close
  (nlams [(0, C); (1, C); (2, C); (3, atom_test (NVar 0));
    (4, Look (NVar 0) ((if left then left_path else right_path) (NVar 1)) (NVar 2))]
    (napps (NClosed leaf_path) [NVar 0;
      (if left then left_path else right_path) (NVar 1); NVar 2; NVar 4; NVar 3]))
  (ltac:(destruct left; reflexivity)).
Theorem leaf_step_rejection_typed side :
  Typed ε (leaf_step_rejection side) (leaf_step_rejection_type side).
Proof. destruct side; RkCheck.certify_with 512. Qed.

End ResourceSeparation.
