(** Stratified one-step inversion for arbitrary represented lookup proofs.
    No constructor injectivity or functionality is assumed. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier InternalResources InternalPaths.
Import ListNotations.
Module LookupInversion.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalPaths.InternalPaths.
(** SAME local lookup rules, a separately declared exact motive rank 9.
    One-step case analysis is derived below, not a clause of this relation. *)
Definition deep_fields := [(30, nArrow C (nArrow C (nArrow C (NSort 9))));
  (31, root_rule); (32, left_rule); (33, right_rule)].
Definition deep_lookup := close (nlams [(0, C); (1, C); (2, C)]
  (npis deep_fields (R (NVar 0) (NVar 1) (NVar 2)))) Logic.eq_refl.
Definition Deep a p v := napps (NClosed deep_lookup) [a; p; v].
Theorem deep_lookup_sorted : Typed ε deep_lookup
  (Arrow carrier (Arrow carrier (Arrow carrier (𝓤 11)))).
Proof. RkCheck.certify_with 512. Qed.
Definition deep_root_type := close
  (npis [(0, C); (3, G (NVar 0))] (Deep (NVar 0) stop (NVar 0))) Logic.eq_refl.
Definition deep_root := close
  (nlams ([(0, C); (3, G (NVar 0))] ++ deep_fields)
    (napps (NVar 31) [NVar 0; NVar 3])) Logic.eq_refl.
Theorem deep_root_typed : Typed ε deep_root deep_root_type.
Proof. RkCheck.certify_with 512. Qed.
Definition deep_step_type (left : bool) := close
  (npis [(0, C); (1, C); (2, C); (3, C);
    (4, G (NVar (if left then 1 else 0)));
    (5, Deep (NVar (if left then 0 else 1)) (NVar 2) (NVar 3))]
    (Deep (node (NVar 0) (NVar 1))
      ((if left then left_path else right_path) (NVar 2)) (NVar 3)))
  (ltac:(destruct left; reflexivity)).
Definition deep_step (left : bool) := close
  (nlams ([(0, C); (1, C); (2, C); (3, C);
    (4, G (NVar (if left then 1 else 0)));
    (5, Deep (NVar (if left then 0 else 1)) (NVar 2) (NVar 3))] ++ deep_fields)
    (napps (NVar (if left then 32 else 33)) [NVar 0; NVar 1; NVar 2; NVar 3; NVar 4;
      napps (NVar 5) [NVar 30; NVar 31; NVar 32; NVar 33]]))
  (ltac:(destruct left; reflexivity)).
Theorem deep_step_typed side : Typed ε (deep_step side) (deep_step_type side).
Proof. destruct side; RkCheck.certify_with 512. Qed.

(** The case handlers receive a genuine LOWER-RANK lookup for the selected
    child, not an induction hypothesis about the target predicate. *)
Definition case_step_rule (left : bool) := npis
  [(11, C); (12, C); (18, C); (19, C);
   (16, G (NVar (if left then 12 else 11)));
   (17, Look (NVar (if left then 11 else 12)) (NVar 18) (NVar 19))]
  (R (node (NVar 11) (NVar 12))
    ((if left then left_path else right_path) (NVar 18)) (NVar 19)).
Definition case_fields := [(30, nArrow C (nArrow C (nArrow C (NSort 5))));
  (31, root_rule); (32, case_step_rule true); (33, case_step_rule false)].
Definition view := close (nlams [(0, C); (1, C); (2, C)]
  (npis case_fields (R (NVar 0) (NVar 1) (NVar 2)))) Logic.eq_refl.
Definition View a p v := napps (NClosed view) [a; p; v].
Theorem view_sorted : Typed ε view
  (Arrow carrier (Arrow carrier (Arrow carrier (𝓤 9)))).
Proof. RkCheck.certify_with 512. Qed.

Definition state a p v := NPi 50 (NSort 5)
  (nArrow (npis [(52, Look a p v); (53, R a p v)] (NVar 50)) (NVar 50)).
Definition state_fields a p v := [(50, NSort 5);
  (51, npis [(52, Look a p v); (53, R a p v)] (NVar 50))].
Definition state_root := nlams ([(11, C); (16, G (NVar 11))] ++
  state_fields (NVar 11) stop (NVar 11))
  (napps (NVar 51) [napps (NClosed lookup_root) [NVar 11; NVar 16];
    napps (NVar 31) [NVar 11; NVar 16]]).
Definition state_step (left : bool) := nlams
  ([(11, C); (12, C); (18, C); (19, C);
    (16, G (NVar (if left then 12 else 11)));
    (17, state (NVar (if left then 11 else 12)) (NVar 18) (NVar 19))] ++
   state_fields (node (NVar 11) (NVar 12))
     ((if left then left_path else right_path) (NVar 18)) (NVar 19))
  (napps (NVar 17) [NVar 50;
    nlams [(52, Look (NVar (if left then 11 else 12)) (NVar 18) (NVar 19));
           (53, R (NVar (if left then 11 else 12)) (NVar 18) (NVar 19))]
      (napps (NVar 51)
        [napps (NClosed (lookup_step left)) [NVar 11; NVar 12; NVar 18; NVar 19; NVar 16; NVar 52];
         napps (NVar (if left then 32 else 33)) [NVar 11; NVar 12; NVar 18; NVar 19; NVar 16; NVar 52]])]).
Definition inversion_type := close
  (npis [(0, C); (1, C); (2, C); (3, Deep (NVar 0) (NVar 1) (NVar 2))]
    (View (NVar 0) (NVar 1) (NVar 2))) Logic.eq_refl.
Definition inversion := close
  (nlams ([(0, C); (1, C); (2, C); (3, Deep (NVar 0) (NVar 1) (NVar 2))] ++ case_fields)
    (napps (NVar 3)
      [nlams [(11, C); (18, C); (19, C)] (state (NVar 11) (NVar 18) (NVar 19));
       state_root; state_step true; state_step false;
       R (NVar 0) (NVar 1) (NVar 2);
       nlams [(52, Look (NVar 0) (NVar 1) (NVar 2));
              (53, R (NVar 0) (NVar 1) (NVar 2))] (NVar 53)])) Logic.eq_refl.
Theorem inversion_type_sorted : Typed ε inversion_type (𝓤 12).
Proof. RkCheck.certify_with 512. Qed.
Theorem inversion_typed : Typed ε inversion inversion_type.
Proof. RkCheck.certify_with 512. Qed.

(** This freezes the FULL functionality obligation; it is only a FORMATION
    theorem. No inhabitant, axiom or hypothesis of this type is introduced. *)
Definition functionality_type := close
  (npis [(0, C); (1, C); (2, C); (3, C);
    (4, Look (NVar 0) (NVar 1) (NVar 2));
    (5, Look (NVar 0) (NVar 1) (NVar 3))] (Eq (NVar 2) (NVar 3))) Logic.eq_refl.
Theorem functionality_type_sorted : Typed ε functionality_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.
End LookupInversion.
