(** Independent single-substitution environment. Zero returns the supplied
    image; successor indices return the corresponding old variable. Neither
    rule assumes output scope. The local bound is a separate original-PTS
    theorem, derived from scope of the supplied image. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalBinary InternalScope.
Import ListNotations.

Module InternalSubstitutionEnvironment.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalBinary.InternalBinary
  InternalScope.InternalScope.

Definition TermFType := nArrow C (nArrow C (NSort 13)).
Definition TermFBound target f := npis [(10, C); (11, C);
  (12, napps f [NVar 10; NVar 11])] (Scope target (NVar 11)).
Definition image_rule := napps (NVar 70) [stop; NVar 1].
Definition old_arguments := [(10, C); (11, C);
  (12, Index (NVar 0) (NVar 10)); (13, Succ (NVar 10) (NVar 11))].
Definition old_rule := npis old_arguments
  (napps (NVar 70) [NVar 11; var_code (NVar 10)]).
Definition single_fields := [(70, nArrow C (nArrow C (NSort 12)));
  (71, image_rule); (72, old_rule)].
Definition single_environment := close (nlams [(0, C); (1, C); (2, C); (3, C)]
  (npis single_fields (napps (NVar 70) [NVar 2; NVar 3]))) eq_refl.
Definition SingleEnv target image := napps (NClosed single_environment) [target; image].
Definition Single target image i v := napps (SingleEnv target image) [i; v].
Theorem single_environment_sorted : Typed ε single_environment
  (Arrow carrier (Arrow carrier (Arrow carrier (Arrow carrier (𝓤 13))))).
Proof. RkCheck.certify_with 1024. Qed.

Definition single_image_type := close (npis [(0, C); (1, C)]
  (Single (NVar 0) (NVar 1) stop (NVar 1))) eq_refl.
Definition single_image := close (nlams ([(0, C); (1, C)] ++ single_fields)
  (NVar 71)) eq_refl.
Theorem single_image_type_sorted : Typed ε single_image_type (𝓤 13).
Proof. RkCheck.certify_with 1024. Qed.
Theorem single_image_typed : Typed ε single_image single_image_type.
Proof. RkCheck.certify_with 2048. Qed.

Definition single_old_type := close (npis ([(0, C); (1, C)] ++ old_arguments)
  (Single (NVar 0) (NVar 1) (NVar 11) (var_code (NVar 10)))) eq_refl.
Definition single_old := close
  (nlams ([(0, C); (1, C)] ++ old_arguments ++ single_fields)
    (napps (NVar 72) [NVar 10; NVar 11; NVar 12; NVar 13])) eq_refl.
Theorem single_old_type_sorted : Typed ε single_old_type (𝓤 13).
Proof. RkCheck.certify_with 1024. Qed.
Theorem single_old_typed : Typed ε single_old single_old_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition single_bound_arguments := [(0, C); (1, C);
  (2, Scope (NVar 0) (NVar 1))].
Definition single_bound_type := close (npis single_bound_arguments
  (TermFBound (NVar 0) (SingleEnv (NVar 0) (NVar 1)))) eq_refl.
Definition single_bound_motive := nlams [(20, C); (21, C)]
  (Scope (NVar 0) (NVar 21)).
Definition single_bound_old := nlams old_arguments
  (napps (NClosed scope_var) [NVar 0; NVar 10; NVar 12]).
Definition single_bound := close
  (nlams (single_bound_arguments ++ [(10, C); (11, C);
    (12, Single (NVar 0) (NVar 1) (NVar 10) (NVar 11))])
    (napps (NVar 12) [single_bound_motive; NVar 2; single_bound_old])) eq_refl.
Theorem single_bound_type_sorted : Typed ε single_bound_type (𝓤 14).
Proof. RkCheck.certify_with 2048. Qed.
Theorem single_bound_typed : Typed ε single_bound single_bound_type.
Proof. RkCheck.certify_with 8192. Qed.

End InternalSubstitutionEnvironment.
