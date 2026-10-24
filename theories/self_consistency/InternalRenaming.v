(** Source-directed relational renaming of annotated source codes. One base
    environment is fixed under binders; explicit binary successor witnesses
    update source/target bounds and binder depth. No scope-preservation
    conclusion or bounded-environment condition occurs in the graph rules. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalBinary InternalScope InternalRenamingLookup.
Import ListNotations.

Module InternalRenaming.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalBinary.InternalBinary
  InternalScope.InternalScope InternalRenamingLookup.InternalRenamingLookup.

Definition RR source target depth t u :=
  napps (NVar 80) [source; target; depth; t; u].
Definition sort_arguments := [(10, C); (11, C); (12, C); (13, C);
  (14, Num (NVar 10)); (15, Num (NVar 11)); (16, Num (NVar 13))].
Definition sort_rule := npis sort_arguments
  (RR (NVar 10) (NVar 11) (NVar 12) (sort_code (NVar 13)) (sort_code (NVar 13))).
Definition var_arguments := [(10, C); (11, C); (12, C); (13, C); (14, C);
  (15, Index (NVar 10) (NVar 13));
  (16, RenAt (NVar 0) (NVar 1) (NVar 11) (NVar 12) (NVar 13) (NVar 14))].
Definition var_rule := npis var_arguments
  (RR (NVar 10) (NVar 11) (NVar 12) (var_code (NVar 13)) (var_code (NVar 14))).
Definition binder_codes := [(10, C); (11, C); (12, C);
  (13, C); (14, C); (15, C); (16, C); (17, C); (18, C); (19, C)].
Definition binder_edges := [(20, Succ (NVar 10) (NVar 13));
  (21, Succ (NVar 11) (NVar 14)); (22, Succ (NVar 12) (NVar 15))].
Definition binder_rule tag := npis (binder_codes ++ binder_edges ++
  [(23, RR (NVar 10) (NVar 11) (NVar 12) (NVar 16) (NVar 17));
   (24, RR (NVar 13) (NVar 14) (NVar 15) (NVar 18) (NVar 19))])
  (RR (NVar 10) (NVar 11) (NVar 12)
    (binary_code tag (NVar 16) (NVar 18)) (binary_code tag (NVar 17) (NVar 19))).
Definition app_codes := [(10, C); (11, C); (12, C); (13, C); (14, C); (15, C); (16, C)].
Definition app_rule := npis (app_codes ++
  [(17, RR (NVar 10) (NVar 11) (NVar 12) (NVar 13) (NVar 14));
   (18, RR (NVar 10) (NVar 11) (NVar 12) (NVar 15) (NVar 16))])
  (RR (NVar 10) (NVar 11) (NVar 12)
    (binary_code TApp (NVar 13) (NVar 15)) (binary_code TApp (NVar 14) (NVar 16))).
Definition rename_fields :=
  [(80, nArrow C (nArrow C (nArrow C (nArrow C (nArrow C (NSort 12))))));
   (81, sort_rule); (82, var_rule); (83, binder_rule TPi);
   (84, binder_rule TLam); (85, app_rule)].
Definition rename_arguments := [(0, FType); (1, C); (2, C); (3, C); (4, C); (5, C); (6, C)].
Definition renaming := close (nlams rename_arguments
  (npis rename_fields (RR (NVar 2) (NVar 3) (NVar 4) (NVar 5) (NVar 6)))) eq_refl.
Definition Rename f base source target depth t u :=
  napps (NClosed renaming) [f; base; source; target; depth; t; u].
Definition renaming_sort_type := close (npis rename_arguments (NSort 16)) eq_refl.
Theorem renaming_sorted : Typed ε renaming renaming_sort_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition rename_sort_type := close
  (npis ([(0, FType); (1, C)] ++ sort_arguments)
    (Rename (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
      (sort_code (NVar 13)) (sort_code (NVar 13)))) eq_refl.
Definition rename_sort := close
  (nlams ([(0, FType); (1, C)] ++ sort_arguments ++ rename_fields)
    (napps (NVar 81) [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 15; NVar 16])) eq_refl.
Theorem rename_sort_type_sorted : Typed ε rename_sort_type (𝓤 16).
Proof. RkCheck.certify_with 4096. Qed.
Theorem rename_sort_typed : Typed ε rename_sort rename_sort_type.
Proof. RkCheck.certify_with 16384. Qed.

Definition rename_var_type := close
  (npis ([(0, FType); (1, C)] ++ var_arguments)
    (Rename (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
      (var_code (NVar 13)) (var_code (NVar 14)))) eq_refl.
Definition rename_var := close
  (nlams ([(0, FType); (1, C)] ++ var_arguments ++ rename_fields)
    (napps (NVar 82) [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 15; NVar 16])) eq_refl.
Theorem rename_var_type_sorted : Typed ε rename_var_type (𝓤 16).
Proof. RkCheck.certify_with 4096. Qed.
Theorem rename_var_typed : Typed ε rename_var rename_var_type.
Proof. RkCheck.certify_with 16384. Qed.

Definition rename_use h := napps h [NVar 80; NVar 81; NVar 82; NVar 83; NVar 84; NVar 85].
Definition rename_binder_arguments := [(0, FType); (1, C)] ++ binder_codes ++ binder_edges ++
  [(23, Rename (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 16) (NVar 17));
   (24, Rename (NVar 0) (NVar 1) (NVar 13) (NVar 14) (NVar 15) (NVar 18) (NVar 19))].
Definition rename_binder_type (product : bool) := close
  (npis rename_binder_arguments
    (Rename (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
      (binary_code (if product then TPi else TLam) (NVar 16) (NVar 18))
      (binary_code (if product then TPi else TLam) (NVar 17) (NVar 19))))
  (ltac:(destruct product; reflexivity)).
Definition rename_binder (product : bool) := close
  (nlams (rename_binder_arguments ++ rename_fields)
    (napps (NVar (if product then 83 else 84))
      [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 15;
       NVar 16; NVar 17; NVar 18; NVar 19; NVar 20; NVar 21; NVar 22;
       rename_use (NVar 23); rename_use (NVar 24)]))
  (ltac:(destruct product; reflexivity)).
Theorem rename_binder_type_sorted product : Typed ε (rename_binder_type product) (𝓤 17).
Proof. destruct product; RkCheck.certify_with 4096. Qed.
Theorem rename_binder_typed product : Typed ε (rename_binder product) (rename_binder_type product).
Proof. destruct product; RkCheck.certify_with 65536. Qed.

Definition rename_app_arguments := [(0, FType); (1, C)] ++ app_codes ++
  [(17, Rename (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 13) (NVar 14));
   (18, Rename (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 15) (NVar 16))].
Definition rename_app_type := close (npis rename_app_arguments
  (Rename (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
    (binary_code TApp (NVar 13) (NVar 15)) (binary_code TApp (NVar 14) (NVar 16)))) eq_refl.
Definition rename_app := close (nlams (rename_app_arguments ++ rename_fields)
  (napps (NVar 85) [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 15; NVar 16;
    rename_use (NVar 17); rename_use (NVar 18)])) eq_refl.
Theorem rename_app_type_sorted : Typed ε rename_app_type (𝓤 17).
Proof. RkCheck.certify_with 4096. Qed.
Theorem rename_app_typed : Typed ε rename_app rename_app_type.
Proof. RkCheck.certify_with 65536. Qed.

(** Fold the independent graph into the literal output-scope predicate.
    FBound is a theorem premise, not a graph constructor. RenAt's proved
    all-output bound handles variables; the binder uses the SAME base F. *)
Definition scope_motive := nlams [(10, C); (11, C); (12, C); (13, C); (14, C)]
  (Scope (NVar 11) (NVar 14)).
Definition scope_sort_case := nlams sort_arguments
  (napps (NClosed scope_sort) [NVar 11; NVar 13; NVar 15; NVar 16]).
Definition scope_var_case := nlams var_arguments
  (napps (NClosed scope_var) [NVar 11; NVar 14;
    napps (NClosed ren_at_bound)
      [NVar 0; NVar 1; NVar 11; NVar 12; NVar 13; NVar 14; NVar 7; NVar 16]]).
Definition scope_binder_case (product : bool) :=
  nlams (binder_codes ++ binder_edges ++
    [(23, Scope (NVar 11) (NVar 17)); (24, Scope (NVar 14) (NVar 19))])
    (napps (NClosed (scope_binder product))
      [NVar 11; NVar 14; NVar 17; NVar 19; NVar 21; NVar 23; NVar 24]).
Definition scope_app_case := nlams (app_codes ++
  [(17, Scope (NVar 11) (NVar 14)); (18, Scope (NVar 11) (NVar 16))])
  (napps (NClosed scope_app) [NVar 11; NVar 14; NVar 16; NVar 17; NVar 18]).
Definition preservation_arguments := rename_arguments ++
  [(7, FBound (NVar 1) (NVar 0));
   (8, Rename (NVar 0) (NVar 1) (NVar 2) (NVar 3) (NVar 4) (NVar 5) (NVar 6))].
Definition renaming_scope_type := close
  (npis preservation_arguments (Scope (NVar 3) (NVar 6))) eq_refl.
Definition renaming_scope := close (nlams preservation_arguments
  (napps (NVar 8) [scope_motive; scope_sort_case; scope_var_case;
    scope_binder_case true; scope_binder_case false; scope_app_case])) eq_refl.
Theorem renaming_scope_type_sorted : Typed ε renaming_scope_type (𝓤 17).
Proof. RkCheck.certify_with 16384. Qed.
Theorem renaming_scope_typed : Typed ε renaming_scope renaming_scope_type.
Proof. RkCheck.certify_with 262144. Qed.

End InternalRenaming.
