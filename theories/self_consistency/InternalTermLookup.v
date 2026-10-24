(** Binder-indexed lookup for one fixed TERM-valued environment.  Lifting
    an old image uses the independent annotated renaming graph, with the
    same successor edge as the target-bound update. Neither output scope
    nor the environment bound occurs in a graph clause. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalBinary InternalScope InternalRenamingLookup
  InternalRenaming InternalSubstitutionEnvironment.
Import ListNotations.

Module InternalTermLookup.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalBinary.InternalBinary
  InternalScope.InternalScope InternalRenamingLookup.InternalRenamingLookup
  InternalRenaming.InternalRenaming
  InternalSubstitutionEnvironment.InternalSubstitutionEnvironment.

Definition TR n k i u := napps (NVar 70) [n; k; i; u].
Definition base_rule := npis [(12, C); (13, C);
  (18, napps (NVar 0) [NVar 12; NVar 13])]
  (TR (NVar 1) stop (NVar 12) (NVar 13)).
Definition zero_arguments := [(10, C); (14, C); (11, C); (15, C);
  (20, Succ (NVar 10) (NVar 14)); (21, Succ (NVar 11) (NVar 15))].
Definition zero_rule := npis zero_arguments
  (TR (NVar 14) (NVar 15) stop (var_code stop)).
Definition step_codes := [(10, C); (11, C); (12, C); (13, C);
  (14, C); (15, C); (16, C); (17, C)].
Definition step_edges := [(20, Succ (NVar 10) (NVar 14));
  (21, Succ (NVar 11) (NVar 15)); (22, Succ (NVar 12) (NVar 16));
  (23, Rename (ShiftEnv (NVar 10)) (NVar 14)
    (NVar 10) (NVar 14) stop (NVar 13) (NVar 17))].
Definition step_rule := npis
  (step_codes ++ [(18, TR (NVar 10) (NVar 11) (NVar 12) (NVar 13))] ++ step_edges)
  (TR (NVar 14) (NVar 15) (NVar 16) (NVar 17)).
Definition term_at_fields :=
  [(70, nArrow C (nArrow C (nArrow C (nArrow C (NSort 12)))));
   (71, base_rule); (72, zero_rule); (73, step_rule)].
Definition term_at_arguments := [(0, TermFType); (1, C); (2, C); (3, C); (4, C); (5, C)].
Definition term_at := close (nlams term_at_arguments
  (npis term_at_fields (TR (NVar 2) (NVar 3) (NVar 4) (NVar 5)))) eq_refl.
Definition TermAt f base target depth i u :=
  napps (NClosed term_at) [f; base; target; depth; i; u].
Definition term_at_sort_type := close
  (npis term_at_arguments (NSort 18)) eq_refl.
Theorem term_at_sorted : Typed ε term_at term_at_sort_type.
Proof. RkCheck.certify_with 8192. Qed.

Definition term_at_base_arguments := [(0, TermFType); (1, C); (12, C); (13, C);
  (18, napps (NVar 0) [NVar 12; NVar 13])].
Definition term_at_base_type := close (npis term_at_base_arguments
  (TermAt (NVar 0) (NVar 1) (NVar 1) stop (NVar 12) (NVar 13))) eq_refl.
Definition term_at_base := close (nlams (term_at_base_arguments ++ term_at_fields)
  (napps (NVar 71) [NVar 12; NVar 13; NVar 18])) eq_refl.
Theorem term_at_base_type_sorted : Typed ε term_at_base_type (𝓤 18).
Proof. RkCheck.certify_with 8192. Qed.
Theorem term_at_base_typed : Typed ε term_at_base term_at_base_type.
Proof. RkCheck.certify_with 32768. Qed.

Definition term_at_zero_type := close
  (npis ([(0, TermFType); (1, C)] ++ zero_arguments)
    (TermAt (NVar 0) (NVar 1) (NVar 14) (NVar 15) stop (var_code stop))) eq_refl.
Definition term_at_zero := close
  (nlams ([(0, TermFType); (1, C)] ++ zero_arguments ++ term_at_fields)
    (napps (NVar 72) [NVar 10; NVar 14; NVar 11; NVar 15; NVar 20; NVar 21])) eq_refl.
Theorem term_at_zero_type_sorted : Typed ε term_at_zero_type (𝓤 18).
Proof. RkCheck.certify_with 8192. Qed.
Theorem term_at_zero_typed : Typed ε term_at_zero term_at_zero_type.
Proof. RkCheck.certify_with 32768. Qed.

Definition term_at_step_arguments := [(0, TermFType); (1, C)] ++ step_codes ++
  [(18, TermAt (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 13))] ++ step_edges.
Definition term_at_step_type := close (npis term_at_step_arguments
  (TermAt (NVar 0) (NVar 1) (NVar 14) (NVar 15) (NVar 16) (NVar 17))) eq_refl.
Definition term_at_step := close (nlams (term_at_step_arguments ++ term_at_fields)
  (napps (NVar 73) [NVar 10; NVar 11; NVar 12; NVar 13;
    NVar 14; NVar 15; NVar 16; NVar 17;
    napps (NVar 18) [NVar 70; NVar 71; NVar 72; NVar 73];
    NVar 20; NVar 21; NVar 22; NVar 23])) eq_refl.
Theorem term_at_step_type_sorted : Typed ε term_at_step_type (𝓤 19).
Proof. RkCheck.certify_with 16384. Qed.
Theorem term_at_step_typed : Typed ε term_at_step term_at_step_type.
Proof. RkCheck.certify_with 131072. Qed.

(** Exact rank-12 motive. The step derives the independent shift bound
    from its own target-successor edge, then applies renaming_scope to the
    supplied renaming graph. The recursive premise is retained in the graph
    for standard lifting, although this scope consequence does not use its IH. *)
Definition bound_motive := nlams [(10, C); (11, C); (12, C); (13, C)]
  (Scope (NVar 10) (NVar 13)).
Definition bound_base := nlams [(12, C); (13, C);
  (18, napps (NVar 0) [NVar 12; NVar 13])]
  (napps (NVar 6) [NVar 12; NVar 13; NVar 18]).
Definition bound_zero := nlams zero_arguments
  (napps (NClosed scope_var) [NVar 14; stop;
    napps (NClosed index_zero) [NVar 10; NVar 14; NVar 20]]).
Definition bound_step := nlams
  (step_codes ++ [(18, Scope (NVar 10) (NVar 13))] ++ step_edges)
  (napps (NClosed renaming_scope)
    [ShiftEnv (NVar 10); NVar 14; NVar 10; NVar 14; stop; NVar 13; NVar 17;
     napps (NClosed bounded_shift_bound) [NVar 10; NVar 14; NVar 20]; NVar 23]).
Definition bound_arguments := term_at_arguments ++
  [(6, TermFBound (NVar 1) (NVar 0));
   (7, TermAt (NVar 0) (NVar 1) (NVar 2) (NVar 3) (NVar 4) (NVar 5))].
Definition term_at_bound_type := close (npis bound_arguments
  (Scope (NVar 2) (NVar 5))) eq_refl.
Definition term_at_bound := close (nlams bound_arguments
  (napps (NVar 7) [bound_motive; bound_base; bound_zero; bound_step])) eq_refl.
Theorem term_at_bound_type_sorted : Typed ε term_at_bound_type (𝓤 19).
Proof. RkCheck.certify_with 16384. Qed.
Theorem term_at_bound_typed : Typed ε term_at_bound term_at_bound_type.
Proof. RkCheck.certify_with 524288. Qed.

End InternalTermLookup.
