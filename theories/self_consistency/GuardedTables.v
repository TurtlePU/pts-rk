(** Internal finite-table laws, not just computation on canonical inputs.
    Each public witness is a CLOSED term of the ORIGINAL annotated PTS. *)
From Stdlib Require Import Lists.List Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
Import ListNotations.

Module GuardedTables.
Import CommonCodes Core Structural.

Definition boolean := close
  (NPi 0 (NSort 0) (nArrow (NVar 0) (nArrow (NVar 0) (NVar 0)))) eq_refl.
Definition point (b : bool) := close
  (nlams [(0, NSort 0); (1, NVar 0); (2, NVar 0)]
    (NVar (if b then 1 else 2))) (ltac:(destruct b; reflexivity)).
Definition B := NClosed boolean.
Definition T := NClosed (point true).
Definition F := NClosed (point false).

(** The index denotes the EXACT motive sort, not a cumulative upper bound. *)
Definition can (r : nat) := close
  (NLam 0 B (NPi 10 (nArrow B (NSort r))
    (nArrow (NApp (NVar 10) T)
      (nArrow (NApp (NVar 10) F) (NApp (NVar 10) (NVar 0)))))) eq_refl.
Definition Can r x := NApp (NClosed (can r)) x.
Definition canonical r (b : bool) := close
  (nlams [(10, nArrow B (NSort r)); (11, NApp (NVar 10) T);
    (12, NApp (NVar 10) F)] (NVar (if b then 11 else 12)))
    (ltac:(destruct b; reflexivity)).

Theorem boolean_sorted : Typed ε boolean (𝓤 1).
Proof. RkCheck.certify_with 64. Qed.
Theorem point_typed b : Typed ε (point b) boolean.
Proof. destruct b; RkCheck.certify_with 64. Qed.
Theorem can_one_sorted : Typed ε (can 1) (Arrow boolean (𝓤 3)).
Proof. RkCheck.certify_with 64. Qed.
Theorem can_two_sorted : Typed ε (can 2) (Arrow boolean (𝓤 3)).
Proof. RkCheck.certify_with 64. Qed.
Theorem canonical_one_typed b :
  Typed ε (canonical 1 b) (app (can 1) (point b)).
Proof. destruct b; RkCheck.certify_with 64. Qed.
Theorem canonical_two_typed b :
  Typed ε (canonical 2 b) (app (can 2) (point b)).
Proof. destruct b; RkCheck.certify_with 64. Qed.

(** All named binders introduced here are fresh for the supplied templates. *)
Definition cases2 (R : named -> named -> named) ptt ptf pft pff (x gx y gy : named) :=
  napps gx [NLam 50 B (R (NVar 50) y);
    napps gy [NLam 51 B (R T (NVar 51)); ptt; ptf];
    napps gy [NLam 51 B (R F (NVar 51)); pft; pff]].
Definition arguments := [(20, B); (21, Can 1 (NVar 20));
                         (22, B); (23, Can 1 (NVar 22))].
Definition at2 f x y := napps f [x; y].
Definition binary_type := nArrow B (nArrow B B).
Definition four_cases (R : named -> named -> named) :=
  [(30, R T T); (31, R T F); (32, R F T); (33, R F F)].

Definition binary_elimination_type := close
  (npis ([(0, nArrow B (nArrow B (NSort 1)))] ++
    four_cases (at2 (NVar 0)) ++ arguments)
    (at2 (NVar 0) (NVar 20) (NVar 22))) eq_refl.
Definition binary_elimination := close
  (nlams ([(0, nArrow B (nArrow B (NSort 1)))] ++
    four_cases (at2 (NVar 0)) ++ arguments)
    (cases2 (at2 (NVar 0)) (NVar 30) (NVar 31) (NVar 32) (NVar 33)
      (NVar 20) (NVar 21) (NVar 22) (NVar 23))) eq_refl.
Theorem binary_elimination_sorted : Typed ε binary_elimination_type (𝓤 4).
Proof. RkCheck.certify_with 128. Qed.
Theorem binary_elimination_typed : Typed ε binary_elimination binary_elimination_type.
Proof. RkCheck.certify_with 128. Qed.

(** A table is an ordinary argument.  Four LOCAL closure certificates suffice
    for closure on arbitrary guarded arguments.  Open the output guard first:
    eliminating into the rank-three Can proposition would be ill-ranked. *)
Definition table_cases := four_cases (fun x y => Can 1 (at2 (NVar 0) x y)).
Definition closure_type := close
  (npis ([(0, binary_type)] ++ table_cases ++ arguments)
    (Can 1 (at2 (NVar 0) (NVar 20) (NVar 22)))) eq_refl.
Definition predicate_fields := [(40, nArrow B (NSort 1));
  (41, NApp (NVar 40) T); (42, NApp (NVar 40) F)].
Definition open_case p := napps p [NVar 40; NVar 41; NVar 42].
Definition closure := close
  (nlams ([(0, binary_type)] ++ table_cases ++ arguments ++ predicate_fields)
    (cases2 (fun x y => NApp (NVar 40) (at2 (NVar 0) x y))
      (open_case (NVar 30)) (open_case (NVar 31))
      (open_case (NVar 32)) (open_case (NVar 33))
      (NVar 20) (NVar 21) (NVar 22) (NVar 23))) eq_refl.
Theorem closure_type_sorted : Typed ε closure_type (𝓤 4).
Proof. RkCheck.certify_with 128. Qed.
Theorem closure_typed : Typed ε closure closure_type.
Proof. RkCheck.certify_with 128. Qed.

Definition equal x y := NPi 40 (nArrow B (NSort 0))
  (nArrow (NApp (NVar 40) x) (NApp (NVar 40) y)).
Definition equality := close (nlams [(0, B); (1, B)]
  (equal (NVar 0) (NVar 1))) eq_refl.
Theorem equality_sorted : Typed ε equality
  (Arrow boolean (Arrow boolean (𝓤 3))).
Proof. RkCheck.certify_with 64. Qed.

Definition equality_cases := four_cases (fun x y =>
  equal (at2 (NVar 0) x y) (at2 (NVar 1) x y)).
Definition extensionality_type := close
  (npis ([(0, binary_type); (1, binary_type)] ++ equality_cases ++ arguments)
    (equal (at2 (NVar 0) (NVar 20) (NVar 22))
      (at2 (NVar 1) (NVar 20) (NVar 22)))) eq_refl.
Definition extensionality := close
  (nlams ([(0, binary_type); (1, binary_type)] ++ equality_cases ++ arguments ++
    [(40, nArrow B (NSort 0))])
    (cases2 (fun x y => nArrow
      (NApp (NVar 40) (at2 (NVar 0) x y))
      (NApp (NVar 40) (at2 (NVar 1) x y)))
      (NApp (NVar 30) (NVar 40)) (NApp (NVar 31) (NVar 40))
      (NApp (NVar 32) (NVar 40)) (NApp (NVar 33) (NVar 40))
      (NVar 20) (NVar 21) (NVar 22) (NVar 23))) eq_refl.
Theorem extensionality_type_sorted : Typed ε extensionality_type (𝓤 4).
Proof. RkCheck.certify_with 128. Qed.
Theorem extensionality_typed : Typed ε extensionality extensionality_type.
Proof. RkCheck.certify_with 128. Qed.

(** Generic table data: four entries of the SAME fixed carrier.  Dispatch
    opens the output selector before either input; no E : U0 is asserted. *)
Definition entry_fields := [(0, B); (1, B); (2, B); (3, B)].
Definition dispatch_entry i := napps (NVar i) [NVar 90; NVar 91; NVar 92].
Definition table := close
  (nlams (entry_fields ++ [(20, B); (22, B); (90, NSort 0);
    (91, NVar 90); (92, NVar 90)])
    (napps (NVar 20) [NVar 90;
      napps (NVar 22) [NVar 90; dispatch_entry 0; dispatch_entry 1];
      napps (NVar 22) [NVar 90; dispatch_entry 2; dispatch_entry 3]])) eq_refl.
Definition table_type := close (npis entry_fields binary_type) eq_refl.
Theorem table_type_sorted : Typed ε table_type (𝓤 2).
Proof. RkCheck.certify_with 128. Qed.
Theorem table_typed : Typed ε table table_type.
Proof. RkCheck.certify_with 128. Qed.

Definition lookup t00 t01 t10 t11 :=
  napps (NClosed table) [t00; t01; t10; t11].
Definition table_of (tt tf ft ff : bool) : closed_term :=
  app (app (app (app table (point tt)) (point tf)) (point ft)) (point ff).
Theorem all_sixteen_tables_typed tt tf ft ff : Typed ε (table_of tt tf ft ff)
  (Arrow boolean (Arrow boolean boolean)).
Proof. destruct tt, tf, ft, ff; RkCheck.certify_with 128. Qed.

(** Table selection returns explicit eta expansion, NOT eta conversion.
    Its guard/equality laws are proved by guarded finite cases. *)
Definition expanded x := nlams [(90, NSort 0); (91, NVar 90); (92, NVar 90)]
  (napps x [NVar 90; NVar 91; NVar 92]).
Definition expansion_guard_type := close
  (npis [(0, B); (1, Can 1 (NVar 0))] (Can 1 (expanded (NVar 0)))) eq_refl.
Definition expansion_guard := close
  (nlams ([(0, B); (1, Can 1 (NVar 0))] ++ predicate_fields)
    (napps (NVar 1) [NLam 50 B (NApp (NVar 40) (expanded (NVar 50)));
      NVar 41; NVar 42])) eq_refl.
Theorem expansion_guard_typed : Typed ε expansion_guard expansion_guard_type.
Proof. RkCheck.certify_with 128. Qed.

Definition expansion_equal_type := close
  (npis [(0, B); (1, Can 1 (NVar 0))] (equal (expanded (NVar 0)) (NVar 0))) eq_refl.
Definition expansion_equal := close
  (nlams [(0, B); (1, Can 1 (NVar 0)); (40, nArrow B (NSort 0))]
    (napps (NVar 1)
      [NLam 50 B (nArrow (NApp (NVar 40) (expanded (NVar 50)))
        (NApp (NVar 40) (NVar 50)));
       NLam 41 (NApp (NVar 40) T) (NVar 41);
       NLam 41 (NApp (NVar 40) F) (NVar 41)])) eq_refl.
Theorem expansion_equal_typed : Typed ε expansion_equal expansion_equal_type.
Proof. RkCheck.certify_with 128. Qed.

Definition guarded_entries := [(0, B); (4, Can 1 (NVar 0));
  (1, B); (5, Can 1 (NVar 1)); (2, B); (6, Can 1 (NVar 2));
  (3, B); (7, Can 1 (NVar 3))].
Definition data_table := lookup (NVar 0) (NVar 1) (NVar 2) (NVar 3).
Definition data_closure_type := close
  (npis (guarded_entries ++ arguments)
    (Can 1 (at2 data_table (NVar 20) (NVar 22)))) eq_refl.
Definition data_closure := close
  (nlams (guarded_entries ++ arguments)
    (napps (NClosed closure) ([data_table] ++
      map (fun i => napps (NClosed expansion_guard) [NVar i; NVar (4+i)])
        [0; 1; 2; 3] ++ [NVar 20; NVar 21; NVar 22; NVar 23]))) eq_refl.
Theorem data_closure_type_sorted : Typed ε data_closure_type (𝓤 4).
Proof. RkCheck.certify_with 256. Qed.
Theorem data_closure_typed : Typed ε data_closure data_closure_type.
Proof. RkCheck.certify_with 256. Qed.

Definition selected_index (x y : bool) :=
  if x then (if y then 0 else 1) else (if y then 2 else 3).
Definition data_lookup_type (x y : bool) := close
  (npis guarded_entries
    (equal (at2 data_table (NClosed (point x)) (NClosed (point y)))
      (NVar (selected_index x y)))) (ltac:(destruct x, y; reflexivity)).
Definition data_lookup (x y : bool) := close
  (nlams guarded_entries (napps (NClosed expansion_equal)
    [NVar (selected_index x y); NVar (4 + selected_index x y)]))
    (ltac:(destruct x, y; reflexivity)).
Theorem data_lookup_typed x y : Typed ε (data_lookup x y) (data_lookup_type x y).
Proof. destruct x, y; RkCheck.certify_with 256. Qed.

End GuardedTables.
