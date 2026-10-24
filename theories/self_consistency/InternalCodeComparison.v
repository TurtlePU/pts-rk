(** Output-neutral comparison of all raw serialized trees.  Zip certifies
    only a finite joint traversal: it mentions neither an answer nor equality,
    typing, parsing, acceptance, or rejection.  Actual Boolean computation is
    a separate fold.  Every displayed term belongs to the original PTS. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectREval DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier GuardedTables.
Import ListNotations.

Module InternalCodeComparison.
Import CommonCodes Core Structural.
Module IC := InternalCarrier.InternalCarrier.
Module BT := GuardedTables.GuardedTables.

Definition C := NClosed IC.carrier.
Definition B := NClosed BT.boolean.
Definition Pair x y := napps (NClosed IC.pair) [x; y].

(** Open the output selector before folding.  In particular we do not pass
    Bool:U1 to the raw carrier's X:U0 argument, nor use eta conversion. *)
Definition is_atom (t : tag) := close
  (nlams [(0, C); (90, NSort 0); (91, NVar 90); (92, NVar 90)]
    (napps (NVar 0) ([NVar 90] ++
      map (fun u => NVar (if Nat.eqb (IC.tag_number t) (IC.tag_number u)
        then 91 else 92)) IC.tags ++
      [nlams [(201, NVar 90); (202, NVar 90)] (NVar 92)])))
  (ltac:(destruct t; reflexivity)).
Theorem is_atom_typed t : Typed ε (is_atom t) (Arrow IC.carrier BT.boolean).
Proof. destruct t; RkCheck.certify_with 256. Qed.

Definition conjunction := close
  (nlams [(0, B); (1, B); (90, NSort 0); (91, NVar 90); (92, NVar 90)]
    (napps (NVar 0) [NVar 90;
      napps (NVar 1) [NVar 90; NVar 91; NVar 92]; NVar 92])) eq_refl.
Theorem conjunction_typed : Typed ε conjunction
  (Arrow BT.boolean (Arrow BT.boolean BT.boolean)).
Proof. RkCheck.certify_with 128. Qed.

Definition predicate := nArrow C (nArrow C (NSort 1)).
Definition predicate_at x y := napps (NVar 200) [x; y].
Definition atom_case t := NPi 201 C (predicate_at (NClosed (IC.atom t)) (NVar 201)).
Definition pair_atom_case t := npis [(201, C); (202, C)]
  (predicate_at (Pair (NVar 201) (NVar 202)) (NClosed (IC.atom t))).
Definition pair_pair_case := npis [(201, C); (202, C); (203, C); (204, C)]
  (nArrow (predicate_at (NVar 201) (NVar 203))
    (nArrow (predicate_at (NVar 202) (NVar 204))
      (predicate_at (Pair (NVar 201) (NVar 202)) (Pair (NVar 203) (NVar 204))))).
Definition fields := [(200, predicate)] ++
  map (fun t => (300 + IC.tag_number t, atom_case t)) IC.tags ++
  map (fun t => (400 + IC.tag_number t, pair_atom_case t)) IC.tags ++
  [(205, pair_pair_case)].
Definition use_zip g := napps g ([NVar 200] ++
  map (fun t => NVar (300 + IC.tag_number t)) IC.tags ++
  map (fun t => NVar (400 + IC.tag_number t)) IC.tags ++ [NVar 205]).
Definition zip := close (nlams [(0, C); (1, C)]
  (npis fields (predicate_at (NVar 0) (NVar 1)))) eq_refl.
Definition Zip x y := napps (NClosed zip) [x; y].
Definition zip_at {n} (x y : Term nat n) := app (app (lift_closed zip) x) y.
Definition pair_at {n} (x y : Term nat n) := app (app (lift_closed IC.pair) x) y.
Theorem zip_sorted : Typed ε zip (Arrow IC.carrier (Arrow IC.carrier (𝓤 4))).
Proof. RkCheck.certify_with 1024. Qed.

Definition atom_zip_type t := close
  (NPi 1 C (Zip (NClosed (IC.atom t)) (NVar 1)))
  (ltac:(destruct t; reflexivity)).
Definition atom_zip t := close
  (nlams ([(1, C)] ++ fields)
    (NApp (NVar (300 + IC.tag_number t)) (NVar 1)))
  (ltac:(destruct t; reflexivity)).
Theorem atom_zip_typed t : Typed ε (atom_zip t) (atom_zip_type t).
Proof. destruct t; RkCheck.certify_with 1024. Qed.

Definition pair_atom_zip_type t := close
  (npis [(0, C); (1, C)]
    (Zip (Pair (NVar 0) (NVar 1)) (NClosed (IC.atom t))))
  (ltac:(destruct t; reflexivity)).
Definition pair_atom_zip t := close
  (nlams ([(0, C); (1, C)] ++ fields)
    (napps (NVar (400 + IC.tag_number t)) [NVar 0; NVar 1]))
  (ltac:(destruct t; reflexivity)).
Theorem pair_atom_zip_typed t : Typed ε (pair_atom_zip t) (pair_atom_zip_type t).
Proof. destruct t; RkCheck.certify_with 1024. Qed.

Definition pair_pair_fields := [(0, C); (1, C); (2, C); (3, C);
  (4, Zip (NVar 0) (NVar 2)); (5, Zip (NVar 1) (NVar 3))].
Definition pair_pair_zip_type := close (npis pair_pair_fields
  (Zip (Pair (NVar 0) (NVar 1)) (Pair (NVar 2) (NVar 3)))) eq_refl.
Definition pair_pair_zip := close (nlams (pair_pair_fields ++ fields)
  (napps (NVar 205) [NVar 0; NVar 1; NVar 2; NVar 3;
    use_zip (NVar 4); use_zip (NVar 5)])) eq_refl.
Theorem pair_pair_zip_typed : Typed ε pair_pair_zip pair_pair_zip_type.
Proof. RkCheck.certify_with 2048. Qed.

Definition comparison_arguments :=
  [nlams [(201, C); (202, C)] B] ++
  map (fun t => NLam 201 C (NApp (NClosed (is_atom t)) (NVar 201))) IC.tags ++
  map (fun _ : tag => nlams [(201, C); (202, C)] (NClosed (BT.point false))) IC.tags ++
  [nlams [(201, C); (202, C); (203, C); (204, C); (206, B); (207, B)]
    (napps (NClosed conjunction) [NVar 206; NVar 207])].
Definition compare_type := close
  (npis [(0, C); (1, C); (2, Zip (NVar 0) (NVar 1))] B) eq_refl.
Definition compare := close
  (nlams [(0, C); (1, C); (2, Zip (NVar 0) (NVar 1))]
    (napps (NVar 2) comparison_arguments)) eq_refl.
Theorem compare_type_sorted : Typed ε compare_type (𝓤 5).
Proof. RkCheck.certify_with 2048. Qed.
Theorem compare_typed : Typed ε compare compare_type.
Proof. RkCheck.certify_with 2048. Qed.

Definition compare_at {n} (x y g : Term nat n) :=
  app (app (app (lift_closed compare) x) y) g.
Definition conjunction_at {n} (x y : Term nat n) :=
  app (app (lift_closed conjunction) x) y.

(** Open computational equations can be instantiated using original
    replacement/conversion congruence, including at untyped arguments. *)
Theorem is_atom_atom_beta t u :
  app (is_atom t) (IC.atom u) =ᵝ
    BT.point (Nat.eqb (IC.tag_number t) (IC.tag_number u)).
Proof. destruct t, u; apply (RkEval.convert_equal_sound 256); vm_compute; reflexivity. Qed.

Theorem conjunction_beta b c :
  conjunction_at (BT.point b) (BT.point c) =ᵝ BT.point (andb b c).
Proof. destruct b, c; apply (RkEval.convert_equal_sound 128); vm_compute; reflexivity. Qed.

Theorem is_atom_pair_schema t :
  app (@lift_closed 2 (is_atom t)) (pair_at (var (fsucc fzero)) (var fzero))
    =ᵝ lift_closed (BT.point false).
Proof. destruct t; apply (RkEval.convert_equal_sound 256); vm_compute; reflexivity. Qed.

Theorem compare_atom_schema t :
  compare_at (@lift_closed 1 (IC.atom t)) (var fzero)
    (app (lift_closed (atom_zip t)) (var fzero))
    =ᵝ app (lift_closed (is_atom t)) (var fzero).
Proof. destruct t; apply (RkEval.convert_equal_sound 2048); vm_compute; reflexivity. Qed.

Theorem compare_pair_atom_schema t :
  compare_at (pair_at (var (fsucc fzero)) (var fzero)) (@lift_closed 2 (IC.atom t))
    (app (app (lift_closed (pair_atom_zip t)) (var (fsucc fzero))) (var fzero))
    =ᵝ lift_closed (BT.point false).
Proof. destruct t; apply (RkEval.convert_equal_sound 2048); vm_compute; reflexivity. Qed.

Definition v0 : Term nat 6 := var fzero.
Definition v1 : Term nat 6 := var (fsucc fzero).
Definition v2 : Term nat 6 := var (fsucc (fsucc fzero)).
Definition v3 : Term nat 6 := var (fsucc (fsucc (fsucc fzero))).
Definition v4 : Term nat 6 := var (fsucc (fsucc (fsucc (fsucc fzero)))).
Definition v5 : Term nat 6 := var (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).
Theorem compare_pair_pair_schema :
  compare_at (pair_at v5 v4) (pair_at v3 v2)
    (app (app (app (app (app (app (lift_closed pair_pair_zip) v5) v4) v3) v2) v1) v0)
    =ᵝ conjunction_at (compare_at v5 v3 v1) (compare_at v4 v2 v0).
Proof. apply (RkEval.convert_equal_sound 2048); vm_compute; reflexivity. Qed.

End InternalCodeComparison.
