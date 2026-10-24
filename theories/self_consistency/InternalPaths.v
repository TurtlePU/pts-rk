(** Structural path substitution and stratified lookup composition.
    All endpoints concern literal ORIGINAL PTS terms. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier InternalResources.
Import ListNotations.

Module InternalPaths.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources.

Definition expanded x := nlams fields (dispatch x).
Definition plug := close
  (nlams ([(0, C); (1, C)] ++ fields)
    (napps (NVar 0) ([NVar 90] ++
      map (fun t => match t with NZero => dispatch (NVar 1)
                    | _ => NVar (100 + tag_number t) end) tags ++ [NVar 91]))) eq_refl.
Definition Plug p q := napps (NClosed plug) [p; q].
Theorem plug_typed : Typed ε plug (Arrow carrier (Arrow carrier carrier)).
Proof. RkCheck.certify_with 256. Qed.

(** This substitutes at EVERY NZero leaf, so it is total on arbitrary raw
    trees. On direction paths it is precisely path concatenation. *)
Definition expansion_guard_type := close
  (npis [(0, C); (1, G (NVar 0))] (G (expanded (NVar 0)))) eq_refl.
Definition expansion_pair := nlams [(201, C); (202, C);
  (203, NApp (NVar 200) (expanded (NVar 201)));
  (204, NApp (NVar 200) (expanded (NVar 202)))]
  (napps (NVar 205) [expanded (NVar 201); expanded (NVar 202); NVar 203; NVar 204]).
Definition expansion_guard := close
  (nlams ([(0, C); (1, G (NVar 0))] ++ guard_fields)
    (napps (NVar 1) ([NLam 206 C (NApp (NVar 200) (expanded (NVar 206)))] ++
      map (fun t => NVar (300 + tag_number t)) tags ++ [expansion_pair]))) eq_refl.
Theorem expansion_guard_typed : Typed ε expansion_guard expansion_guard_type.
Proof. RkCheck.certify_with 512. Qed.

Definition plug_guard_type := close
  (npis [(0, C); (1, C); (2, G (NVar 0)); (3, G (NVar 1))]
    (G (Plug (NVar 0) (NVar 1)))) eq_refl.
Definition plug_pair := nlams [(201, C); (202, C);
  (203, NApp (NVar 200) (Plug (NVar 201) (NVar 1)));
  (204, NApp (NVar 200) (Plug (NVar 202) (NVar 1)))]
  (napps (NVar 205) [Plug (NVar 201) (NVar 1); Plug (NVar 202) (NVar 1);
    NVar 203; NVar 204]).
Definition plug_guard := close
  (nlams ([(0, C); (1, C); (2, G (NVar 0)); (3, G (NVar 1))] ++ guard_fields)
    (napps (NVar 2) ([NLam 206 C (NApp (NVar 200) (Plug (NVar 206) (NVar 1)))] ++
      map (fun t => match t with
        | NZero => use_guard (napps (NClosed expansion_guard) [NVar 1; NVar 3])
        | _ => NVar (300 + tag_number t) end) tags ++ [plug_pair]))) eq_refl.
Theorem plug_guard_typed : Typed ε plug_guard plug_guard_type.
Proof. RkCheck.certify_with 512. Qed.

(** Equality is directed Leibniz transport at EXACT predicate rank 0. *)
Definition Eq x y := NPi 60 (nArrow C (NSort 0))
  (nArrow (NApp (NVar 60) x) (NApp (NVar 60) y)).
Definition equality := close (nlams [(0, C); (1, C)] (Eq (NVar 0) (NVar 1))) eq_refl.
Theorem equality_sorted : Typed ε equality (Arrow carrier (Arrow carrier (𝓤 4))).
Proof. RkCheck.certify_with 256. Qed.
Definition eq_refl x := nlams [(60, nArrow C (NSort 0)); (61, NApp (NVar 60) x)] (NVar 61).
Definition expansion_equal_type := close
  (npis [(0, C); (1, G (NVar 0))] (Eq (expanded (NVar 0)) (NVar 0))) Logic.eq_refl.
Definition expansion_equal := close
  (nlams [(0, C); (1, G (NVar 0)); (60, nArrow C (NSort 0))]
    (napps (NVar 1)
      ([NLam 206 C (nArrow (NApp (NVar 60) (expanded (NVar 206)))
        (NApp (NVar 60) (NVar 206)))] ++
       map (fun t => NLam 61 (NApp (NVar 60) (NClosed (atom t))) (NVar 61)) tags ++
       [nlams [(201, C); (202, C);
         (203, nArrow (NApp (NVar 60) (expanded (NVar 201))) (NApp (NVar 60) (NVar 201)));
         (204, nArrow (NApp (NVar 60) (expanded (NVar 202))) (NApp (NVar 60) (NVar 202)));
         (61, NApp (NVar 60) (node (NVar 201) (NVar 202)))] (NVar 61)]))) Logic.eq_refl.
Theorem expansion_equal_typed : Typed ε expansion_equal expansion_equal_type.
Proof. RkCheck.certify_with 512. Qed.

Definition unit_type (left : bool) := close
  (npis [(0, C); (1, G (NVar 0))]
    (Eq (if left then Plug stop (NVar 0) else Plug (NVar 0) stop) (NVar 0)))
  (ltac:(destruct left; reflexivity)).
Theorem plug_unit_typed side : Typed ε expansion_equal (unit_type side).
Proof. destruct side; RkCheck.certify_with 512. Qed.
Definition associative_type := close
  (npis [(0, C); (1, C); (2, C)]
    (Eq (Plug (Plug (NVar 0) (NVar 1)) (NVar 2))
      (Plug (NVar 0) (Plug (NVar 1) (NVar 2))))) Logic.eq_refl.
Definition associative := close
  (nlams [(0, C); (1, C); (2, C)]
    (eq_refl (Plug (Plug (NVar 0) (NVar 1)) (NVar 2)))) Logic.eq_refl.
Theorem associative_typed : Typed ε associative associative_type.
Proof. RkCheck.certify_with 512. Qed.

(** SAME local lookup rules, a separately declared exact motive rank 6.
    Composition is a theorem below, not a clause of this relation. *)
Definition high_fields := [(30, nArrow C (nArrow C (nArrow C (NSort 6))));
  (31, root_rule); (32, left_rule); (33, right_rule)].
Definition high_lookup := close (nlams [(0, C); (1, C); (2, C)]
  (npis high_fields (R (NVar 0) (NVar 1) (NVar 2)))) Logic.eq_refl.
Definition High a p v := napps (NClosed high_lookup) [a; p; v].
Theorem high_lookup_sorted : Typed ε high_lookup
  (Arrow carrier (Arrow carrier (Arrow carrier (𝓤 8)))).
Proof. RkCheck.certify_with 512. Qed.
Definition high_root_type := close
  (npis [(0, C); (3, G (NVar 0))] (High (NVar 0) stop (NVar 0))) Logic.eq_refl.
Definition high_root := close
  (nlams ([(0, C); (3, G (NVar 0))] ++ high_fields)
    (napps (NVar 31) [NVar 0; NVar 3])) Logic.eq_refl.
Theorem high_root_typed : Typed ε high_root high_root_type.
Proof. RkCheck.certify_with 512. Qed.
Definition high_step_type (left : bool) := close
  (npis [(0, C); (1, C); (2, C); (3, C);
    (4, G (NVar (if left then 1 else 0)));
    (5, High (NVar (if left then 0 else 1)) (NVar 2) (NVar 3))]
    (High (node (NVar 0) (NVar 1))
      ((if left then left_path else right_path) (NVar 2)) (NVar 3)))
  (ltac:(destruct left; reflexivity)).
Definition high_step (left : bool) := close
  (nlams ([(0, C); (1, C); (2, C); (3, C);
    (4, G (NVar (if left then 1 else 0)));
    (5, High (NVar (if left then 0 else 1)) (NVar 2) (NVar 3))] ++ high_fields)
    (napps (NVar (if left then 32 else 33)) [NVar 0; NVar 1; NVar 2; NVar 3; NVar 4;
      napps (NVar 5) [NVar 30; NVar 31; NVar 32; NVar 33]]))
  (ltac:(destruct left; reflexivity)).
Theorem high_step_typed side : Typed ε (high_step side) (high_step_type side).
Proof. destruct side; RkCheck.certify_with 512. Qed.

(** Open the result relation before eliminating the first lookup. Its
    continuation R(value,expand(q),c) -> R(root,plug(p,q),c) has rank 6. *)
Definition composition_arguments := [(0, C); (1, C); (2, C); (3, C); (4, C);
  (5, High (NVar 0) (NVar 1) (NVar 2));
  (6, Look (NVar 2) (NVar 3) (NVar 4))].
Definition composition_type := close (npis composition_arguments
  (Look (NVar 0) (Plug (NVar 1) (NVar 3)) (NVar 4))) Logic.eq_refl.
Definition continuation a p v := nArrow (R v (expanded (NVar 3)) (NVar 4))
  (R a (Plug p (NVar 3)) (NVar 4)).
Definition composition_root := nlams [(11, C); (16, G (NVar 11));
  (40, R (NVar 11) (expanded (NVar 3)) (NVar 4))] (NVar 40).
Definition composition_step (left : bool) := nlams
  [(11, C); (12, C); (18, C); (19, C);
   (16, G (NVar (if left then 12 else 11)));
   (17, continuation (NVar (if left then 11 else 12)) (NVar 18) (NVar 19));
   (40, R (NVar 19) (expanded (NVar 3)) (NVar 4))]
  (napps (NVar (if left then 32 else 33))
    [NVar 11; NVar 12; Plug (NVar 18) (NVar 3); NVar 4; NVar 16;
     NApp (NVar 17) (NVar 40)]).
Definition expanded_step (left : bool) := nlams
  [(11, C); (12, C); (18, C); (19, C);
   (16, G (NVar (if left then 12 else 11)));
   (17, R (NVar (if left then 11 else 12)) (expanded (NVar 18)) (NVar 19))]
  (napps (NVar (if left then 32 else 33))
    [NVar 11; NVar 12; expanded (NVar 18); NVar 19; NVar 16; NVar 17]).
Definition composition := close
  (nlams (composition_arguments ++ lookup_fields)
    (napps (NVar 5)
      [nlams [(11, C); (18, C); (19, C)] (continuation (NVar 11) (NVar 18) (NVar 19));
       composition_root; composition_step true; composition_step false;
       napps (NVar 6)
         [nlams [(11, C); (18, C); (19, C)] (R (NVar 11) (expanded (NVar 18)) (NVar 19));
          NVar 31; expanded_step true; expanded_step false]])) Logic.eq_refl.
Theorem composition_type_sorted : Typed ε composition_type (𝓤 9).
Proof. RkCheck.certify_with 512. Qed.
Theorem composition_typed : Typed ε composition composition_type.
Proof. RkCheck.certify_with 512. Qed.

End InternalPaths.
