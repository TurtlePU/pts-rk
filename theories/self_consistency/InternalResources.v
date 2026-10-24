(** Fixed-rank ORIGINAL PTS resource relations, specified by local closure
    alone. These do not assert checker soundness or budget sufficiency. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier.
Import ListNotations.

Module InternalResources.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier.
Definition C := NClosed carrier.
Definition G x := NApp (NClosed good) x.
Definition node x y := napps (NClosed pair) [x; y].
Definition stop := NClosed (atom NZero).
Definition left_path p := node (NClosed (atom PEven)) p.
Definition right_path p := node (NClosed (atom POdd)) p.

(** Fixed-rank predicate transport gives transitivity by composition, with
    no stronger induction motive and no transitivity axiom among the rules. *)
Definition growth_left := npis [(11, C); (12, C)]
  (nArrow (G (NVar 12)) (nArrow (NApp (NVar 10) (NVar 11))
    (NApp (NVar 10) (node (NVar 11) (NVar 12))))).
Definition growth_right := npis [(11, C); (12, C)]
  (nArrow (G (NVar 11)) (nArrow (NApp (NVar 10) (NVar 12))
    (NApp (NVar 10) (node (NVar 11) (NVar 12))))).
Definition growth_fields := [(10, nArrow C (NSort 4));
  (13, growth_left); (14, growth_right)].
Definition prefix_fields := [(10, nArrow C (NSort 4)); (13, growth_left)].
Definition extension := close
  (nlams [(0, C); (1, C)] (npis growth_fields
    (nArrow (NApp (NVar 10) (NVar 0)) (NApp (NVar 10) (NVar 1))))) eq_refl.
Definition prefix := close
  (nlams [(0, C); (1, C)] (npis prefix_fields
    (nArrow (NApp (NVar 10) (NVar 0)) (NApp (NVar 10) (NVar 1))))) eq_refl.
Definition Ext x y := napps (NClosed extension) [x; y].
Definition Pre x y := napps (NClosed prefix) [x; y].
Theorem extension_sorted : Typed ε extension (Arrow carrier (Arrow carrier (𝓤 6))).
Proof. RkCheck.certify_with 256. Qed.
Theorem prefix_sorted : Typed ε prefix (Arrow carrier (Arrow carrier (𝓤 6))).
Proof. RkCheck.certify_with 256. Qed.

Definition extension_refl_type := close (NPi 0 C (Ext (NVar 0) (NVar 0))) eq_refl.
Definition extension_refl := close
  (nlams ([(0, C)] ++ growth_fields ++ [(15, NApp (NVar 10) (NVar 0))])
    (NVar 15)) eq_refl.
Definition extension_trans_type := close
  (npis [(0, C); (1, C); (2, C); (3, Ext (NVar 0) (NVar 1));
    (4, Ext (NVar 1) (NVar 2))] (Ext (NVar 0) (NVar 2))) eq_refl.
Definition extension_trans := close
  (nlams ([(0, C); (1, C); (2, C); (3, Ext (NVar 0) (NVar 1));
    (4, Ext (NVar 1) (NVar 2))] ++ growth_fields ++
    [(15, NApp (NVar 10) (NVar 0))])
    (napps (NVar 4) [NVar 10; NVar 13; NVar 14;
      napps (NVar 3) [NVar 10; NVar 13; NVar 14; NVar 15]])) eq_refl.
Definition join_left_type := close
  (npis [(0, C); (1, C); (2, G (NVar 1))]
    (Ext (NVar 0) (node (NVar 0) (NVar 1)))) eq_refl.
Definition join_left := close
  (nlams ([(0, C); (1, C); (2, G (NVar 1))] ++ growth_fields ++
    [(15, NApp (NVar 10) (NVar 0))])
    (napps (NVar 13) [NVar 0; NVar 1; NVar 2; NVar 15])) eq_refl.
Definition join_right_type := close
  (npis [(0, C); (1, C); (2, G (NVar 0))]
    (Ext (NVar 1) (node (NVar 0) (NVar 1)))) eq_refl.
Definition join_right := close
  (nlams ([(0, C); (1, C); (2, G (NVar 0))] ++ growth_fields ++
    [(15, NApp (NVar 10) (NVar 1))])
    (napps (NVar 14) [NVar 0; NVar 1; NVar 2; NVar 15])) eq_refl.
Theorem extension_refl_typed : Typed ε extension_refl extension_refl_type.
Proof. RkCheck.certify_with 256. Qed.
Theorem extension_trans_typed : Typed ε extension_trans extension_trans_type.
Proof. RkCheck.certify_with 256. Qed.
Theorem extension_trans_sorted : Typed ε extension_trans_type (𝓤 7).
Proof. RkCheck.certify_with 256. Qed.
Theorem join_left_typed : Typed ε join_left join_left_type.
Proof. RkCheck.certify_with 256. Qed.
Theorem join_right_typed : Typed ε join_right join_right_type.
Proof. RkCheck.certify_with 256. Qed.

Definition prefix_refl_type := close (NPi 0 C (Pre (NVar 0) (NVar 0))) eq_refl.
Definition prefix_refl := close
  (nlams ([(0, C)] ++ prefix_fields ++ [(15, NApp (NVar 10) (NVar 0))])
    (NVar 15)) eq_refl.
Definition prefix_step_type := close
  (npis [(0, C); (1, C); (2, G (NVar 1))]
    (Pre (NVar 0) (node (NVar 0) (NVar 1)))) eq_refl.
Definition prefix_step := close
  (nlams ([(0, C); (1, C); (2, G (NVar 1))] ++ prefix_fields ++
    [(15, NApp (NVar 10) (NVar 0))])
    (napps (NVar 13) [NVar 0; NVar 1; NVar 2; NVar 15])) eq_refl.
Definition prefix_trans_type := close
  (npis [(0, C); (1, C); (2, C); (3, Pre (NVar 0) (NVar 1));
    (4, Pre (NVar 1) (NVar 2))] (Pre (NVar 0) (NVar 2))) eq_refl.
Definition prefix_trans := close
  (nlams ([(0, C); (1, C); (2, C); (3, Pre (NVar 0) (NVar 1));
    (4, Pre (NVar 1) (NVar 2))] ++ prefix_fields ++
    [(15, NApp (NVar 10) (NVar 0))])
    (napps (NVar 4) [NVar 10; NVar 13;
      napps (NVar 3) [NVar 10; NVar 13; NVar 15]])) eq_refl.
Definition prefix_extension_type := close
  (npis [(0, C); (1, C); (2, Pre (NVar 0) (NVar 1))]
    (Ext (NVar 0) (NVar 1))) eq_refl.
Definition prefix_extension := close
  (nlams ([(0, C); (1, C); (2, Pre (NVar 0) (NVar 1))] ++ growth_fields ++
    [(15, NApp (NVar 10) (NVar 0))])
    (napps (NVar 2) [NVar 10; NVar 13; NVar 15])) eq_refl.
Theorem prefix_refl_typed : Typed ε prefix_refl prefix_refl_type.
Proof. RkCheck.certify_with 256. Qed.
Theorem prefix_step_typed : Typed ε prefix_step prefix_step_type.
Proof. RkCheck.certify_with 256. Qed.
Theorem prefix_trans_typed : Typed ε prefix_trans prefix_trans_type.
Proof. RkCheck.certify_with 256. Qed.
Theorem prefix_extension_typed : Typed ε prefix_extension prefix_extension_type.
Proof. RkCheck.certify_with 256. Qed.

Definition good_left := nlams [(11, C); (12, C); (16, G (NVar 12)); (17, G (NVar 11))]
  (napps (NClosed good_pair) [NVar 11; NVar 12; NVar 17; NVar 16]).
Definition good_right := nlams [(11, C); (12, C); (16, G (NVar 11)); (17, G (NVar 12))]
  (napps (NClosed good_pair) [NVar 11; NVar 12; NVar 16; NVar 17]).
Definition extension_generation_type := close
  (npis [(0, C); (1, C); (2, Ext (NVar 0) (NVar 1)); (3, G (NVar 0))]
    (G (NVar 1))) eq_refl.
Definition extension_generation := close
  (nlams [(0, C); (1, C); (2, Ext (NVar 0) (NVar 1)); (3, G (NVar 0))]
    (napps (NVar 2) [NClosed good; good_left; good_right; NVar 3])) eq_refl.
Theorem extension_generation_typed : Typed ε extension_generation extension_generation_type.
Proof. RkCheck.certify_with 512. Qed.

(** Lookup is independently specified by root/left/right rules at motive
    rank 5. Good siblings and the Good root leaf are structural guards. *)
Definition R a p v := napps (NVar 30) [a; p; v].
Definition root_rule := npis [(11, C); (16, G (NVar 11))]
  (R (NVar 11) stop (NVar 11)).
Definition left_rule := npis [(11, C); (12, C); (18, C); (19, C);
  (16, G (NVar 12)); (17, R (NVar 11) (NVar 18) (NVar 19))]
  (R (node (NVar 11) (NVar 12)) (left_path (NVar 18)) (NVar 19)).
Definition right_rule := npis [(11, C); (12, C); (18, C); (19, C);
  (16, G (NVar 11)); (17, R (NVar 12) (NVar 18) (NVar 19))]
  (R (node (NVar 11) (NVar 12)) (right_path (NVar 18)) (NVar 19)).
Definition lookup_fields := [(30, nArrow C (nArrow C (nArrow C (NSort 5))));
  (31, root_rule); (32, left_rule); (33, right_rule)].
Definition lookup := close (nlams [(0, C); (1, C); (2, C)]
  (npis lookup_fields (R (NVar 0) (NVar 1) (NVar 2)))) eq_refl.
Definition Look a p v := napps (NClosed lookup) [a; p; v].
Theorem lookup_sorted : Typed ε lookup
  (Arrow carrier (Arrow carrier (Arrow carrier (𝓤 7)))).
Proof. RkCheck.certify_with 512. Qed.

Definition lookup_root_type := close
  (npis [(0, C); (3, G (NVar 0))] (Look (NVar 0) stop (NVar 0))) eq_refl.
Definition lookup_root := close
  (nlams ([(0, C); (3, G (NVar 0))] ++ lookup_fields)
    (napps (NVar 31) [NVar 0; NVar 3])) eq_refl.
Definition lookup_step_type (left : bool) := close
  (npis [(0, C); (1, C); (2, C); (3, C);
    (4, G (NVar (if left then 1 else 0)));
    (5, Look (NVar (if left then 0 else 1)) (NVar 2) (NVar 3))]
    (Look (node (NVar 0) (NVar 1))
      ((if left then left_path else right_path) (NVar 2)) (NVar 3)))
  (ltac:(destruct left; reflexivity)).
Definition lookup_step (left : bool) := close
  (nlams ([(0, C); (1, C); (2, C); (3, C);
    (4, G (NVar (if left then 1 else 0)));
    (5, Look (NVar (if left then 0 else 1)) (NVar 2) (NVar 3))] ++ lookup_fields)
    (napps (NVar (if left then 32 else 33)) [NVar 0; NVar 1; NVar 2; NVar 3; NVar 4;
      napps (NVar 5) [NVar 30; NVar 31; NVar 32; NVar 33]]))
  (ltac:(destruct left; reflexivity)).
Theorem lookup_root_typed : Typed ε lookup_root lookup_root_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem lookup_step_typed side : Typed ε (lookup_step side) (lookup_step_type side).
Proof. destruct side; RkCheck.certify_with 512. Qed.
Theorem lookup_step_sorted side : Typed ε (lookup_step_type side) (𝓤 8).
Proof. destruct side; RkCheck.certify_with 512. Qed.

(** EXACT padding, not cumulativity: Unit4 : U4 has the closed inhabitant
    good_atom NZero.  Unit4 -> Good(x) has rank 5 and can be eliminated back
    to Good(x) by supplying that inhabitant. *)
Definition Unit4 := G stop.
Definition unit4 := NClosed (good_atom NZero).
Inductive observation := Root | Path | Value.
Definition observed (o : observation) (a p v : named) :=
  match o with Root => a | Path => p | Value => v end.
Definition padded x := nArrow Unit4 (G x).
Definition guard_motive o := nlams [(11, C); (18, C); (19, C)]
  (padded (observed o (NVar 11) (NVar 18) (NVar 19))).
Definition guard_root o := nlams [(11, C); (16, G (NVar 11)); (40, Unit4)]
  (match o with Path => unit4 | _ => NVar 16 end).
Definition guard_step o (left : bool) :=
  nlams [(11, C); (12, C); (18, C); (19, C);
    (16, G (NVar (if left then 12 else 11)));
    (17, padded (observed o (NVar (if left then 11 else 12)) (NVar 18) (NVar 19)));
    (40, Unit4)]
  (let ih := NApp (NVar 17) (NVar 40) in
   match o with
   | Root => napps (NClosed good_pair) [NVar 11; NVar 12;
       if left then ih else NVar 16; if left then NVar 16 else ih]
   | Path => napps (NClosed good_pair)
       [NClosed (atom (if left then PEven else POdd)); NVar 18;
        NClosed (good_atom (if left then PEven else POdd)); ih]
   | Value => ih
   end).
Definition lookup_guard_type o := close
  (npis [(0, C); (1, C); (2, C); (3, Look (NVar 0) (NVar 1) (NVar 2))]
    (G (observed o (NVar 0) (NVar 1) (NVar 2)))) (ltac:(destruct o; reflexivity)).
Definition lookup_guard o := close
  (nlams [(0, C); (1, C); (2, C); (3, Look (NVar 0) (NVar 1) (NVar 2))]
    (napps (NVar 3) [guard_motive o; guard_root o;
      guard_step o true; guard_step o false; unit4]))
  (ltac:(destruct o; reflexivity)).
Theorem lookup_guard_typed o : Typed ε (lookup_guard o) (lookup_guard_type o).
Proof. destruct o; RkCheck.certify_with 512. Qed.
Theorem lookup_guard_sorted o : Typed ε (lookup_guard_type o) (𝓤 8).
Proof. destruct o; RkCheck.certify_with 512. Qed.

Definition transport_motive := nlams [(11, C); (18, C); (19, C)]
  (nArrow (NApp (NVar 10) (NVar 19)) (NApp (NVar 10) (NVar 11))).
Definition transport_root := nlams [(11, C); (16, G (NVar 11));
  (40, NApp (NVar 10) (NVar 11))] (NVar 40).
Definition transport_step (left : bool) :=
  nlams [(11, C); (12, C); (18, C); (19, C);
    (16, G (NVar (if left then 12 else 11)));
    (17, nArrow (NApp (NVar 10) (NVar 19))
      (NApp (NVar 10) (NVar (if left then 11 else 12))));
    (40, NApp (NVar 10) (NVar 19))]
    (napps (NVar (if left then 13 else 14))
      [NVar 11; NVar 12; NVar 16; NApp (NVar 17) (NVar 40)]).
Definition lookup_extension_type := close
  (npis [(0, C); (1, C); (2, C); (3, Look (NVar 0) (NVar 1) (NVar 2))]
    (Ext (NVar 2) (NVar 0))) eq_refl.
Definition lookup_extension := close
  (nlams ([(0, C); (1, C); (2, C); (3, Look (NVar 0) (NVar 1) (NVar 2))] ++
    growth_fields ++ [(15, NApp (NVar 10) (NVar 2))])
    (napps (NVar 3) [transport_motive; transport_root;
      transport_step true; transport_step false; NVar 15])) eq_refl.
Theorem lookup_extension_typed : Typed ε lookup_extension lookup_extension_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem lookup_extension_sorted : Typed ε lookup_extension_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.

Definition prefix_generation_type := close
  (npis [(0, C); (1, C); (2, Pre (NVar 0) (NVar 1)); (3, G (NVar 0))]
    (G (NVar 1))) eq_refl.
Definition prefix_generation := close
  (nlams [(0, C); (1, C); (2, Pre (NVar 0) (NVar 1)); (3, G (NVar 0))]
    (napps (NClosed extension_generation) [NVar 0; NVar 1;
      napps (NClosed prefix_extension) [NVar 0; NVar 1; NVar 2]; NVar 3])) eq_refl.
Theorem prefix_generation_typed : Typed ε prefix_generation prefix_generation_type.
Proof. RkCheck.certify_with 512. Qed.
End InternalResources.
