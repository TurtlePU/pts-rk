(** Forward simulation of resource lookup by concrete structural operations.
    Open the target relation before folding the source: the SAME motive rank
    suffices, and no constructor inversion or functionality is used.
    No converse or injectivity is claimed; shape/plug can identify or add
    resource structure.
    They do not assert preservation of the encoded PTS typing judgment. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalPaths LookupHistory InternalCapacity.
Import ListNotations.

Module LookupHomomorphisms.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalPaths.InternalPaths
  LookupHistory.LookupHistory InternalCapacity.InternalCapacity.

(** These are assembler templates, not an assumed homomorphism axiom.
    Each public term below uses one of the two concrete operations, whose
    pairing equations hold by literal beta conversion. *)
Definition mapped_motive (f : named -> named) :=
  nlams [(11, C); (18, C); (19, C)]
    (R (f (NVar 11)) (NVar 18) (f (NVar 19))).
Definition mapped_root (f : named -> named) (guard : named -> named -> named) :=
  nlams [(11, C); (16, G (NVar 11))]
    (napps (NVar 31) [f (NVar 11); guard (NVar 11) (NVar 16)]).
Definition mapped_step (f : named -> named) (guard : named -> named -> named)
  (left : bool) := nlams
  [(11, C); (12, C); (18, C); (19, C);
   (16, G (NVar (if left then 12 else 11)));
   (17, R (f (NVar (if left then 11 else 12))) (NVar 18) (f (NVar 19)))]
  (napps (NVar (if left then 32 else 33))
    [f (NVar 11); f (NVar 12); NVar 18; f (NVar 19);
     guard (NVar (if left then 12 else 11)) (NVar 16); NVar 17]).
Definition mapped_fold (f : named -> named) (guard : named -> named -> named) :=
  napps (NVar 3) [mapped_motive f; mapped_root f guard;
    mapped_step f guard true; mapped_step f guard false].
Definition shape_generation x gx := napps (NClosed shape_guard) [x; gx].
Definition fill x := Plug x (NVar 6).
Definition fill_generation x gx :=
  napps (NClosed plug_guard) [x; NVar 6; gx; NVar 7].
Definition fill_arguments := [(6, C); (7, G (NVar 6))].
Definition low_arguments := [(0, C); (1, C); (2, C);
  (3, Look (NVar 0) (NVar 1) (NVar 2))].
Definition high_arguments := [(0, C); (1, C); (2, C);
  (3, High (NVar 0) (NVar 1) (NVar 2))].

Definition shape_lookup_type := close (npis low_arguments
  (Look (Sh (NVar 0)) (NVar 1) (Sh (NVar 2)))) Logic.eq_refl.
Definition shape_lookup := close (nlams (low_arguments ++ lookup_fields)
  (mapped_fold Sh shape_generation)) Logic.eq_refl.
Theorem shape_lookup_type_sorted : Typed ε shape_lookup_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.
Theorem shape_lookup_typed : Typed ε shape_lookup shape_lookup_type.
Proof. RkCheck.certify_with 512. Qed.

Definition plug_lookup_type := close (npis (low_arguments ++ fill_arguments)
  (Look (fill (NVar 0)) (NVar 1) (fill (NVar 2)))) Logic.eq_refl.
Definition plug_lookup := close
  (nlams (low_arguments ++ fill_arguments ++ lookup_fields)
    (mapped_fold fill fill_generation)) Logic.eq_refl.
Theorem plug_lookup_type_sorted : Typed ε plug_lookup_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.
Theorem plug_lookup_typed : Typed ε plug_lookup plug_lookup_type.
Proof. RkCheck.certify_with 512. Qed.

(** The same construction independently preserves Look_6.  It neither
    lifts Look_5 proofs nor changes either relation's local rules. *)
Definition shape_high_type := close (npis high_arguments
  (High (Sh (NVar 0)) (NVar 1) (Sh (NVar 2)))) Logic.eq_refl.
Definition shape_high := close (nlams (high_arguments ++ high_fields)
  (mapped_fold Sh shape_generation)) Logic.eq_refl.
Theorem shape_high_type_sorted : Typed ε shape_high_type (𝓤 9).
Proof. RkCheck.certify_with 512. Qed.
Theorem shape_high_typed : Typed ε shape_high shape_high_type.
Proof. RkCheck.certify_with 512. Qed.

Definition plug_high_type := close (npis (high_arguments ++ fill_arguments)
  (High (fill (NVar 0)) (NVar 1) (fill (NVar 2)))) Logic.eq_refl.
Definition plug_high := close
  (nlams (high_arguments ++ fill_arguments ++ high_fields)
    (mapped_fold fill fill_generation)) Logic.eq_refl.
Theorem plug_high_type_sorted : Typed ε plug_high_type (𝓤 9).
Proof. RkCheck.certify_with 512. Qed.
Theorem plug_high_typed : Typed ε plug_high plug_high_type.
Proof. RkCheck.certify_with 512. Qed.

(** Map each history segment while retaining its path.  Each independent
    Look_6 segment uses the ACTUAL terms above; fold at unchanged U7. *)
Definition history_arguments := [(0, C); (1, C); (2, C);
  (3, Hist (NVar 0) (NVar 1) (NVar 2))].
Definition mapped_segment (f : named -> named)
  (segment : named -> named -> named -> named -> named) := nlams
  [(11, C); (18, C); (12, C); (19, C); (20, C);
   (16, High (NVar 11) (NVar 18) (NVar 12));
   (17, R (f (NVar 12)) (NVar 19) (f (NVar 20)))]
  (napps (NVar 32) [f (NVar 11); NVar 18; f (NVar 12); NVar 19;
    f (NVar 20); segment (NVar 11) (NVar 18) (NVar 12) (NVar 16); NVar 17]).
Definition mapped_history (f : named -> named) (guard : named -> named -> named)
  (segment : named -> named -> named -> named -> named) :=
  napps (NVar 3) [mapped_motive f; mapped_root f guard; mapped_segment f segment].
Definition shape_segment a p v h := napps (NClosed shape_high) [a; p; v; h].
Definition fill_segment a p v h := napps (NClosed plug_high)
  [a; p; v; h; NVar 6; NVar 7].

Definition shape_history_type := close (npis history_arguments
  (Hist (Sh (NVar 0)) (NVar 1) (Sh (NVar 2)))) Logic.eq_refl.
Definition shape_history := close (nlams (history_arguments ++ history_fields)
  (mapped_history Sh shape_generation shape_segment)) Logic.eq_refl.
Theorem shape_history_type_sorted : Typed ε shape_history_type (𝓤 11).
Proof. RkCheck.certify_with 1024. Qed.
Theorem shape_history_typed : Typed ε shape_history shape_history_type.
Proof. RkCheck.certify_with 1024. Qed.

Definition plug_history_type := close (npis (history_arguments ++ fill_arguments)
  (Hist (fill (NVar 0)) (NVar 1) (fill (NVar 2)))) Logic.eq_refl.
Definition plug_history := close
  (nlams (history_arguments ++ fill_arguments ++ history_fields)
    (mapped_history fill fill_generation fill_segment)) Logic.eq_refl.
Theorem plug_history_type_sorted : Typed ε plug_history_type (𝓤 11).
Proof. RkCheck.certify_with 1024. Qed.
Theorem plug_history_typed : Typed ε plug_history plug_history_type.
Proof. RkCheck.certify_with 1024. Qed.
End LookupHomomorphisms.
