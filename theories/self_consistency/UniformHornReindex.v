(** Uniform, proof-preserving restriction of represented Horn fragments.
    Source clauses S(d) select target clauses by an internally supplied map
    g(d,-).  Their premise positions and atom endpoints are LITERAL pullbacks
    along that map.  Thus transport needs no equality, model, source typing,
    membership or desired soundness premise.  It does not establish original
    PTS-to-catalogue completeness or construction of a model interpretation.

    Both exact atom-rank interfaces 1 and 2 are certified.  Source proof
    fibers have rank 4 and the transport's full type has rank 5.  All other
    carrier fibers have exact rank 1; no cumulativity or eta rule is used. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import NamedTemplates NamedBeta UniformHorn.
Import ListNotations.

Module UniformHornReindex.
Import CommonCodes Core Structural.
Module UH := UniformHorn.UniformHorn.
Module NT := NamedTemplates.NamedTemplates.
Module NB := NamedBeta.NamedBeta.

Definition SourceClauses d := NApp (NVar 6) d.
Definition Selected d s := napps (NVar 7) [d; s].
Definition restriction_fields := [(6, nArrow UH.D (NSort 1));
  (7, npis [(10, UH.D); (40, SourceClauses (NVar 10))]
    (UH.Clauses (NVar 10)))].
Definition interface_fields atom_rank := UH.interface_fields atom_rank ++
  restriction_fields.
Definition SourcePrem X d s := UH.Prem X d (Selected d s).
Definition SourceHandler X d := NPi 40 (SourceClauses d)
  (nArrow (SourcePrem X d (NVar 40))
    (NApp X (UH.Head d (Selected d (NVar 40))))).
Definition source_proof_fields d :=
  [(20, UH.Assignment); (21, SourceHandler (NVar 20) d)].
Definition SourceProof d q := npis (source_proof_fields d) (NApp (NVar 20) q).

Definition handler_fields atom_rank := interface_fields atom_rank ++
  [(10, UH.D); (20, UH.Assignment)].
Definition handler_type atom_rank := close
  (npis (handler_fields atom_rank) (NSort 3)) eq_refl.
Definition handler atom_rank := close (nlams (handler_fields atom_rank)
  (SourceHandler (NVar 20) (NVar 10))) eq_refl.
Definition family_fields atom_rank := interface_fields atom_rank ++
  [(10, UH.D); (13, UH.A)].
Definition family_type atom_rank := close
  (npis (family_fields atom_rank) (NSort 4)) eq_refl.
Definition family atom_rank := close (nlams (family_fields atom_rank)
  (SourceProof (NVar 10) (NVar 13))) eq_refl.

Theorem handler_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (handler atom_rank) (handler_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 512. Qed.
Theorem family_type_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (family_type atom_rank) (𝓤 3).
Proof. intros [-> | ->]; RkCheck.certify_with 512. Qed.
Theorem family_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (family atom_rank) (family_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 512. Qed.

(** The handler supplied to the source proof merely selects a target clause.
    In particular, no target proof or truth value is stored in a source rule. *)
Definition transport_fields atom_rank := family_fields atom_rank ++
  [(32, SourceProof (NVar 10) (NVar 13))].
Definition restricted_handler := nlams
  [(40, SourceClauses (NVar 10));
   (41, SourcePrem (NVar 20) (NVar 10) (NVar 40))]
  (napps (NVar 21) [Selected (NVar 10) (NVar 40); NVar 41]).
Definition transport_body := napps (NVar 32) [NVar 20; restricted_handler].
Definition transport_type atom_rank := close (npis (transport_fields atom_rank)
  (UH.Proof (NVar 10) (NVar 13))) eq_refl.
Definition transport atom_rank := close (nlams
  (transport_fields atom_rank ++ UH.proof_fields (NVar 10)) transport_body) eq_refl.
Theorem transport_type_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (transport_type atom_rank) (𝓤 5).
Proof. intros [-> | ->]; RkCheck.certify_with 1024. Qed.
Theorem transport_typed atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (transport atom_rank) (transport_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 1024. Qed.

(** All application laws permit arbitrary original contexts and open source
    proofs, not only externally generated canonical proofs. *)
Theorem family_application {n} (G : Ctx nat n) atom_rank e xs final :
  atom_rank = 1 \/ atom_rank = 2 ->
  NB.NamedSpine G (family_fields atom_rank) e xs final ->
  Typed G (NB.apply_spine (lift_closed (family atom_rank)) xs) (𝓤 4).
Proof.
  intros Hr Hs; eapply (NB.named_spine_application G (family_fields atom_rank)
    e xs final (NSort 4)); [exact Hs | | reflexivity |].
  - exact (NT.evaluate_close (npis (family_fields atom_rank) (NSort 4)) eq_refl n e).
  - apply lift_closed_typed, family_sorted, Hr.
Qed.
Theorem family_beta {n} (G : Ctx nat n) atom_rank e xs final r :
  NB.NamedSpine G (family_fields atom_rank) e xs final ->
  NT.evaluate (SourceProof (NVar 10) (NVar 13)) final = Some r ->
  NB.apply_spine (lift_closed (family atom_rank)) xs =ᵝ r.
Proof.
  intros Hs Hr; eapply UH.named_spine_beta; [exact Hs | | exact Hr].
  exact (NT.evaluate_close (nlams (family_fields atom_rank)
    (SourceProof (NVar 10) (NVar 13))) eq_refl n e).
Qed.
Theorem transport_application {n} (G : Ctx nat n) atom_rank e xs final r :
  atom_rank = 1 \/ atom_rank = 2 ->
  NB.NamedSpine G (transport_fields atom_rank) e xs final ->
  NT.evaluate (UH.Proof (NVar 10) (NVar 13)) final = Some r ->
  Typed G (NB.apply_spine (lift_closed (transport atom_rank)) xs) r.
Proof.
  intros Hr Hs HE; eapply (NB.named_spine_application G (transport_fields atom_rank)
    e xs final (UH.Proof (NVar 10) (NVar 13))); [exact Hs | | exact HE |].
  - exact (NT.evaluate_close (npis (transport_fields atom_rank)
      (UH.Proof (NVar 10) (NVar 13))) eq_refl n e).
  - apply lift_closed_typed, transport_typed, Hr.
Qed.
Theorem transport_beta {n} (G : Ctx nat n) atom_rank e xs final r :
  NB.NamedSpine G (transport_fields atom_rank ++ UH.proof_fields (NVar 10))
    e xs final ->
  NT.evaluate transport_body final = Some r ->
  NB.apply_spine (lift_closed (transport atom_rank)) xs =ᵝ r.
Proof.
  intros Hs Hr; eapply UH.named_spine_beta; [exact Hs | | exact Hr].
  exact (NT.evaluate_close (nlams
    (transport_fields atom_rank ++ UH.proof_fields (NVar 10)) transport_body)
    eq_refl n e).
Qed.

(** Interpretation after transport is the original proof interpreted with
    the selected handler.  This is a concrete beta equation under all
    interface binders, not a general eta identity for arbitrary proofs. *)
Definition fold_fields atom_rank := transport_fields atom_rank ++
  UH.proof_fields (NVar 10).
Definition fold_type atom_rank := close (npis (fold_fields atom_rank)
  (NApp (NVar 20) (NVar 13))) eq_refl.
Definition fold_left atom_rank := close (nlams (fold_fields atom_rank)
  (napps (NClosed (transport atom_rank))
    (UH.interface_arguments ++
      [NVar 6; NVar 7; NVar 10; NVar 13; NVar 32; NVar 20; NVar 21]))) eq_refl.
Definition fold_right atom_rank := close
  (nlams (fold_fields atom_rank) transport_body) eq_refl.
Theorem fold_left_typed atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (fold_left atom_rank) (fold_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 2048. Qed.
Theorem fold_right_typed atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (fold_right atom_rank) (fold_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 1024. Qed.
Theorem fold_beta atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  fold_left atom_rank =ᵝ fold_right atom_rank.
Proof.
  intros [-> | ->]; eapply RkCheck.check_conv_sound with (fuel := 2048);
    vm_compute; reflexivity.
Qed.

(** Restriction composes by beta reduction.  The intermediate interface is
    itself a literal pullback, and both sides use the actual transport term.
    No injectivity or surjectivity of either selector is required. *)
Definition DeepClauses d := NApp (NVar 8) d.
Definition SelectedAgain d t := napps (NVar 9) [d; t].
Definition Composite d t := Selected d (SelectedAgain d t).
Definition composite_map := nlams [(10, UH.D); (42, DeepClauses (NVar 10))]
  (Composite (NVar 10) (NVar 42)).
Definition DeepHandler X d := NPi 42 (DeepClauses d)
  (nArrow (UH.Prem X d (Composite d (NVar 42)))
    (NApp X (UH.Head d (Composite d (NVar 42))))).
Definition DeepProof d q := npis
  [(20, UH.Assignment); (21, DeepHandler (NVar 20) d)] (NApp (NVar 20) q).
Definition source_positions := nlams
  [(10, UH.D); (40, SourceClauses (NVar 10))]
  (UH.Positions (NVar 10) (Selected (NVar 10) (NVar 40))).
Definition source_premise := nlams
  [(10, UH.D); (40, SourceClauses (NVar 10));
   (12, UH.Positions (NVar 10) (Selected (NVar 10) (NVar 40)))]
  (UH.Premise (NVar 10) (Selected (NVar 10) (NVar 40)) (NVar 12)).
Definition source_head := nlams
  [(10, UH.D); (40, SourceClauses (NVar 10))]
  (UH.Head (NVar 10) (Selected (NVar 10) (NVar 40))).
Definition source_interface_arguments :=
  [NVar 0; NVar 1; NVar 6; source_positions; source_premise; source_head].
Definition composition_fields atom_rank := interface_fields atom_rank ++
  [(8, nArrow UH.D (NSort 1));
   (9, npis [(10, UH.D); (42, DeepClauses (NVar 10))]
     (SourceClauses (NVar 10)));
   (10, UH.D); (13, UH.A); (32, DeepProof (NVar 10) (NVar 13))].
Definition composition_type atom_rank := close (npis (composition_fields atom_rank)
  (UH.Proof (NVar 10) (NVar 13))) eq_refl.
Definition composition_left atom_rank := close (nlams (composition_fields atom_rank)
  (napps (NClosed (transport atom_rank)) (UH.interface_arguments ++
    [NVar 6; NVar 7; NVar 10; NVar 13;
      napps (NClosed (transport atom_rank)) (source_interface_arguments ++
        [NVar 8; NVar 9; NVar 10; NVar 13; NVar 32])]))) eq_refl.
Definition composition_right atom_rank := close (nlams (composition_fields atom_rank)
  (napps (NClosed (transport atom_rank)) (UH.interface_arguments ++
    [NVar 8; composite_map; NVar 10; NVar 13; NVar 32]))) eq_refl.
Theorem composition_type_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (composition_type atom_rank) (𝓤 5).
Proof. intros [-> | ->]; RkCheck.certify_with 1024. Qed.
Theorem composition_left_typed atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (composition_left atom_rank) (composition_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 4096. Qed.
Theorem composition_right_typed atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (composition_right atom_rank) (composition_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 2048. Qed.
Theorem composition_beta atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  composition_left atom_rank =ᵝ composition_right atom_rank.
Proof.
  intros [-> | ->]; eapply RkCheck.check_conv_sound with (fuel := 4096);
    vm_compute; reflexivity.
Qed.

End UniformHornReindex.
