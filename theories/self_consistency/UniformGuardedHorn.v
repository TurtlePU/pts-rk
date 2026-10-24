(** Original-PTS Horn closure with an explicit independent clause guard.
    The entire interface, fragment, clause, guard witness and proof are
    object-language arguments.  The positive rule interface contains no
    built-in model or soundness premise.  Its guard must be instantiated
    independently of the desired interpretation, as with finite generation.

    Exact guard ranks 3 and 4 are checked separately, covering the empty
    and nonempty Enum_3 ranks without cumulativity.  Exact atom ranks 1 and
    2 are likewise separate instances.  This module does not construct the
    concrete generation guard, its source coverage, or a model handler. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import NamedTemplates NamedBeta UniformHorn.
Import ListNotations.

Module UniformGuardedHorn.
Import CommonCodes Core Structural.
Module UH := UniformHorn.UniformHorn.
Module NT := NamedTemplates.NamedTemplates.
Module NB := NamedBeta.NamedBeta.

Definition Guard d c := napps (NVar 6) [d; c].
Definition interface_fields atom_rank guard_rank := UH.interface_fields atom_rank ++
  [(6, npis [(10, UH.D); (11, UH.Clauses (NVar 10))] (NSort guard_rank))].
Definition Handler X d := npis
  [(11, UH.Clauses d); (40, Guard d (NVar 11))]
  (nArrow (UH.Prem X d (NVar 11)) (NApp X (UH.Head d (NVar 11)))).
Definition proof_fields d := [(20, UH.Assignment); (21, Handler (NVar 20) d)].
Definition Proof d q := npis (proof_fields d) (NApp (NVar 20) q).

Definition handler_fields atom_rank guard_rank := interface_fields atom_rank guard_rank ++
  [(10, UH.D); (20, UH.Assignment)].
Definition handler_type atom_rank guard_rank := close
  (npis (handler_fields atom_rank guard_rank) (NSort (guard_rank + 1))) eq_refl.
Definition handler atom_rank guard_rank := close
  (nlams (handler_fields atom_rank guard_rank) (Handler (NVar 20) (NVar 10))) eq_refl.
Definition family_fields atom_rank guard_rank := interface_fields atom_rank guard_rank ++
  [(10, UH.D); (13, UH.A)].
Definition family_type atom_rank guard_rank := close
  (npis (family_fields atom_rank guard_rank) (NSort (guard_rank + 2))) eq_refl.
Definition family atom_rank guard_rank := close
  (nlams (family_fields atom_rank guard_rank) (Proof (NVar 10) (NVar 13))) eq_refl.

Theorem handler_sorted a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (handler a g) (handler_type a g).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 512. Qed.
Theorem family_type_sorted a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (family_type a g) (𝓤 3).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 512. Qed.
Theorem family_sorted a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (family a g) (family_type a g).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 512. Qed.

Definition Children d c := NPi 12 (UH.Positions d c)
  (Proof d (UH.Premise d c (NVar 12))).
Definition node_fields atom_rank guard_rank := interface_fields atom_rank guard_rank ++
  [(10, UH.D); (11, UH.Clauses (NVar 10));
   (40, Guard (NVar 10) (NVar 11)); (22, Children (NVar 10) (NVar 11))].
Definition node_type atom_rank guard_rank := close
  (npis (node_fields atom_rank guard_rank)
    (Proof (NVar 10) (UH.Head (NVar 10) (NVar 11)))) eq_refl.
Definition node_body := napps (NVar 21)
  [NVar 11; NVar 40; NLam 12 (UH.Positions (NVar 10) (NVar 11))
    (napps (NVar 22) [NVar 12; NVar 20; NVar 21])].
Definition node atom_rank guard_rank := close (nlams
  (node_fields atom_rank guard_rank ++ proof_fields (NVar 10)) node_body) eq_refl.
Theorem node_type_sorted a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (node_type a g) (𝓤 (g + 3)).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 1024. Qed.
Theorem node_typed a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (node a g) (node_type a g).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 1024. Qed.

(** The interpretation and its guarded clause handler are explicit separate
    arguments.  The theorem eliminates an arbitrary represented proof; it
    neither constructs that handler nor infers it from native soundness. *)
Definition consume_fields atom_rank guard_rank := interface_fields atom_rank guard_rank ++
  [(10, UH.D); (30, UH.Assignment); (31, Handler (NVar 30) (NVar 10));
   (13, UH.A); (32, Proof (NVar 10) (NVar 13))].
Definition consume_type atom_rank guard_rank := close
  (npis (consume_fields atom_rank guard_rank) (NApp (NVar 30) (NVar 13))) eq_refl.
Definition consume_body := napps (NVar 32) [NVar 30; NVar 31].
Definition consume atom_rank guard_rank := close
  (nlams (consume_fields atom_rank guard_rank) consume_body) eq_refl.
Theorem consume_type_sorted a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (consume_type a g) (𝓤 (g + 3)).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 1024. Qed.
Theorem consume_typed a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (consume a g) (consume_type a g).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 1024. Qed.

(** Scoped applications use only repeated original typing rules. *)
Theorem family_application {n} (G : Ctx nat n) a g e xs final :
  (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  NB.NamedSpine G (family_fields a g) e xs final ->
  Typed G (NB.apply_spine (lift_closed (family a g)) xs) (𝓤 (g + 2)).
Proof.
  intros Ha Hg Hs; eapply (NB.named_spine_application G (family_fields a g)
    e xs final (NSort (g + 2))); [exact Hs | | reflexivity |].
  - exact (NT.evaluate_close (npis (family_fields a g) (NSort (g + 2))) eq_refl n e).
  - apply lift_closed_typed, family_sorted; assumption.
Qed.
Theorem family_beta {n} (G : Ctx nat n) a g e xs final r :
  NB.NamedSpine G (family_fields a g) e xs final ->
  NT.evaluate (Proof (NVar 10) (NVar 13)) final = Some r ->
  NB.apply_spine (lift_closed (family a g)) xs =ᵝ r.
Proof.
  intros Hs Hr; eapply UH.named_spine_beta; [exact Hs | | exact Hr].
  exact (NT.evaluate_close (nlams (family_fields a g)
    (Proof (NVar 10) (NVar 13))) eq_refl n e).
Qed.
Theorem node_application {n} (G : Ctx nat n) a g e xs final r :
  (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  NB.NamedSpine G (node_fields a g) e xs final ->
  NT.evaluate (Proof (NVar 10) (UH.Head (NVar 10) (NVar 11))) final = Some r ->
  Typed G (NB.apply_spine (lift_closed (node a g)) xs) r.
Proof.
  intros Ha Hg Hs HE; eapply (NB.named_spine_application G (node_fields a g)
    e xs final (Proof (NVar 10) (UH.Head (NVar 10) (NVar 11))));
    [exact Hs | | exact HE |].
  - exact (NT.evaluate_close (npis (node_fields a g)
      (Proof (NVar 10) (UH.Head (NVar 10) (NVar 11)))) eq_refl n e).
  - apply lift_closed_typed, node_typed; assumption.
Qed.
Theorem node_beta {n} (G : Ctx nat n) a g e xs final r :
  NB.NamedSpine G (node_fields a g ++ proof_fields (NVar 10)) e xs final ->
  NT.evaluate node_body final = Some r ->
  NB.apply_spine (lift_closed (node a g)) xs =ᵝ r.
Proof.
  intros Hs Hr; eapply UH.named_spine_beta; [exact Hs | | exact Hr].
  exact (NT.evaluate_close (nlams
    (node_fields a g ++ proof_fields (NVar 10)) node_body) eq_refl n e).
Qed.
Theorem consume_application {n} (G : Ctx nat n) a g e xs final r :
  (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  NB.NamedSpine G (consume_fields a g) e xs final ->
  NT.evaluate (NApp (NVar 30) (NVar 13)) final = Some r ->
  Typed G (NB.apply_spine (lift_closed (consume a g)) xs) r.
Proof.
  intros Ha Hg Hs HE; eapply (NB.named_spine_application G (consume_fields a g)
    e xs final (NApp (NVar 30) (NVar 13))); [exact Hs | | exact HE |].
  - exact (NT.evaluate_close (npis (consume_fields a g)
      (NApp (NVar 30) (NVar 13))) eq_refl n e).
  - apply lift_closed_typed, consume_typed; assumption.
Qed.
Theorem consume_beta {n} (G : Ctx nat n) a g e xs final r :
  NB.NamedSpine G (consume_fields a g) e xs final ->
  NT.evaluate consume_body final = Some r ->
  NB.apply_spine (lift_closed (consume a g)) xs =ᵝ r.
Proof.
  intros Hs Hr; eapply UH.named_spine_beta; [exact Hs | | exact Hr].
  exact (NT.evaluate_close (nlams (consume_fields a g) consume_body) eq_refl n e).
Qed.

(** The fold equation retains the guard witness, passing it to the supplied
    handler.  It is literal beta conversion, without eta or parametricity. *)
Definition interface_arguments := UH.interface_arguments ++ [NVar 6].
Definition node_fold_fields a g := node_fields a g ++
  [(30, UH.Assignment); (31, Handler (NVar 30) (NVar 10))].
Definition node_fold_type a g := close (npis (node_fold_fields a g)
  (NApp (NVar 30) (UH.Head (NVar 10) (NVar 11)))) eq_refl.
Definition node_fold a g := close (nlams (node_fold_fields a g)
  (napps (NClosed (consume a g)) (interface_arguments ++
    [NVar 10; NVar 30; NVar 31; UH.Head (NVar 10) (NVar 11);
      napps (NClosed (node a g))
        (interface_arguments ++ [NVar 10; NVar 11; NVar 40; NVar 22])]))) eq_refl.
Definition node_fold_result a g := close (nlams (node_fold_fields a g)
  (napps (NVar 31) [NVar 11; NVar 40;
    NLam 12 (UH.Positions (NVar 10) (NVar 11))
      (napps (NVar 22) [NVar 12; NVar 30; NVar 31])])) eq_refl.
Theorem node_fold_typed a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (node_fold a g) (node_fold_type a g).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 2048. Qed.
Theorem node_fold_result_typed a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  Typed ε (node_fold_result a g) (node_fold_type a g).
Proof. intros [-> | ->] [-> | ->]; RkCheck.certify_with 1024. Qed.
Theorem node_fold_beta a g : (a = 1 \/ a = 2) -> (g = 3 \/ g = 4) ->
  node_fold a g =ᵝ node_fold_result a g.
Proof.
  intros [-> | ->] [-> | ->]; eapply RkCheck.check_conv_sound with (fuel := 2048);
    vm_compute; reflexivity.
Qed.

End UniformGuardedHorn.
