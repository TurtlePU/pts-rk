(** A fixed original-PTS interface for internally represented Horn fragments.
    D, A, clause/premise-position families, their projections, and d:D are
    genuine object-language arguments.  Proof contains only positive Horn
    closure, never a model, truth value, source typing or desired conclusion.

    Exact atom ranks 1 and 2 are certified separately by one finite native
    parameter restriction; the other carrier fibers have exact rank 1.
    No cumulativity identifies the two interfaces.  The generic consumer
    accepts an explicit interpretation and clause handler.  Constructing that
    handler from a represented model and proving original-source coverage
    remain separate obligations. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import NamedTemplates NamedBeta.
Import ListNotations.

Module UniformHorn.
Import CommonCodes Core Structural.
Module NT := NamedTemplates.NamedTemplates.
Module NB := NamedBeta.NamedBeta.

Definition D := NVar 0.
Definition A := NVar 1.
Definition Clauses d := NApp (NVar 2) d.
Definition Positions d c := napps (NVar 3) [d; c].
Definition Premise d c i := napps (NVar 4) [d; c; i].
Definition Head d c := napps (NVar 5) [d; c].

Definition interface_fields atom_rank :=
  [(0, NSort 1); (1, NSort atom_rank);
   (2, nArrow D (NSort 1));
   (3, npis [(10, D); (11, Clauses (NVar 10))] (NSort 1));
   (4, npis [(10, D); (11, Clauses (NVar 10));
     (12, Positions (NVar 10) (NVar 11))] A);
   (5, npis [(10, D); (11, Clauses (NVar 10))] A)].
Definition Assignment := nArrow A (NSort 1).
Definition Prem X d c := NPi 12 (Positions d c)
  (NApp X (Premise d c (NVar 12))).
Definition Handler X d := NPi 11 (Clauses d)
  (nArrow (Prem X d (NVar 11)) (NApp X (Head d (NVar 11)))).
Definition proof_fields d := [(20, Assignment); (21, Handler (NVar 20) d)].
Definition Proof d q := npis (proof_fields d) (NApp (NVar 20) q).

(** These family terms expose exact fiber ranks, including empty position
    carriers: no arity-dependent proposition telescope occurs. *)
Definition premise_fields atom_rank := interface_fields atom_rank ++
  [(10, D); (11, Clauses (NVar 10)); (20, Assignment)].
Definition premise_type atom_rank := close
  (npis (premise_fields atom_rank) (NSort 2)) eq_refl.
Definition premise atom_rank := close (nlams (premise_fields atom_rank)
  (Prem (NVar 20) (NVar 10) (NVar 11))) eq_refl.
Definition handler_fields atom_rank := interface_fields atom_rank ++
  [(10, D); (20, Assignment)].
Definition handler_type atom_rank := close
  (npis (handler_fields atom_rank) (NSort 3)) eq_refl.
Definition handler atom_rank := close (nlams (handler_fields atom_rank)
  (Handler (NVar 20) (NVar 10))) eq_refl.
Definition family_fields atom_rank := interface_fields atom_rank ++
  [(10, D); (13, A)].
Definition family_type atom_rank := close
  (npis (family_fields atom_rank) (NSort 4)) eq_refl.
Definition family atom_rank := close (nlams (family_fields atom_rank)
  (Proof (NVar 10) (NVar 13))) eq_refl.

Theorem premise_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (premise atom_rank) (premise_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 512. Qed.
Theorem handler_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (handler atom_rank) (handler_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 512. Qed.
Theorem family_type_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (family_type atom_rank) (𝓤 3).
Proof. intros [-> | ->]; RkCheck.certify_with 512. Qed.
Theorem family_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (family atom_rank) (family_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 512. Qed.

(** Clause introduction accepts arbitrary represented child proofs. *)
Definition Children d c := NPi 12 (Positions d c)
  (Proof d (Premise d c (NVar 12))).
Definition node_fields atom_rank := interface_fields atom_rank ++
  [(10, D); (11, Clauses (NVar 10));
   (22, Children (NVar 10) (NVar 11))].
Definition node_type atom_rank := close (npis (node_fields atom_rank)
  (Proof (NVar 10) (Head (NVar 10) (NVar 11)))) eq_refl.
Definition node_body := napps (NVar 21)
  [NVar 11; NLam 12 (Positions (NVar 10) (NVar 11))
    (napps (NVar 22) [NVar 12; NVar 20; NVar 21])].
Definition node atom_rank := close (nlams
  (node_fields atom_rank ++ proof_fields (NVar 10)) node_body) eq_refl.
Theorem node_type_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (node_type atom_rank) (𝓤 5).
Proof. intros [-> | ->]; RkCheck.certify_with 1024. Qed.
Theorem node_typed atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (node atom_rank) (node_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 1024. Qed.

(** Ordinary Church elimination, internally quantified over the fragment,
    query and arbitrary proof.  hV is supplied separately, not hidden in
    Proof or in source admission.  This theorem does NOT construct hV. *)
Definition consume_fields atom_rank := interface_fields atom_rank ++
  [(10, D); (30, Assignment); (31, Handler (NVar 30) (NVar 10));
   (13, A); (32, Proof (NVar 10) (NVar 13))].
Definition consume_type atom_rank := close (npis (consume_fields atom_rank)
  (NApp (NVar 30) (NVar 13))) eq_refl.
Definition consume_body := napps (NVar 32) [NVar 30; NVar 31].
Definition consume atom_rank := close
  (nlams (consume_fields atom_rank) consume_body) eq_refl.
Theorem consume_type_sorted atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (consume_type atom_rank) (𝓤 5).
Proof. intros [-> | ->]; RkCheck.certify_with 1024. Qed.
Theorem consume_typed atom_rank : atom_rank = 1 \/ atom_rank = 2 ->
  Typed ε (consume atom_rank) (consume_type atom_rank).
Proof. intros [-> | ->]; RkCheck.certify_with 1024. Qed.

(** Structural application and computation laws apply in arbitrary original
    contexts.  NamedSpine packages only repeated original typing rules; its
    environment is assembler data and is absent from the object interface. *)
Lemma apply_spine_beta {n} (f g : Term nat n) xs : f =ᵝ g ->
  NB.apply_spine f xs =ᵝ NB.apply_spine g xs.
Proof.
  revert f g; induction xs as [|x xs IH]; intros f g H; cbn [NB.apply_spine].
  - exact H.
  - apply IH, beta_app; [exact H | reflexivity].
Qed.

Lemma named_spine_beta {n} (G : Ctx nat n) fields e xs final :
  NB.NamedSpine G fields e xs final -> forall body f r,
  NT.evaluate (nlams fields body) e = Some f ->
  NT.evaluate body final = Some r -> NB.apply_spine f xs =ᵝ r.
Proof.
  intro H; induction H as [e|x A fields e arg U args final HA Harg Hs IH];
    intros body f r HF HR.
  - cbn [nlams fold_right] in HF; rewrite HF in HR; injection HR as <-;
      reflexivity.
  - change (NT.evaluate (NLam x A (nlams fields body)) e = Some f) in HF.
    destruct (NB.named_application_result e x A (nlams fields body) f arg HF)
      as [f1 [E1 B1]].
    cbn [NB.apply_spine].
    transitivity (NB.apply_spine f1 args).
    + apply apply_spine_beta, B1.
    + exact (IH body f1 r E1 HR).
Qed.

Theorem family_application {n} (G : Ctx nat n) atom_rank e xs final :
  atom_rank = 1 \/ atom_rank = 2 ->
  NB.NamedSpine G (family_fields atom_rank) e xs final ->
  Typed G (NB.apply_spine (lift_closed (family atom_rank)) xs) (𝓤 4).
Proof.
  intros Hr Hs; eapply (NB.named_spine_application G (family_fields atom_rank)
    e xs final (NSort 4)); [exact Hs | | reflexivity |].
  - exact (NT.evaluate_close _ eq_refl n e).
  - apply lift_closed_typed, family_sorted, Hr.
Qed.
Theorem family_beta {n} (G : Ctx nat n) atom_rank e xs final r :
  NB.NamedSpine G (family_fields atom_rank) e xs final ->
  NT.evaluate (Proof (NVar 10) (NVar 13)) final = Some r ->
  NB.apply_spine (lift_closed (family atom_rank)) xs =ᵝ r.
Proof.
  intros Hs Hr; eapply named_spine_beta; [exact Hs | | exact Hr].
  exact (NT.evaluate_close _ eq_refl n e).
Qed.

Theorem node_application {n} (G : Ctx nat n) atom_rank e xs final r :
  atom_rank = 1 \/ atom_rank = 2 ->
  NB.NamedSpine G (node_fields atom_rank) e xs final ->
  NT.evaluate (Proof (NVar 10) (Head (NVar 10) (NVar 11))) final = Some r ->
  Typed G (NB.apply_spine (lift_closed (node atom_rank)) xs) r.
Proof.
  intros Hr Hs HE; eapply (NB.named_spine_application G (node_fields atom_rank)
    e xs final (Proof (NVar 10) (Head (NVar 10) (NVar 11))));
    [exact Hs | | exact HE |].
  - exact (NT.evaluate_close _ eq_refl n e).
  - apply lift_closed_typed, node_typed, Hr.
Qed.
Theorem node_beta {n} (G : Ctx nat n) atom_rank e xs final r :
  NB.NamedSpine G (node_fields atom_rank ++ proof_fields (NVar 10)) e xs final ->
  NT.evaluate node_body final = Some r ->
  NB.apply_spine (lift_closed (node atom_rank)) xs =ᵝ r.
Proof.
  intros Hs Hr; eapply named_spine_beta; [exact Hs | | exact Hr].
  exact (NT.evaluate_close _ eq_refl n e).
Qed.

Theorem consume_application {n} (G : Ctx nat n) atom_rank e xs final r :
  atom_rank = 1 \/ atom_rank = 2 ->
  NB.NamedSpine G (consume_fields atom_rank) e xs final ->
  NT.evaluate (NApp (NVar 30) (NVar 13)) final = Some r ->
  Typed G (NB.apply_spine (lift_closed (consume atom_rank)) xs) r.
Proof.
  intros Hr Hs HE; eapply (NB.named_spine_application G (consume_fields atom_rank)
    e xs final (NApp (NVar 30) (NVar 13))); [exact Hs | | exact HE |].
  - exact (NT.evaluate_close _ eq_refl n e).
  - apply lift_closed_typed, consume_typed, Hr.
Qed.
Theorem consume_beta {n} (G : Ctx nat n) atom_rank e xs final r :
  NB.NamedSpine G (consume_fields atom_rank) e xs final ->
  NT.evaluate consume_body final = Some r ->
  NB.apply_spine (lift_closed (consume atom_rank)) xs =ᵝ r.
Proof.
  intros Hs Hr; eapply named_spine_beta; [exact Hs | | exact Hr].
  exact (NT.evaluate_close _ eq_refl n e).
Qed.

End UniformHorn.
