(** Structural renaming/weakening for the native judgmental-equality
    certificates. The embedding records only insertion of an actually typed
    declaration and synchronous lifting across a binder. In particular its
    definition does not assume typing or equality preservation. Preservation
    of all three mutual judgments is proved below, without endpoint regularity
    or a semantic conversion premise. *)
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context.
From PTSrkModel Require Import TypedEquality SyntaxRenaming.

Module TypedEqualityRenaming.
Module TE := TypedEquality.TypedEquality.

Lemma typing_context n (G : Ctx nat n) t A : TE.typ G t A -> TE.wf G.
Proof. intro H; induction H; assumption. Qed.

Lemma equality_context n (G : Ctx nat n) t u A : TE.equal G t u A -> TE.wf G.
Proof. intro H; induction H; try assumption; eapply typing_context; eassumption. Qed.

Inductive embedding : forall {n m}, Ctx nat n -> Ctx nat m -> (Fin n -> Fin m) -> Prop :=
| embedding_empty : embedding ε ε (fun i => i)
| embedding_insert {n m} (G : Ctx nat n) (D : Ctx nat m) r B k :
    embedding G D r -> TE.typ D B (𝓤 k) ->
    embedding G (D & B) (fun i => fsucc (r i))
| embedding_extend {n m} (G : Ctx nat n) (D : Ctx nat m) r A :
    embedding G D r -> embedding (G & A) (D & rename r A) (weak r).
Derive Signature for embedding.

Lemma embedding_lookup n m (G : Ctx nat n) (D : Ctx nat m) r :
  embedding G D r -> context_renaming G D r.
Proof.
  intro H; induction H.
  - intro i; dependent elimination i.
  - intro i. change (rename (fun i => fsucc (r i)) (G !! i) = shift (D !! r i)).
    unfold shift. rewrite <- rename_comp, IHembedding. reflexivity.
  - apply context_renaming_extend; assumption.
Qed.

Theorem certificate_renaming :
  (forall n (G : Ctx nat n), TE.wf G ->
    forall m (D : Ctx nat m) r, embedding G D r -> TE.wf D) /\
  (forall n (G : Ctx nat n) t A, TE.typ G t A ->
    forall m (D : Ctx nat m) r, embedding G D r -> TE.typ D (rename r t) (rename r A)) /\
  (forall n (G : Ctx nat n) t u A, TE.equal G t u A ->
    forall m (D : Ctx nat m) r, embedding G D r ->
      TE.equal D (rename r t) (rename r u) (rename r A)).
Proof.
  apply TE.certificate_induction.
  - intros m D r HR. dependent elimination HR; [apply TE.wf_empty |].
    eapply TE.wf_extend; eassumption.
  - intros n G A k HA IHA m D r HR. dependent elimination HR.
    + eapply TE.wf_extend; eassumption.
    + eapply TE.wf_extend. apply IHA; eassumption.
  - intros n G i HG IHG m D r HR; cbn [rename]. apply TE.typ_sort; eapply IHG; exact HR.
  - intros n G i HG IHG m D r HR; cbn [rename].
    rewrite (embedding_lookup _ _ _ _ _ HR). apply TE.typ_variable; eapply IHG; exact HR.
  - intros n G A B j k HA IHA HB IHB m D r HR; cbn [rename].
    eapply TE.typ_product; [apply IHA; exact HR | apply IHB, embedding_extend; exact HR].
  - intros n G A B t j k HA IHA HB IHB HT IHT m D r HR; cbn [rename].
    eapply TE.typ_lambda; [apply IHA; exact HR | apply IHB, embedding_extend; exact HR |
      apply IHT, embedding_extend; exact HR].
  - intros n G A B t u HT IHT HU IHU m D r HR; cbn [rename].
    rewrite rename_subst. eapply TE.typ_application; [apply IHT; exact HR | apply IHU; exact HR].
  - intros n G t A B k HE IHE HT IHT m D r HR; cbn [rename].
    eapply TE.typ_conversion; [apply IHE; exact HR | apply IHT; exact HR].
  - intros n G i HG IHG m D r HR; cbn [rename]. apply TE.equal_sort; eapply IHG; exact HR.
  - intros n G i HG IHG m D r HR; cbn [rename].
    rewrite (embedding_lookup _ _ _ _ _ HR). apply TE.equal_variable; eapply IHG; exact HR.
  - intros n G A A' B B' j k HA IHA HB IHB m D r HR; cbn [rename].
    eapply TE.equal_product; [apply IHA; exact HR | apply IHB, embedding_extend; exact HR].
  - intros n G A A' B t t' j k HA IHA HT IHT HB IHB m D r HR; cbn [rename].
    eapply TE.equal_lambda; [apply IHA; exact HR | apply IHT, embedding_extend; exact HR |
      apply IHB, embedding_extend; exact HR].
  - intros n G A B t t' u u' HT IHT HU IHU m D r HR; cbn [rename].
    rewrite rename_subst. eapply TE.equal_application; [apply IHT; exact HR | apply IHU; exact HR].
  - intros n G t u A HE IHE m D r HR. apply TE.equal_symmetric, IHE; exact HR.
  - intros n G t u v A HE IHE HE' IHE' m D r HR.
    eapply TE.equal_transitive; [apply IHE; exact HR | apply IHE'; exact HR].
  - intros n G t u A B k HE IHE HE' IHE' m D r HR; cbn [rename].
    eapply TE.equal_conversion; [apply IHE; exact HR | apply IHE'; exact HR].
  - intros n G A B t u j k HA IHA HB IHB HT IHT HU IHU m D r HR; cbn [rename].
    rewrite !rename_subst. eapply TE.equal_beta.
    + apply IHA; exact HR.
    + apply IHB, embedding_extend; exact HR.
    + apply IHT, embedding_extend; exact HR.
    + apply IHU; exact HR.
Qed.

Theorem wf_renaming n (G : Ctx nat n) : TE.wf G ->
  forall m (D : Ctx nat m) r, embedding G D r -> TE.wf D.
Proof. exact (proj1 certificate_renaming n G). Qed.
Theorem typing_renaming n (G : Ctx nat n) t A : TE.typ G t A ->
  forall m (D : Ctx nat m) r, embedding G D r -> TE.typ D (rename r t) (rename r A).
Proof. exact (proj1 (proj2 certificate_renaming) n G t A). Qed.
Theorem equality_renaming n (G : Ctx nat n) t u A : TE.equal G t u A ->
  forall m (D : Ctx nat m) r, embedding G D r ->
    TE.equal D (rename r t) (rename r u) (rename r A).
Proof. exact (proj2 (proj2 certificate_renaming) n G t u A). Qed.

Lemma embedding_identity n (G : Ctx nat n) :
  exists r, embedding G G r /\ forall i, r i = i.
Proof.
  induction G.
  - exists (fun i => i); split; [apply embedding_empty | reflexivity].
  - destruct IHG as [r [HR Er]]. exists (weak r); split.
    + assert (EA : rename r t = t).
      { rewrite (rename_ext r (fun i => i) Er), rename_id; reflexivity. }
      rewrite <- EA at 2. apply embedding_extend; exact HR.
    + intro i; dependent elimination i; cbn [weak fin_match]; [reflexivity | rewrite Er; reflexivity].
Qed.

Lemma embedding_weakening n (G : Ctx nat n) B k : TE.typ G B (𝓤 k) ->
  exists r, embedding G (G & B) r /\ forall i, r i = fsucc i.
Proof.
  intro HB. destruct (embedding_identity n G) as [r [HR Er]].
  exists (fun i => fsucc (r i)); split; [eapply embedding_insert; eassumption |].
  intro i; rewrite Er; reflexivity.
Qed.

Theorem typing_weakening n (G : Ctx nat n) t A B k :
  TE.typ G t A -> TE.typ G B (𝓤 k) -> TE.typ (G & B) (shift t) (shift A).
Proof.
  intros HT HB. destruct (embedding_weakening n G B k HB) as [r [HR Er]].
  pose proof (typing_renaming n G t A HT (S n) (G & B) r HR) as H.
  rewrite !(rename_ext r fsucc Er) in H. exact H.
Qed.
Theorem equality_weakening n (G : Ctx nat n) t u A B k :
  TE.equal G t u A -> TE.typ G B (𝓤 k) ->
  TE.equal (G & B) (shift t) (shift u) (shift A).
Proof.
  intros HE HB. destruct (embedding_weakening n G B k HB) as [r [HR Er]].
  pose proof (equality_renaming n G t u A HE (S n) (G & B) r HR) as H.
  rewrite !(rename_ext r fsucc Er) in H. exact H.
Qed.

End TypedEqualityRenaming.
Print Assumptions TypedEqualityRenaming.typing_context.
Print Assumptions TypedEqualityRenaming.equality_context.
Print Assumptions TypedEqualityRenaming.embedding_lookup.
Print Assumptions TypedEqualityRenaming.certificate_renaming.
Print Assumptions TypedEqualityRenaming.typing_weakening.
Print Assumptions TypedEqualityRenaming.equality_weakening.
