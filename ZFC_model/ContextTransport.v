(** Transport through original context typing, then original context reduction.
    This is not a semantic conversion axiom. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Preservation DefEq AbstractRewriting.
From PTSrkModel Require Import SyntaxSubstitution Denotation InterpretedContexts.

Definition context_typing_morphism {n} (G D : Ctx nat n) :=
  forall i, @typ nat RankSorts n D (var i) (G !! i).

Lemma context_typing_morphism_identity n (G : Ctx nat n) : context_typing_morphism G G.
Proof. intro i; apply typ_var. Qed.

Theorem typing_context_transport n (G D : Ctx nat n) t T :
  context_typing_morphism G D -> @typ nat RankSorts n G t T -> @typ nat RankSorts n D t T.
Proof.
  intros HM HT.
  pose proof (rank_typing_replace n G t T HT n D (@var nat n)) as HS.
  rewrite !replace_var in HS. apply HS.
  intro i; rewrite replace_var; apply HM.
Qed.

Lemma context_typing_morphism_compose n (G D E : Ctx nat n) :
  context_typing_morphism G D -> context_typing_morphism D E -> context_typing_morphism G E.
Proof. intros HGD HDE i; eapply typing_context_transport; [exact HDE | apply HGD]. Qed.

Theorem denotes_context_transport H s n (G D : Ctx nat n) rho t v :
  context_typing_morphism G D -> denotes H s n G rho t v -> denotes H s n D rho t v.
Proof.
  intros HM HD.
  pose proof (denotes_replace H s n G rho t v HD n D (@var nat n) rho) as HS.
  rewrite replace_var in HS. apply HS.
  - intro i; rewrite replace_var; apply HM.
  - intro i; apply denotes_var.
Qed.

Theorem context_reduction_morphism n (G D : Ctx nat n) :
  @wf nat RankSorts n G -> ctx_beta G D -> context_typing_morphism G D.
Proof.
  intros HG HR i. eapply context_reduction_strong; [apply typ_var | exact HG | exact HR].
Qed.

Theorem denotes_context_reduction H s n (G D : Ctx nat n) rho t v :
  @wf nat RankSorts n G -> ctx_beta G D ->
  denotes H s n G rho t v -> denotes H s n D rho t v.
Proof.
  intros HG HR HD. eapply denotes_context_transport; [eapply context_reduction_morphism; eauto | exact HD].
Qed.
Print Assumptions typing_context_transport.
Print Assumptions denotes_context_transport.
Print Assumptions context_reduction_morphism.
Print Assumptions denotes_context_reduction.

Inductive contexts_convertible : forall n, Ctx nat n -> Ctx nat n -> Prop :=
| contexts_convertible_empty : contexts_convertible 0 ε ε
| contexts_convertible_cons n (G D : Ctx nat n) A B :
    contexts_convertible n G D -> A =ᵝ B -> contexts_convertible (S n) (G & A) (D & B).

Lemma contexts_convertible_sym n (G D : Ctx nat n) :
  contexts_convertible n G D -> contexts_convertible n D G.
Proof. intro HC; induction HC; constructor; auto. symmetry; assumption. Qed.

Lemma wf_context_tail n (G : Ctx nat n) A : @wf nat RankSorts (S n) (G & A) -> @wf nat RankSorts n G.
Proof. intro HG; dependent elimination HG; assumption. Qed.
Lemma wf_context_head n (G : Ctx nat n) A : @wf nat RankSorts (S n) (G & A) ->
  exists l, @typ nat RankSorts n G A (𝓤 l).
Proof. intro HG; dependent elimination HG; eauto. Qed.

Theorem context_conversion_morphism n (G D : Ctx nat n) :
  contexts_convertible n G D -> @wf nat RankSorts n G -> context_typing_morphism G D.
Proof.
  intro HC; induction HC; intros HG i.
  - dependent elimination i.
  - pose proof (IHHC (wf_context_tail n G A HG)) as HM.
    destruct (wf_context_head n G A HG) as [l TA].
    dependent elimination i as [fzero | fsucc j].
    + change (@typ nat RankSorts _ (D & B) (var fzero) (shift A)).
      eapply typ_conv with (T := shift B) (ℓ := l).
      * exact (@typ_var nat RankSorts _ (D & B) fzero).
      * change (@typ nat RankSorts _ (D & B) (shift A) (shift (𝓤 l))).
        apply weakening. eapply typing_context_transport; [exact HM | exact TA].
      * apply rename_equiv. symmetry; assumption.
    + change (@typ nat RankSorts _ (D & B) (shift (var j)) (shift (G !! j))).
      apply weakening, HM.
Qed.

Theorem denotes_context_conversion H s n (G D : Ctx nat n) rho t v :
  contexts_convertible n G D -> @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  (denotes H s n G rho t v <-> denotes H s n D rho t v).
Proof.
  intros HC HG HD; split; apply denotes_context_transport; apply context_conversion_morphism.
  - exact HC.
  - exact HG.
  - apply contexts_convertible_sym; exact HC.
  - exact HD.
Qed.
Print Assumptions context_conversion_morphism.
Print Assumptions denotes_context_conversion.
Check denotes_context_conversion.

Lemma contexts_convertible_refl n (G : Ctx nat n) : contexts_convertible n G G.
Proof. induction G; constructor; auto. reflexivity. Qed.

Corollary denotes_binder_context_conversion H s n (G : Ctx nat n) A B l k rho t v :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 l) ->
  @typ nat RankSorts n G B (𝓤 k) -> A =ᵝ B ->
  (denotes H s (S n) (G & A) rho t v <-> denotes H s (S n) (G & B) rho t v).
Proof.
  intros HG HA HB E. apply denotes_context_conversion.
  - constructor; [apply contexts_convertible_refl | exact E].
  - eapply wf_cons; eauto.
  - eapply wf_cons; eauto.
Qed.
Print Assumptions denotes_binder_context_conversion.

(** Realization transports at a fixed valuation without assuming preservation
    of validity of that valuation. The latter also changes declaration terms
    and must not be inferred from syntactic context conversion alone. *)
Theorem realizes_context_transport H s n (G D : Ctx nat n) rho t T :
  context_typing_morphism G D -> realizes H s G rho t T ->
  realizes H s D rho t T.
Proof.
  intros HM [v [a [Dt [DT Hv]]]]. exists v, a. split.
  - eapply denotes_context_transport; eassumption.
  - split; [eapply denotes_context_transport; eassumption | exact Hv].
Qed.

Theorem realizes_context_conversion H s n (G D : Ctx nat n) rho t T :
  contexts_convertible n G D -> @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  (realizes H s G rho t T <-> realizes H s D rho t T).
Proof.
  intros HC HG HD. split; apply realizes_context_transport;
    apply context_conversion_morphism.
  - exact HC.
  - exact HG.
  - apply contexts_convertible_sym; exact HC.
  - exact HD.
Qed.
Print Assumptions realizes_context_transport.
Print Assumptions realizes_context_conversion.
