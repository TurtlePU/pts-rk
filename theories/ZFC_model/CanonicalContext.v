(** Context transport for canonical denotation at the SAME syntax, valuation,
    and value. Original typing witnesses transport along an original context
    typing morphism; their syntactic normality is unchanged. No semantic
    conversion, normalization of an annotation, or target-validity premise is
    assumed. Transport of validity of a valuation is NOT asserted here. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Preservation DefEq.
From PTSrkModel Require Import ContextTransport CanonicalDenotation CanonicalRealization.

Module CanonicalContext.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module CR := CanonicalRealization.CanonicalRealization.

Lemma context_typing_morphism_extend n (G D : Ctx nat n) A :
  context_typing_morphism G D -> context_typing_morphism (G & A) (D & A).
Proof.
  intros HM i; dependent elimination i as [fzero | fsucc j].
  - exact (@typ_var nat RankSorts _ (D & A) fzero).
  - change (@typ nat RankSorts _ (D & A) (shift (var j)) (shift (G !! j))).
    apply weakening, HM.
Qed.

Section Transport.
Variables H s : Ens.

Theorem denotes_context_transport n G rho t v : CD.denotes H s n G rho t v ->
  forall D : Ctx nat n, context_typing_morphism G D -> CD.denotes H s n D rho t v.
Proof.
  intro HD; induction HD; intros D HM.
  - apply CD.denotes_sort.
  - apply CD.denotes_var.
  - eapply CD.denotes_product; eauto using context_typing_morphism_extend.
  - eapply CD.denotes_lambda with (B := B).
    + eapply typing_context_transport; [apply context_typing_morphism_extend; exact HM | eassumption].
    + assumption.
    + eauto.
    + eauto using context_typing_morphism_extend.
    + eauto using context_typing_morphism_extend.
    + assumption.
    + assumption.
  - eapply CD.denotes_application with (A := A) (B := B).
    + eapply typing_context_transport; [exact HM | eassumption].
    + assumption.
    + eauto.
    + eauto using context_typing_morphism_extend.
    + assumption.
    + eauto.
    + eauto.
  - eapply CD.denotes_equal; eauto.
Qed.

Theorem denotes_context_reduction n (G D : Ctx nat n) rho t v :
  @wf nat RankSorts n G -> ctx_beta G D ->
  CD.denotes H s n G rho t v -> CD.denotes H s n D rho t v.
Proof.
  intros HG HR HD. eapply denotes_context_transport; [exact HD |].
  eapply context_reduction_morphism; eassumption.
Qed.

Theorem denotes_context_conversion n (G D : Ctx nat n) rho t v :
  contexts_convertible n G D -> @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  (CD.denotes H s n G rho t v <-> CD.denotes H s n D rho t v).
Proof.
  intros HC HG HD; split; intro HV; eapply denotes_context_transport; [exact HV | | exact HV |];
    apply context_conversion_morphism.
  - exact HC.
  - exact HG.
  - apply contexts_convertible_sym; exact HC.
  - exact HD.
Qed.

Corollary denotes_binder_context_conversion n (G : Ctx nat n) A B l k rho t v :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 l) ->
  @typ nat RankSorts n G B (𝓤 k) -> A =ᵝ B ->
  (CD.denotes H s (S n) (G & A) rho t v <-> CD.denotes H s (S n) (G & B) rho t v).
Proof.
  intros HG HA HB E. apply denotes_context_conversion.
  - constructor; [apply contexts_convertible_refl | exact E].
  - eapply wf_cons; eassumption.
  - eapply wf_cons; eassumption.
Qed.

Theorem realizes_context_transport n (G D : Ctx nat n) rho t T :
  context_typing_morphism G D -> CR.realizes H s G rho t T -> CR.realizes H s D rho t T.
Proof.
  intros HM [v [a [Dt [DT Hv]]]]. exists v, a; split.
  - eapply denotes_context_transport; eassumption.
  - split; [eapply denotes_context_transport; eassumption | exact Hv].
Qed.

Theorem realizes_context_conversion n (G D : Ctx nat n) rho t T :
  contexts_convertible n G D -> @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  (CR.realizes H s G rho t T <-> CR.realizes H s D rho t T).
Proof.
  intros HC HG HD. split; apply realizes_context_transport; apply context_conversion_morphism.
  - exact HC.
  - exact HG.
  - apply contexts_convertible_sym; exact HC.
  - exact HD.
Qed.
End Transport.
End CanonicalContext.

Print Assumptions CanonicalContext.context_typing_morphism_extend.
Print Assumptions CanonicalContext.denotes_context_transport.
Print Assumptions CanonicalContext.denotes_context_reduction.
Print Assumptions CanonicalContext.denotes_context_conversion.
Print Assumptions CanonicalContext.denotes_binder_context_conversion.
Print Assumptions CanonicalContext.realizes_context_transport.
Print Assumptions CanonicalContext.realizes_context_conversion.
