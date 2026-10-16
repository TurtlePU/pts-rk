(** Preservation of the independently defined classical relational deduction
    system, in the original PTS typing judgment. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural DirectRLogic.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRRelationalSyntax
  DirectRRelationalTranslation DirectRRelationalEquality DirectRRelationalAxioms.
Import ListNotations.
Module RelationalDeduction.
Import CommonCodes Core Structural NegativeLogic RelationalTranslation.

Theorem preservation {k} Ξ (A : Relational.formula k) : Relational.derives Ξ A ->
  forall n (Γ : Ctx nat n) env,
  (forall i, Typed Γ (env i) (lift_closed Unary.Domain)) ->
  (forall i, inhabited Γ (Unary.admitted (env i))) ->
  (forall B, In B Ξ -> inhabited Γ (formula B env)) ->
  inhabited Γ (formula A env).
Proof.
  intro HD. induction HD; intros m Δ env Henv Hg Hctx.
  - apply Hctx. exact H.
  - apply RelationalAxioms.source_axiom_realized. exact H.
  - apply implication_introduction; [exact Henv |].
    apply IHHD.
    + apply environment_shift. exact Henv.
    + apply admitted_environment_shift. exact Hg.
    + intros C [<-|HC].
      * rewrite <- formula_shift. apply newest.
      * rewrite <- formula_shift. apply inhabited_shift, Hctx. exact HC.
  - eapply implication_elimination; [apply IHHD1 |apply IHHD2]; eassumption.
  - apply universal_introduction, IHHD.
    + apply environment_shift, environment_transpose. exact Henv.
    + apply admitted_environment_transpose. exact Hg.
    + intros C HC. apply in_map_iff in HC. destruct HC as [B [<- HB]].
      rewrite formula_source_rename.
      change (inhabited (Δ & lift_closed Unary.Domain & Unary.admitted V0)
        (formula B (fun i => shift (shift (env i))))).
      rewrite <- !formula_shift. apply inhabited_shift, inhabited_shift, Hctx. exact HB.
  - apply universal_elimination; [exact Henv |exact Hg |apply IHHD; assumption].
  - apply classical_elimination; [exact Henv |apply IHHD; assumption].
  - apply equality_reflexivity. exact Henv.
  - eapply RelationalEquality.equality_replacement; [exact Henv |apply IHHD1 |apply IHHD2]; assumption.
Qed.

Theorem sentence_preservation (A : Relational.formula 0) :
  Relational.derives [] A -> exists p, @typ nat RankSorts 0 ε p (sentence A).
Proof.
  intro H. apply (preservation [] A H 0 ε empty_env).
  - intro i. exact (match i with end).
  - intro i. exact (match i with end).
  - intros B HB. contradiction.
Qed.
End RelationalDeduction.
