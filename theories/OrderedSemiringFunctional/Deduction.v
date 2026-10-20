(** Generic deduction preservation. The explicit axiom-realization argument
    is discharged by the final interpretation module, not postulated. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural DirectRLogic.
From OrderedSemiring Require Import ModelInterface.
From OrderedSemiringFunctional Require Import Source Translation Equality.
Import ListNotations.
Module FunctionalDeduction.
Import CommonCodes Core Structural NegativeLogic FunctionalTranslation.

Lemma closed_formula {k n} (env : Fin k -> Term nat n) (A : FunctionalSource.formula 0) :
  formula (FunctionalSource.closed_instance A) env = lift_closed (sentence A).
Proof.
  unfold FunctionalSource.closed_instance. rewrite formula_source_rename.
  unfold lift_closed, sentence. rewrite formula_rename.
  apply formula_ext. intro i. exact (match i with end).
Qed.

Theorem preservation_from_axiom_realization
  (axioms : forall A, FunctionalSource.axiom A -> Realizes (sentence A))
  {k} Ξ (A : FunctionalSource.formula k) : FunctionalSource.derives Ξ A ->
  forall n (Γ : Ctx nat n) env,
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  (forall i, inhabited Γ (Model.admitted (env i))) ->
  (forall B, In B Ξ -> inhabited Γ (formula B env)) ->
  inhabited Γ (formula A env).
Proof.
  intro HD. induction HD; intros m Δ env Henv Hg Hctx.
  - apply Hctx. exact H.
  - rewrite closed_formula. destruct (axioms A H) as [p Hp].
    exists (lift_closed p). exact (lift_closed_typed Δ _ _ Hp).
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
      change (inhabited (Δ & lift_closed Model.Domain & Model.admitted V0)
        (formula B (fun i => shift (shift (env i))))).
      rewrite <- !formula_shift. apply inhabited_shift, inhabited_shift, Hctx. exact HB.
  - apply universal_elimination; [exact Henv |exact Hg |apply IHHD; assumption].
  - apply classical_elimination; [exact Henv |apply IHHD; assumption].
  - apply equality_reflexivity. exact Henv.
  - eapply FunctionalEquality.equality_replacement;
      [exact Henv |exact Hg |apply IHHD1 |apply IHHD2]; assumption.
Qed.

Theorem sentence_preservation_from_axiom_realization
  (axioms : forall A, FunctionalSource.axiom A -> Realizes (sentence A))
  (A : FunctionalSource.formula 0) :
  FunctionalSource.derives [] A -> exists p, @typ nat RankSorts 0 ε p (sentence A).
Proof.
  intro H. apply (preservation_from_axiom_realization axioms [] A H 0 ε empty_env).
  - intro i. exact (match i with end).
  - intro i. exact (match i with end).
  - intros B HB. contradiction.
Qed.
Print Assumptions preservation_from_axiom_realization.
End FunctionalDeduction.
