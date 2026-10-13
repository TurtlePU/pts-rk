(** Preservation of independent classical functional deductions in original typ. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFirstOrder
  DirectRFunctionalSyntax DirectRFunctionalTranslation DirectRFunctionalFormulaLogic
  DirectRFunctionalEquality DirectRFunctionalSourceAxioms DirectRFunctionalTerms
  DirectRFunctionalBounded.
Import ListNotations.
Module FunctionalDeduction.
Import Codes Core Structural NegativeLogic FirstOrder FunctionalTranslation
  FunctionalFormulaLogic FunctionalEquality.

Lemma conjunction_intro {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed Γ B -> inhabited Γ A -> inhabited Γ B -> inhabited Γ (Conj A B).
Proof.
  intros HA HB Hp Hq. unfold Conj, Neg. apply arrow_intro.
  - apply arrow_formed; [exact HA |apply arrow_formed; [exact HB |exists 1; apply bottom_in_context]].
  - rewrite <- lift_closed_shift. pose proof (newest Γ (Arrow A (Arrow B (lift_closed Bottom)))) as H.
    normalize_shifts H.
    eapply arrow_elim; [eapply arrow_elim; [exact H |apply inhabited_shift; exact Hp] |].
    apply inhabited_shift. exact Hq.
Qed.
Lemma conjunction_elim {n} (Γ : Ctx nat n) A B C :
  formed Γ A -> formed Γ B -> formed Γ C -> stable Γ C ->
  inhabited Γ (Conj A B) -> inhabited Γ (Arrow A (Arrow B C)) -> inhabited Γ C.
Proof.
  intros HA HB HC HS Hp Hf. eapply arrow_elim; [exact HS |].
  apply arrow_intro; [apply neg_formed; exact HC |]. rewrite <- lift_closed_shift.
  weaken_copy Hp (Neg C) Hp1. unfold Conj in Hp1. normalize_shifts Hp1.
  eapply arrow_elim; [exact Hp1 |].
  apply arrow_intro; [apply formed_shift; exact HA |]. rewrite shift_arrow.
  apply arrow_intro; [apply formed_shift, formed_shift; exact HB |].
  rewrite <- !lift_closed_shift.
  pose proof (newest Γ (Neg C)) as Hnc. normalize_shifts Hnc.
  weaken_copy Hnc (shift A) Hnc2. weaken_copy Hnc2 (shift (shift B)) Hnc3.
  eapply arrow_elim; [exact Hnc3 |].
  weaken_copy Hf (Neg C) Hf1. weaken_copy Hf1 (shift A) Hf2.
  weaken_copy Hf2 (shift (shift B)) Hf3.
  eapply arrow_elim; [eapply arrow_elim; [exact Hf3 |] |apply newest].
  apply inhabited_shift, newest.
Qed.
Lemma conjunction_left {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed Γ B -> stable Γ A -> inhabited Γ (Conj A B) -> inhabited Γ A.
Proof.
  intros HA HB HS Hp. apply (conjunction_elim Γ A B A); try assumption.
  apply arrow_intro; [exact HA |]. rewrite shift_arrow.
  apply arrow_intro; [apply formed_shift; exact HB |]. apply inhabited_shift, newest.
Qed.
Lemma conjunction_right {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed Γ B -> stable Γ B -> inhabited Γ (Conj A B) -> inhabited Γ B.
Proof.
  intros HA HB HS Hp. apply (conjunction_elim Γ A B B); try assumption.
  apply arrow_intro; [exact HA |]. rewrite shift_arrow.
  apply arrow_intro; [apply formed_shift; exact HB |]. apply newest.
Qed.
Theorem preservation {k} Ξ (A : formula k) : FunctionalSyntax.derives Ξ A ->
  forall n (Γ : Ctx nat n) env,
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  (forall i, inhabited Γ (GoodAt (env i))) ->
  (forall B, In B Ξ -> inhabited Γ (translate_formula B env)) ->
  inhabited Γ (translate_formula A env).
Proof.
  intro HD. induction HD; intros m Δ env Henv Hg Hctx.
  - apply Hctx. exact H.
  - apply FunctionalSourceAxioms.source_axiom_realized. exact H.
  - cbn [translate_formula]. apply arrow_intro; [apply formula_formed; exact Henv |].
    rewrite formula_shift. apply IHHD.
    + apply environment_shift. exact Henv.
    + apply admitted_environment_shift. exact Hg.
    + intros C [<-|HC].
      * rewrite <- formula_shift. apply newest.
      * rewrite <- formula_shift. apply inhabited_shift, Hctx. exact HC.
  - eapply arrow_elim; [apply IHHD1 |apply IHHD2]; eassumption.
  - apply conjunction_intro; [apply formula_formed |apply formula_formed |apply IHHD1 |apply IHHD2]; assumption.
  - apply (conjunction_left Δ (translate_formula A env) (translate_formula B env));
      [apply formula_formed; exact Henv |apply formula_formed; exact Henv |
      apply formula_stable; exact Henv |apply IHHD; assumption].
  - apply (conjunction_right Δ (translate_formula A env) (translate_formula B env));
      [apply formula_formed; exact Henv |apply formula_formed; exact Henv |
      apply formula_stable; exact Henv |apply IHHD; assumption].
  - cbn [translate_formula]. apply (flat_injection _ _ _ (translate_formula A env)).
    + repeat constructor; apply formula_formed; exact Henv.
    + left. reflexivity.
    + apply IHHD; assumption.
  - cbn [translate_formula]. apply (flat_injection _ _ _ (translate_formula B env)).
    + repeat constructor; apply formula_formed; exact Henv.
    + right. left. reflexivity.
    + apply IHHD; assumption.
  - apply (flat_eliminate _ [translate_formula A env; translate_formula B env]).
    + repeat constructor; apply formula_formed; exact Henv.
    + apply formula_formed. exact Henv.
    + apply formula_stable. exact Henv.
    + apply IHHD1; assumption.
    + intros D [<-|[<-|[]]]; apply arrow_intro; [apply formula_formed; exact Henv | |apply formula_formed; exact Henv |];
        rewrite formula_shift.
      * apply IHHD2.
        -- apply environment_shift. exact Henv.
        -- apply admitted_environment_shift. exact Hg.
        -- intros E [<-|HE]; rewrite <- formula_shift; [apply newest |apply inhabited_shift, Hctx; exact HE].
      * apply IHHD3.
        -- apply environment_shift. exact Henv.
        -- apply admitted_environment_shift. exact Hg.
        -- intros E [<-|HE]; rewrite <- formula_shift; [apply newest |apply inhabited_shift, Hctx; exact HE].
  - apply universal_introduction, IHHD.
    + apply environment_shift, environment_extend. exact Henv.
    + apply admitted_environment_extend. exact Hg.
    + intros C HC. apply in_map_iff in HC. destruct HC as [B [<- HB]].
      rewrite formula_source_rename.
      change (inhabited (Δ & lift_closed Domain & GoodAt V0)
        (translate_formula B (fun i => shift (shift (env i))))).
      rewrite <- !formula_shift. apply inhabited_shift, inhabited_shift, Hctx. exact HB.
  - rewrite instantiate_translation, formula_instance. apply universal_instance.
    + apply FunctionalTerms.term_typed. exact Henv.
    + apply FunctionalTerms.term_admitted; assumption.
    + apply IHHD; assumption.
  - change (inhabited Δ (Neg (translate_formula (universal (FunctionalSyntax.neg A)) env))).
    apply arrow_intro; [apply formula_formed; exact Henv |]. rewrite <- lift_closed_shift.
    assert (HU : inhabited (Δ & translate_formula (universal (FunctionalSyntax.neg A)) env)
      (translate_formula (universal (FunctionalSyntax.neg A)) (fun i => shift (env i)))).
    { rewrite <- formula_shift. apply newest. }
    pose proof (universal_instance _ _ _ (translate_term (fun i => shift (env i)) t)
      (FunctionalTerms.term_typed _ _ _ (environment_shift _ _ _ Henv))
      (FunctionalTerms.term_admitted _ _ _ (environment_shift _ _ _ Henv)
        (admitted_environment_shift _ _ _ Hg)) HU) as HN.
    cbn [FunctionalSyntax.neg translate_formula] in HN.
    eapply arrow_elim; [exact HN |].
    rewrite <- formula_instance, <- instantiate_translation.
    rewrite <- formula_shift. apply inhabited_shift. apply IHHD; assumption.
  - eapply arrow_elim; [apply formula_stable; exact Henv |].
    apply arrow_intro; [apply neg_formed, formula_formed; exact Henv |].
    rewrite <- lift_closed_shift.
    pose proof (IHHD1 _ Δ env Henv Hg Hctx) as Hex.
    change (inhabited Δ (Neg (translate_formula (universal (FunctionalSyntax.neg A)) env))) in Hex.
    weaken_copy Hex (Neg (translate_formula B env)) Hex1.
    eapply arrow_elim; [exact Hex1 |]. rewrite formula_shift. apply universal_introduction.
    cbn [FunctionalSyntax.neg translate_formula].
    apply arrow_intro.
    + apply formula_formed, environment_shift, environment_extend, environment_shift. exact Henv.
    + rewrite <- lift_closed_shift.
      set (envA := fun i => shift (shift (extend (fun j => shift (env j)) i))).
      assert (HT : forall i, Typed
        (Δ & Neg (translate_formula B env) & lift_closed Domain & GoodAt V0 &
          translate_formula A (fun i => shift (extend (fun j => shift (env j)) i)))
        (envA i) (lift_closed Domain)).
      { unfold envA. apply environment_shift, environment_shift, environment_extend, environment_shift. exact Henv. }
      assert (HG : forall i, inhabited
        (Δ & Neg (translate_formula B env) & lift_closed Domain & GoodAt V0 &
          translate_formula A (fun i => shift (extend (fun j => shift (env j)) i)))
        (GoodAt (envA i))).
      { unfold envA. apply admitted_environment_shift, admitted_environment_extend, admitted_environment_shift. exact Hg. }
      pose proof (newest Δ (Neg (translate_formula B env))) as Hnb. normalize_shifts Hnb.
      weaken_copy Hnb (@lift_closed (S m) Domain) Hnb2.
      weaken_copy Hnb2 (GoodAt (@V0 (S m))) Hnb3.
      weaken_copy Hnb3 (translate_formula A (fun i => shift (extend (fun j => shift (env j)) i))) Hnb4.
      eapply arrow_elim; [exact Hnb4 |]. rewrite !formula_shift.
      change (inhabited
        (Δ & Neg (translate_formula B env) & lift_closed Domain & GoodAt V0 &
          translate_formula A (fun i => shift (extend (fun j => shift (env j)) i)))
        (translate_formula B (fun i => envA (fsucc i)))).
      rewrite <- (formula_source_rename B fsucc envA).
      apply IHHD2; [exact HT |exact HG |].
      intros C [<-|HC].
      * pose proof (newest (Δ & Neg (translate_formula B env) & lift_closed Domain & GoodAt V0)
          (translate_formula A (fun i => shift (extend (fun j => shift (env j)) i)))) as Hnew.
        rewrite formula_shift in Hnew. exact Hnew.
      * apply in_map_iff in HC. destruct HC as [D [<- HD]].
        rewrite formula_source_rename. unfold envA.
        cbn [extend fin_match].
        rewrite <- !formula_shift. repeat apply inhabited_shift. apply Hctx. exact HD.
  - eapply arrow_elim; [apply formula_stable; exact Henv |apply IHHD; assumption].
  - apply FunctionalBounded.equality_reflexivity.
    + apply FunctionalTerms.term_typed. exact Henv.
    + apply FunctionalTerms.term_observed; assumption.
  - eapply equality_replacement; [exact Henv |exact Hg |apply IHHD1 |apply IHHD2]; assumption.
Qed.
Theorem sentence_preservation (A : formula 0) :
  FunctionalSyntax.derives [] A -> exists p, @typ nat RankSorts 0 ε p (sentence_translation A).
Proof.
  intro H. apply (preservation [] A H 0 ε FunctionalTerms.empty_env).
  - intro i. exact (match i with end).
  - intro i. exact (match i with end).
  - intros B HB. contradiction.
Qed.
End FunctionalDeduction.
