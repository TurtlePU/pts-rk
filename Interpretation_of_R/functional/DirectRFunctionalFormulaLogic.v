(** Formation and classical stability of every functional source formula. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations
  DirectRFirstOrder DirectRFunctionalTerms DirectRFunctionalTranslation
  DirectRFunctionalBounded DirectRFunctionalCases DirectRFunctionalLogic.
Import ListNotations.
Module FunctionalFormulaLogic.
Import Codes Core Structural NegativeLogic FirstOrder FunctionalTranslation.
Lemma domain_in_context {n} (Γ : Ctx nat n) : Typed Γ (lift_closed Domain) (𝓤 3).
Proof. exact (lift_closed_typed Γ _ _ Foundations.domain_formation). Qed.
Lemma environment_shift {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) B :
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  forall i, Typed (Γ & B) (shift (env i)) (lift_closed Domain).
Proof. intros H i. rewrite lift_closed_shift. apply weakening. apply H. Qed.
Lemma environment_extend {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) :
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  forall i, Typed (Γ & lift_closed Domain) (extend env i) (lift_closed Domain).
Proof.
  intros H i. dependent elimination i.
  - exact (tV (Γ & lift_closed Domain) fzero).
  - cbn [extend fin_match]. apply environment_shift. exact H.
Qed.
Lemma product_formed {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed (Γ & A) B -> formed Γ (Π A B).
Proof. intros [a Ha] [b Hb]. exists (Nat.max (S a) b). exact (tPi Ha Hb). Qed.
Theorem formula_formed {k} (A : formula k) : forall n (Γ : Ctx nat n) env,
  (forall i, Typed Γ (env i) (lift_closed Domain)) -> formed Γ (translate_formula A env).
Proof.
  induction A; intros m Γ env Henv; cbn [translate_formula].
  - exists 6. apply FunctionalBounded.equality_formation; apply FunctionalTerms.term_typed; exact Henv.
  - exists 6. apply FunctionalBounded.order_formation; apply FunctionalTerms.term_typed; exact Henv.
  - exists 1. apply bottom_in_context.
  - apply arrow_formed; [apply IHA1 |apply IHA2]; exact Henv.
  - unfold Conj. apply neg_formed, arrow_formed; [apply IHA1; exact Henv |].
    apply arrow_formed; [apply IHA2; exact Henv |exists 1; apply bottom_in_context].
  - apply flat_formed. repeat constructor; [apply IHA1 |apply IHA2]; exact Henv.
  - apply product_formed; [exists 3; apply domain_in_context |].
    apply arrow_formed.
    + exists 12. apply FunctionalCases.good_at_formation.
      exact (tV (Γ & lift_closed Domain) fzero).
    + apply IHA, environment_extend. exact Henv.
  - apply neg_formed, product_formed;
      [exists 3; apply domain_in_context |].
    apply arrow_formed.
    + exists 12. apply FunctionalCases.good_at_formation.
      exact (tV (Γ & lift_closed Domain) fzero).
    + apply arrow_formed; [apply IHA, environment_extend; exact Henv |exists 1; apply bottom_in_context].
Qed.
Lemma formula_shift {k n} A (env : Fin k -> Term nat n) :
  shift (translate_formula A env) = translate_formula A (fun i => shift (env i)).
Proof. apply formula_rename. Qed.
Lemma formula_instance {k n} A (env : Fin k -> Term nat n) d :
  subst (translate_formula A (extend env)) d = translate_formula A (fin_match d env).
Proof.
  unfold subst. rewrite formula_replace. apply formula_ext. intro i.
  dependent elimination i; cbn [extend fin_match]; [reflexivity |].
  apply replace_shift_substitution.
Qed.
Theorem universal_introduction {k n} (Γ : Ctx nat n) env (A : formula (S k)) :
  inhabited ((Γ & lift_closed Domain) & GoodAt V0)
    (translate_formula A (fun i => shift (extend env i))) ->
  inhabited Γ (translate_formula (universal A) env).
Proof.
  intro H. cbn [translate_formula]. apply product_intro.
  - exists 3. apply domain_in_context.
  - apply arrow_intro.
    + exists 12. apply FunctionalCases.good_at_formation.
      exact (tV (Γ & lift_closed Domain) fzero).
    + rewrite formula_shift. exact H.
Qed.
Lemma universal_instance {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) A d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) ->
  inhabited Γ (translate_formula (universal A) env) ->
  inhabited Γ (translate_formula A (fin_match d env)).
Proof.
  intros Hd Hg [p Hp]. pose proof (tApp Hp Hd) as H.
  change (Typed Γ (app p d)
    (subst (Arrow (GoodAt V0) (translate_formula A (extend env))) d)) in H.
  rewrite subst_arrow in H.
  change (Typed Γ (app p d)
    (Arrow (GoodAt d) (subst (translate_formula A (extend env)) d))) in H.
  rewrite formula_instance in H.
  eapply arrow_elim; [exists (app p d); exact H |exact Hg].
Qed.
Lemma instance_environment {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) d :
  (forall i, Typed Γ (env i) (lift_closed Domain)) -> Typed Γ d (lift_closed Domain) ->
  forall i, Typed Γ (fin_match d env i) (lift_closed Domain).
Proof. intros H Hd i. dependent elimination i; [exact Hd |apply H]. Qed.
Lemma universal_instance_arrow {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) A d :
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) ->
  inhabited Γ (Arrow (translate_formula (universal A) env) (translate_formula A (fin_match d env))).
Proof.
  intros Henv Hd Hg. apply arrow_intro.
  - apply formula_formed. exact Henv.
  - rewrite formula_shift.
    replace (translate_formula A (fun i => shift (fin_match d env i))) with
      (translate_formula A (fin_match (shift d) (fun i => shift (env i)))).
    + apply universal_instance.
      * rewrite lift_closed_shift. apply weakening. exact Hd.
      * exact (inhabited_shift _ _ _ Hg).
      * rewrite <- formula_shift. apply newest.
    + apply formula_ext. intro i. dependent elimination i; reflexivity.
Qed.
Theorem formula_stable {k} (A : formula k) : forall n (Γ : Ctx nat n) env,
  (forall i, Typed Γ (env i) (lift_closed Domain)) -> stable Γ (translate_formula A env).
Proof.
  induction A; intros m Γ env Henv; cbn [translate_formula].
  - apply FunctionalLogic.equality_stable; apply FunctionalTerms.term_typed; exact Henv.
  - apply FunctionalLogic.order_stable; apply FunctionalTerms.term_typed; exact Henv.
  - apply bottom_stable.
  - apply arrow_stable.
    + apply formula_formed. exact Henv.
    + apply formula_formed. exact Henv.
    + apply IHA2. exact Henv.
  - unfold Conj, Neg. apply arrow_stable.
    + apply arrow_formed; [apply formula_formed; exact Henv |].
      apply arrow_formed; [apply formula_formed; exact Henv |exists 1; apply bottom_in_context].
    + exists 1. apply bottom_in_context.
    + apply bottom_stable.
  - apply flat_stable. repeat constructor; apply formula_formed; exact Henv.
  - change (stable Γ (translate_formula (universal A) env)).
    unfold stable. set (H := Neg (Neg (translate_formula (universal A) env))).
    apply arrow_intro.
    + unfold H. apply neg_formed, neg_formed, formula_formed. exact Henv.
    + rewrite formula_shift. apply universal_introduction.
      set (env2 := fun i => shift (extend (fun j => shift (env j)) i)).
      set (env3 := fun i => shift (shift (shift (env i)))).
      assert (HT2 : forall i, Typed ((Γ & H) & lift_closed Domain & GoodAt V0)
        (env2 i) (lift_closed Domain)).
      { unfold env2. apply environment_shift, environment_extend, environment_shift. exact Henv. }
      eapply arrow_elim; [exact (IHA _ _ env2 HT2) |].
      assert (HT3 : forall i, Typed ((Γ & H) & lift_closed Domain & GoodAt V0)
        (env3 i) (lift_closed Domain)).
      { unfold env3. apply environment_shift, environment_shift, environment_shift. exact Henv. }
      assert (HE : translate_formula A env2 = translate_formula A (fin_match (shift V0) env3)).
      { apply formula_ext. intro i. dependent elimination i; reflexivity. }
      rewrite HE.
      assert (Hd : Typed ((Γ & H) & lift_closed Domain & GoodAt V0)
        (shift V0) (lift_closed Domain)).
      { pose proof (weakening RankSorts _ _ (GoodAt V0)
          (tV ((Γ & H) & lift_closed Domain) fzero)) as Hv.
        change (Typed ((Γ & H) & lift_closed Domain & GoodAt V0)
          (shift V0) (shift (shift (lift_closed Domain)))) in Hv.
        rewrite <- !lift_closed_shift in Hv. exact Hv. }
      eapply (double_negation_map _ (translate_formula (universal A) env3)).
      * apply formula_formed. exact HT3.
      * apply formula_formed, instance_environment; eassumption.
      * apply universal_instance_arrow; [exact HT3 |exact Hd |].
        exact (newest ((Γ & H) & lift_closed Domain) (GoodAt V0)).
      * pose proof (newest Γ H) as Hnn.
        unfold H in Hnn. normalize_shifts Hnn.
        weaken_copy Hnn (@lift_closed (S m) Domain) Hnn2.
        weaken_copy Hnn2 (GoodAt (@V0 (S m))) Hnn3.
        rewrite !formula_shift in Hnn3. exact Hnn3.
  - unfold Neg. apply arrow_stable.
    + apply product_formed; [exists 3; apply domain_in_context |].
      apply arrow_formed.
      * exists 12. apply FunctionalCases.good_at_formation.
        exact (tV (Γ & lift_closed Domain) fzero).
      * apply arrow_formed; [apply formula_formed, environment_extend; exact Henv |].
        exists 1. apply bottom_in_context.
    + exists 1. apply bottom_in_context.
    + apply bottom_stable.
Qed.
End FunctionalFormulaLogic.
