(** Equality transport for the original functional carrier. Observation
    premises are supplied by Good admission, never silently dropped. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations
  DirectRFirstOrder DirectRFunctionalSyntax DirectRFunctionalTranslation
  DirectRFunctionalFormulaLogic DirectRFunctionalTerms DirectRFunctionalBounded
  DirectRFunctionalAddition DirectRFunctionalMultiplication.
Import ListNotations.
Module FunctionalEquality.
Import Codes Core Structural NegativeLogic FirstOrder FunctionalTranslation FunctionalFormulaLogic.
Lemma symmetry {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  inhabited Γ (GAt d) -> inhabited Γ (GAt e) ->
  inhabited Γ (EqAt d e) -> inhabited Γ (EqAt e d).
Proof.
  intros Hd He [gd Hgd] [ge Hge] [p Hp].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_eq_sym_typed) as H.
  change (Typed Γ (lift_closed Law_eq_sym)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Arrow (EqAt (shift V0) V0) (EqAt V0 (shift V0)))))))) in H.
  Foundations.feed_object H Hd. Foundations.feed_arrow H Hgd.
  Foundations.feed_object H He. Foundations.feed_arrow H Hge.
  Foundations.feed_arrow H Hp. eexists. exact H.
Qed.
Lemma term_congruence {k} (t : term k) : forall n (Γ : Ctx nat n) env env',
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  (forall i, Typed Γ (env' i) (lift_closed Domain)) ->
  (forall i, inhabited Γ (GoodAt (env i))) ->
  (forall i, inhabited Γ (GoodAt (env' i))) ->
  (forall i, inhabited Γ (EqAt (env i) (env' i))) ->
  inhabited Γ (EqAt (translate_term env t) (translate_term env' t)).
Proof.
  induction t; intros m Γ env env' Henv Henv' Hg Hg' HE; cbn [translate_term].
  - apply HE.
  - apply FunctionalBounded.equality_reflexivity.
    + exact (lift_closed_typed Γ _ _ Foundations.zero_typed).
    + exists (lift_closed g_zero_proof). exact (lift_closed_typed Γ _ _ Foundations.observed_zero_typed).
  - apply FunctionalBounded.successor_congruence;
      eauto using FunctionalTerms.term_typed, FunctionalTerms.term_observed.
  - apply FunctionalAddition.addition_congruence;
      eauto using FunctionalTerms.term_typed, FunctionalTerms.term_observed.
  - apply FunctionalMultiplication.multiplication_congruence;
      eauto using FunctionalTerms.term_typed, FunctionalTerms.term_observed.
Qed.
Lemma equality_transport {n} (Γ : Ctx nat n) d d' e e' :
  Typed Γ d (lift_closed Domain) -> Typed Γ d' (lift_closed Domain) ->
  Typed Γ e (lift_closed Domain) -> Typed Γ e' (lift_closed Domain) ->
  inhabited Γ (GAt d) -> inhabited Γ (GAt d') ->
  inhabited Γ (GAt e) -> inhabited Γ (GAt e') ->
  inhabited Γ (EqAt d d') -> inhabited Γ (EqAt e e') ->
  inhabited Γ (EqAt d e) -> inhabited Γ (EqAt d' e').
Proof.
  intros Hd Hd' He He' Gd Gd' Ge Ge' Hdd Hee Hde.
  apply (FunctionalAddition.equality_transitivity Γ d' e e'); try assumption.
  apply (FunctionalAddition.equality_transitivity Γ d' d e); try assumption.
  apply symmetry; assumption.
Qed.
Lemma admitted_environment_shift {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) B :
  (forall i, inhabited Γ (GoodAt (env i))) ->
  forall i, inhabited (Γ & B) (GoodAt (shift (env i))).
Proof. intros H i. exact (inhabited_shift Γ _ B (H i)). Qed.
Lemma related_shift {k n} (Γ : Ctx nat n) (env env' : Fin k -> Term nat n) B :
  (forall i, inhabited Γ (EqAt (env i) (env' i))) ->
  forall i, inhabited (Γ & B) (EqAt (shift (env i)) (shift (env' i))).
Proof. intros H i. exact (inhabited_shift Γ _ B (H i)). Qed.
Lemma related_symmetry {k n} (Γ : Ctx nat n) (env env' : Fin k -> Term nat n) :
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  (forall i, Typed Γ (env' i) (lift_closed Domain)) ->
  (forall i, inhabited Γ (GoodAt (env i))) ->
  (forall i, inhabited Γ (GoodAt (env' i))) ->
  (forall i, inhabited Γ (EqAt (env i) (env' i))) ->
  forall i, inhabited Γ (EqAt (env' i) (env i)).
Proof.
  intros Henv Henv' Hg Hg' HE i. apply symmetry; auto;
    apply FunctionalTerms.admitted_observed; auto.
Qed.
Lemma admitted_environment_extend {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) :
  (forall i, inhabited Γ (GoodAt (env i))) ->
  forall i, inhabited (Γ & lift_closed Domain & GoodAt V0) (GoodAt (shift (extend env i))).
Proof.
  intros H i. dependent elimination i.
  - exact (newest (Γ & lift_closed Domain) (GoodAt V0)).
  - cbn [extend fin_match]. exact (inhabited_shift _ _ (GoodAt V0)
      (inhabited_shift Γ _ (lift_closed Domain) (H f))).
Qed.
Lemma related_extend {k n} (Γ : Ctx nat n) (env env' : Fin k -> Term nat n) :
  (forall i, inhabited Γ (EqAt (env i) (env' i))) ->
  forall i, inhabited (Γ & lift_closed Domain & GoodAt V0)
    (EqAt (shift (extend env i)) (shift (extend env' i))).
Proof.
  intros H i. dependent elimination i.
  - apply FunctionalBounded.equality_reflexivity.
    + exact (tV (Γ & lift_closed Domain & GoodAt V0) (fsucc fzero)).
    + apply FunctionalTerms.admitted_observed.
      * exact (tV (Γ & lift_closed Domain & GoodAt V0) (fsucc fzero)).
      * exact (newest (Γ & lift_closed Domain) (GoodAt V0)).
  - cbn [extend fin_match]. exact (inhabited_shift _ _ (GoodAt V0)
      (inhabited_shift Γ _ (lift_closed Domain) (H f))).
Qed.
(** This is a property to be proved by induction, not a premise added to the
    source proof system or the domain. It quantifies over actual PTS contexts. *)
Definition transportable {k} (A : formula k) :=
  forall n (Γ : Ctx nat n) env env',
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  (forall i, Typed Γ (env' i) (lift_closed Domain)) ->
  (forall i, inhabited Γ (GoodAt (env i))) ->
  (forall i, inhabited Γ (GoodAt (env' i))) ->
  (forall i, inhabited Γ (EqAt (env i) (env' i))) ->
  inhabited Γ (translate_formula A env) -> inhabited Γ (translate_formula A env').
Lemma falsity_transportable {k} : transportable (@falsity k).
Proof. intros n Γ env env' Henv Henv' Hg Hg' HE Hp. exact Hp. Qed.
Lemma implication_transportable {k} (A B : formula k) :
  transportable A -> transportable B -> transportable (implication A B).
Proof.
  intros HA HB m Γ env env' Henv Henv' Hg Hg' HE Hp.
  cbn [translate_formula] in Hp |- *. apply arrow_intro.
  - apply formula_formed. exact Henv'.
  - rewrite formula_shift.
    apply (HB _ _ (fun i => shift (env i)) (fun i => shift (env' i))).
    + apply environment_shift. exact Henv.
    + apply environment_shift. exact Henv'.
    + apply admitted_environment_shift. exact Hg.
    + apply admitted_environment_shift. exact Hg'.
    + apply related_shift. exact HE.
    + pose proof (inhabited_shift _ _ (translate_formula A env') Hp) as Himp.
      rewrite shift_arrow, !formula_shift in Himp.
      eapply arrow_elim; [exact Himp |].
      apply (HA _ _ (fun i => shift (env' i)) (fun i => shift (env i))).
      * apply environment_shift. exact Henv'.
      * apply environment_shift. exact Henv.
      * apply admitted_environment_shift. exact Hg'.
      * apply admitted_environment_shift. exact Hg.
      * apply related_shift, related_symmetry; assumption.
      * rewrite <- formula_shift. apply newest.
Qed.
Lemma neg_transportable {k} (A : formula k) :
  transportable A -> transportable (FunctionalSyntax.neg A).
Proof. intro H. apply implication_transportable; [exact H |apply falsity_transportable]. Qed.
Lemma universal_transportable {k} (A : formula (S k)) :
  transportable A -> transportable (universal A).
Proof.
  intros HA m Γ env env' Henv Henv' Hg Hg' HE Hp.
  apply universal_introduction.
  apply (HA _ _ (fun i => shift (extend env i)) (fun i => shift (extend env' i))).
  - apply environment_shift, environment_extend. exact Henv.
  - apply environment_shift, environment_extend. exact Henv'.
  - apply admitted_environment_extend. exact Hg.
  - apply admitted_environment_extend. exact Hg'.
  - apply related_extend. exact HE.
  - replace (translate_formula A (fun i => shift (extend env i))) with
      (translate_formula A (fin_match (shift V0) (fun i => shift (shift (env i))))).
    + apply universal_instance.
      * exact (tV (Γ & lift_closed Domain & GoodAt V0) (fsucc fzero)).
      * exact (newest (Γ & lift_closed Domain) (GoodAt V0)).
      * rewrite <- !formula_shift. apply inhabited_shift, inhabited_shift. exact Hp.
    + apply formula_ext. intro i. dependent elimination i; reflexivity.
Qed.
Theorem formula_transport {k} (A : formula k) : transportable A.
Proof.
  induction A.
  - intros m Γ env env' Henv Henv' Hg Hg' HE Hp.
    cbn [translate_formula] in Hp |- *.
    apply (equality_transport Γ (translate_term env t) (translate_term env' t)
      (translate_term env t0) (translate_term env' t0));
      eauto using FunctionalTerms.term_typed, FunctionalTerms.term_observed, term_congruence.
  - intros m Γ env env' Henv Henv' Hg Hg' HE Hp.
    cbn [translate_formula] in Hp |- *.
    apply (FunctionalBounded.order_congruence Γ (translate_term env t) (translate_term env' t)
      (translate_term env t0) (translate_term env' t0));
      eauto using FunctionalTerms.term_typed, FunctionalTerms.term_observed, term_congruence.
  - apply falsity_transportable.
  - apply implication_transportable; assumption.
  - change (transportable (FunctionalSyntax.neg (implication A1 (implication A2 falsity)))).
    apply neg_transportable, implication_transportable; [exact IHA1 |].
    apply implication_transportable; [exact IHA2 |apply falsity_transportable].
  - change (transportable (implication (FunctionalSyntax.neg A1)
      (implication (FunctionalSyntax.neg A2) falsity))).
    apply implication_transportable; [apply neg_transportable; exact IHA1 |].
    apply implication_transportable; [apply neg_transportable; exact IHA2 |apply falsity_transportable].
  - apply universal_transportable. exact IHA.
  - change (transportable (FunctionalSyntax.neg (universal (FunctionalSyntax.neg A)))).
    apply neg_transportable, universal_transportable, neg_transportable. exact IHA.
Qed.
Theorem equality_replacement {k n} (Γ : Ctx nat n) env (A : formula (S k)) t u :
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  (forall i, inhabited Γ (GoodAt (env i))) ->
  inhabited Γ (translate_formula (equal t u) env) ->
  inhabited Γ (translate_formula (FunctionalSyntax.instantiate A t) env) ->
  inhabited Γ (translate_formula (FunctionalSyntax.instantiate A u) env).
Proof.
  intros Henv Hg Heq Ht. rewrite !instantiate_translation, !formula_instance in Ht |- *.
  apply (formula_transport A _ Γ (fin_match (translate_term env t) env)
    (fin_match (translate_term env u) env)).
  - apply instance_environment; [exact Henv |apply FunctionalTerms.term_typed; exact Henv].
  - apply instance_environment; [exact Henv |apply FunctionalTerms.term_typed; exact Henv].
  - intro i. dependent elimination i; [apply FunctionalTerms.term_admitted; assumption |apply Hg].
  - intro i. dependent elimination i; [apply FunctionalTerms.term_admitted; assumption |apply Hg].
  - intro i. dependent elimination i; [exact Heq |].
    apply FunctionalBounded.equality_reflexivity; [apply Henv |].
    apply FunctionalTerms.admitted_observed; [apply Henv |apply Hg].
  - exact Ht.
Qed.
End FunctionalEquality.
