(** Equality replacement for arbitrary functional terms. Each binary
    congruence uses the actual Church operation and both Good15 environments. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import AbstractRewriting DefEq Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural
  DirectRLogic DirectRFiniteUp DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary.
From OrderedSemiring Require Import RigCodes ObservationEquality ArithmeticCongruence
  SemiringLaws OrderLaws ModelInterface FirstOrderEquality.
From OrderedSemiringFunctional Require Import Source Translation.
Import ListNotations.
Module FunctionalEquality.
Import CommonCodes Core Structural NegativeLogic FunctionalTranslation.

Module Codes := FirstOrderEquality.Codes.

Lemma symmetry {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d e) -> inhabited Γ (Model.E e d).
Proof. apply FirstOrderEquality.symmetry. Qed.
Lemma transitivity {n} (Γ : Ctx nat n) d e f :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  Typed Γ f (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d e) -> inhabited Γ (Model.E e f) -> inhabited Γ (Model.E d f).
Proof. apply FirstOrderEquality.transitivity. Qed.
Lemma successor_congruence {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d e) ->
  inhabited Γ (Model.E (app (lift_closed Model.successor) d) (app (lift_closed Model.successor) e)).
Proof. apply FirstOrderEquality.successor_congruence. Qed.
Lemma equality_transport {n} (Γ : Ctx nat n) d d' e e' :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ d' (lift_closed Model.Domain) ->
  Typed Γ e (lift_closed Model.Domain) -> Typed Γ e' (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d d') -> inhabited Γ (Model.E e e') ->
  inhabited Γ (Model.E d e) -> inhabited Γ (Model.E d' e').
Proof. apply FirstOrderEquality.equality_transport. Qed.
Lemma order_transport {n} (Γ : Ctx nat n) d d' e e' :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ d' (lift_closed Model.Domain) ->
  Typed Γ e (lift_closed Model.Domain) -> Typed Γ e' (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d d') -> inhabited Γ (Model.E e e') ->
  inhabited Γ (Model.O d e) -> inhabited Γ (Model.O d' e').
Proof. apply FirstOrderEquality.order_transport. Qed.

(** The two permitted binary operations, with their concrete certificates. *)
Definition source_operator (addition : bool) :=
  if addition then Model.addition else Model.multiplication.
Lemma source_binary_congruence {n} (Γ : Ctx nat n) b witness d d' e e' :
  Typed ε witness (Codes.source_congruence_type (source_operator b)) ->
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ d' (lift_closed Model.Domain) ->
  Typed Γ e (lift_closed Model.Domain) -> Typed Γ e' (lift_closed Model.Domain) ->
  inhabited Γ (Model.admitted d) -> inhabited Γ (Model.admitted d') ->
  inhabited Γ (Model.admitted e) -> inhabited Γ (Model.admitted e') ->
  inhabited Γ (Model.E d d') -> inhabited Γ (Model.E e e') ->
  inhabited Γ (Model.E (app (app (lift_closed (source_operator b)) d) e)
    (app (app (lift_closed (source_operator b)) d') e')).
Proof. apply FirstOrderEquality.source_binary_congruence. Qed.
Lemma shift_E {n} (d e : Term nat n) : shift (Model.E d e) = Model.E (shift d) (shift e).
Proof. apply FirstOrderEquality.shift_E. Qed.
Lemma related_shift {k n} (Γ : Ctx nat n) (env env' : Fin k -> Term nat n) B :
  (forall i, inhabited Γ (Model.E (env i) (env' i))) ->
  forall i, inhabited (Γ & B) (Model.E (shift (env i)) (shift (env' i))).
Proof. apply FirstOrderEquality.related_shift. Qed.

Lemma term_congruence {k} (t : FunctionalSource.term k) : forall n (Γ : Ctx nat n) env env',
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  (forall i, Typed Γ (env' i) (lift_closed Model.Domain)) ->
  (forall i, inhabited Γ (Model.admitted (env i))) ->
  (forall i, inhabited Γ (Model.admitted (env' i))) ->
  (forall i, inhabited Γ (Model.E (env i) (env' i))) ->
  inhabited Γ (Model.E (term env t) (term env' t)).
Proof.
  induction t; intros m Γ env env' Henv Henv' Hgood Hgood' HE; cbn [term].
  - apply HE.
  - apply equality_reflexivity_in_context. exact (lift_closed_typed Γ _ _ Model.zero_typed).
  - apply successor_congruence.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply IHt; assumption.
  - apply (source_binary_congruence Γ true Codes.addition_congruence).
    + apply Codes.addition_congruence_typed.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply term_admitted; assumption.
    + apply term_admitted; assumption.
    + apply term_admitted; assumption.
    + apply term_admitted; assumption.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - apply (source_binary_congruence Γ false Codes.multiplication_congruence).
    + apply Codes.multiplication_congruence_typed.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply term_admitted; assumption.
    + apply term_admitted; assumption.
    + apply term_admitted; assumption.
    + apply term_admitted; assumption.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

Theorem formula_transport {k} (A : FunctionalSource.formula k) : forall n (Γ : Ctx nat n) env env',
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  (forall i, Typed Γ (env' i) (lift_closed Model.Domain)) ->
  (forall i, inhabited Γ (Model.admitted (env i))) ->
  (forall i, inhabited Γ (Model.admitted (env' i))) ->
  (forall i, inhabited Γ (Model.E (env i) (env' i))) ->
  inhabited Γ (formula A env) -> inhabited Γ (formula A env').
Proof.
  induction A; intros m Γ env env' Henv Henv' Hgood Hgood' HE Hp; cbn [formula] in Hp |- *.
  - apply (equality_transport Γ (term env t) (term env' t) (term env t0) (term env' t0)).
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply term_congruence; assumption.
    + apply term_congruence; assumption.
    + exact Hp.
  - apply (order_transport Γ (term env t) (term env' t) (term env t0) (term env' t0)).
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply term_congruence; assumption.
    + apply term_congruence; assumption.
    + exact Hp.
  - exact Hp.
  - apply arrow_intro.
    + exists (formula_rank A1). apply formula_typed. exact Henv'.
    + rewrite formula_shift.
      apply (IHA2 _ _ (fun i => shift (env i)) (fun i => shift (env' i))).
      * apply environment_shift. exact Henv.
      * apply environment_shift. exact Henv'.
      * apply admitted_environment_shift. exact Hgood.
      * apply admitted_environment_shift. exact Hgood'.
      * apply related_shift. exact HE.
      * pose proof (inhabited_shift _ _ (formula A1 env') Hp) as Himp.
        rewrite shift_arrow, !formula_shift in Himp.
        eapply arrow_elim; [exact Himp |].
        apply (IHA1 _ _ (fun i => shift (env' i)) (fun i => shift (env i))).
        -- apply environment_shift. exact Henv'.
        -- apply environment_shift. exact Henv.
        -- apply admitted_environment_shift. exact Hgood'.
        -- apply admitted_environment_shift. exact Hgood.
        -- apply related_shift. intro i. apply symmetry; [apply Henv |apply Henv' |apply HE].
        -- rewrite <- formula_shift. apply newest.
  - change (inhabited Γ (formula (FunctionalSource.all A) env)) in Hp.
    change (inhabited Γ (formula (FunctionalSource.all A) env')).
    apply universal_introduction.
    apply (IHA _ _ (fun i => shift (transpose env i)) (fun i => shift (transpose env' i))).
    + apply environment_shift, environment_transpose. exact Henv.
    + apply environment_shift, environment_transpose. exact Henv'.
    + apply admitted_environment_transpose. exact Hgood.
    + apply admitted_environment_transpose. exact Hgood'.
    + intro i. dependent elimination i.
      * apply equality_reflexivity_in_context.
        pose proof (weakening RankSorts _ _ (Model.admitted V0)
          (tV (Γ & lift_closed Model.Domain) fzero)) as Hv.
        change (Typed (Γ & lift_closed Model.Domain & Model.admitted V0)
          (shift V0) (shift (shift (lift_closed Model.Domain)))) in Hv.
        rewrite <- !lift_closed_shift in Hv. exact Hv.
      * cbn [transpose fin_match].
        pose proof (inhabited_shift _ _ (Model.admitted V0)
          (inhabited_shift Γ _ (lift_closed Model.Domain) (HE f))) as Heq.
        rewrite !shift_E in Heq. exact Heq.
    + replace (formula A (fun i => shift (transpose env i))) with
        (formula A (fin_match (shift V0) (fun i => shift (shift (env i))))).
      * apply universal_instance.
        -- pose proof (weakening RankSorts _ _ (Model.admitted V0)
             (tV (Γ & lift_closed Model.Domain) fzero)) as Hv.
           change (Typed (Γ & lift_closed Model.Domain & Model.admitted V0)
             (shift V0) (shift (shift (lift_closed Model.Domain)))) in Hv.
           rewrite <- !lift_closed_shift in Hv. exact Hv.
        -- exact (newest (Γ & lift_closed Model.Domain) (Model.admitted V0)).
        -- rewrite <- !formula_shift. apply inhabited_shift, inhabited_shift. exact Hp.
      * apply formula_ext. intro i. dependent elimination i; reflexivity.
Qed.

Theorem equality_replacement {k n} (Γ : Ctx nat n) env (A : FunctionalSource.formula (S k)) t u :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  (forall i, inhabited Γ (Model.admitted (env i))) ->
  inhabited Γ (formula (FunctionalSource.equal t u) env) ->
  inhabited Γ (formula (FunctionalSource.instantiate A t) env) ->
  inhabited Γ (formula (FunctionalSource.instantiate A u) env).
Proof.
  intros Henv Hgood Heq Ht. rewrite !instantiate_translation, !formula_instance in Ht |- *.
  apply (formula_transport A _ Γ (fin_match (term env t) env) (fin_match (term env u) env)).
  - apply instance_environment; [exact Henv |apply term_typed; exact Henv].
  - apply instance_environment; [exact Henv |apply term_typed; exact Henv].
  - intro i. dependent elimination i; [apply term_admitted; assumption |apply Hgood].
  - intro i. dependent elimination i; [apply term_admitted; assumption |apply Hgood].
  - intro i. dependent elimination i; [exact Heq |apply equality_reflexivity_in_context, Henv].
  - exact Ht.
Qed.
Print Assumptions term_congruence.
Print Assumptions formula_transport.
Print Assumptions equality_replacement.
End FunctionalEquality.
