(** Extensional equality transport for the independent relational language. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import AbstractRewriting DefEq Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural
  DirectRLogic DirectRFiniteUp.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryAxioms
  DirectRRelationalSyntax DirectRRelationalTranslation.
Module RelationalEquality.
Import CommonCodes Core Structural NegativeLogic RelationalTranslation.

Lemma symmetry {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (Unary.E d e) -> inhabited Γ (Unary.E e d).
Proof.
  intros Hd He [p Hp]. eexists. exact (Unary.equality_symmetry_in_context Γ _ _ _ Hd He Hp).
Qed.
Lemma transitivity {n} (Γ : Ctx nat n) d e f :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ f (lift_closed Unary.Domain) ->
  inhabited Γ (Unary.E d e) -> inhabited Γ (Unary.E e f) -> inhabited Γ (Unary.E d f).
Proof.
  intros Hd He Hf [p Hp] [q Hq].
  pose proof (lift_closed_typed Γ _ _ Unary.equality_transitivity_typed) as H.
  change (Typed Γ (lift_closed Unary.equality_transitivity)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (Unary.E (shift (shift V0)) (shift V0))
        (Arrow (Unary.E (shift V0) V0) (Unary.E (shift (shift V0)) V0))))))) in H.
  Unary.feed H Hd. Unary.feed H He. Unary.feed H Hf.
  Unary.feed_arrow H Hp. Unary.feed_arrow H Hq. eexists. exact H.
Qed.
Lemma congruence {n} (Γ : Ctx nat n) f d e :
  Typed Γ f (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain)) ->
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (Unary.E d e) -> inhabited Γ (Unary.E (app f d) (app f e)).
Proof.
  intros Hf Hd He [p Hp]. eexists.
  exact (Unary.equality_congruence_in_context Γ _ _ _ _ Hf Hd He Hp).
Qed.
Lemma term_congruence {k} (t : Relational.term k) : forall n (Γ : Ctx nat n) env env',
  (forall i, Typed Γ (env i) (lift_closed Unary.Domain)) ->
  (forall i, Typed Γ (env' i) (lift_closed Unary.Domain)) ->
  (forall i, inhabited Γ (Unary.E (env i) (env' i))) ->
  inhabited Γ (Unary.E (term env t) (term env' t)).
Proof.
  induction t; intros m Γ env env' Henv Henv' HE; cbn [term].
  - apply HE.
  - apply equality_reflexivity_in_context. exact (lift_closed_typed Γ _ _ Unary.zero_typed).
  - apply congruence; [apply Unary.successor_in_context | | |].
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply IHt; assumption.
Qed.
Lemma equality_transport {n} (Γ : Ctx nat n) d d' e e' :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ d' (lift_closed Unary.Domain) ->
  Typed Γ e (lift_closed Unary.Domain) -> Typed Γ e' (lift_closed Unary.Domain) ->
  inhabited Γ (Unary.E d d') -> inhabited Γ (Unary.E e e') ->
  inhabited Γ (Unary.E d e) -> inhabited Γ (Unary.E d' e').
Proof.
  intros Hd Hd' He He' Hdd Hee Hde.
  eapply transitivity; [exact Hd' |exact He |exact He' | |exact Hee].
  eapply transitivity; [exact Hd' |exact Hd |exact He | |exact Hde].
  apply symmetry; assumption.
Qed.
Lemma order_transport {n} (Γ : Ctx nat n) d d' e e' :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ d' (lift_closed Unary.Domain) ->
  Typed Γ e (lift_closed Unary.Domain) -> Typed Γ e' (lift_closed Unary.Domain) ->
  inhabited Γ (Unary.E d d') -> inhabited Γ (Unary.E e e') ->
  inhabited Γ (Unary.O d e) -> inhabited Γ (Unary.O d' e').
Proof.
  intros Hd Hd' He He' Hdd [q Hq] [p Hp].
  destruct (symmetry Γ _ _ Hd Hd' Hdd) as [r Hr].
  pose proof (Unary.equality_order_in_context Γ _ _ _ Hd' Hd Hr) as Hleft.
  pose proof (Unary.equality_order_in_context Γ _ _ _ He He' Hq) as Hright.
  pose proof (Unary.order_transitivity_in_context Γ _ _ _ _ _ Hd' Hd He Hleft Hp) as Hmid.
  eexists. exact (Unary.order_transitivity_in_context Γ _ _ _ _ _ Hd' He He' Hmid Hright).
Qed.
Lemma binary_congruence {n} (Γ : Ctx nat n) op d d' e e' :
  Typed Γ op (Arrow (lift_closed Unary.Domain)
    (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))) ->
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ d' (lift_closed Unary.Domain) ->
  Typed Γ e (lift_closed Unary.Domain) -> Typed Γ e' (lift_closed Unary.Domain) ->
  inhabited Γ (Unary.E d d') -> inhabited Γ (Unary.E e e') ->
  inhabited Γ (Unary.E (app (app op d) e) (app (app op d') e')).
Proof.
  intros Hop Hd Hd' He He' Hdd Hee.
  set (f := lam (lift_closed Unary.Domain) (app (app (shift op) V0) (shift e))).
  assert (Hf : Typed Γ f (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))).
  { unfold f, Arrow at 1. apply (tLam (lift_closed_typed Γ _ _ Unary.domain_formation)).
    rewrite <- lift_closed_shift.
    pose proof (weakening RankSorts _ _ (lift_closed Unary.Domain) Hop) as Hop'.
    rewrite !shift_arrow, <- !lift_closed_shift in Hop'.
    pose proof (tV (Γ & lift_closed Unary.Domain) fzero) as Hv.
    pose proof (weakening RankSorts _ _ (lift_closed Unary.Domain) He) as He1.
    change (Typed (Γ & lift_closed Unary.Domain) V0 (shift (lift_closed Unary.Domain))) in Hv.
    rewrite <- lift_closed_shift in Hv, He1.
    eapply arrow_application; [eapply arrow_application; [exact Hop' |exact Hv] |exact He1]. }
  assert (Hbeta : forall u, app f u =ᵝ app (app op u) e).
  { intro u. unfold f. eapply beta_trans; [apply beta_contract |].
    rewrite !subst_app, !substitute_shift, subst_V0. apply beta_refl. }
  assert (Hleft : inhabited Γ (Unary.E (app (app op d) e) (app (app op d') e))).
  { eapply FiniteUp.inhabited_conversion.
    - exact (congruence Γ f d d' Hf Hd Hd' Hdd).
    - apply Unary.equality_in_context.
      + eapply arrow_application; [eapply arrow_application; [exact Hop |exact Hd] |exact He].
      + eapply arrow_application; [eapply arrow_application; [exact Hop |exact Hd'] |exact He].
    - unfold Unary.E. apply beta_app; [apply beta_app; [apply beta_refl |apply Hbeta] |apply Hbeta]. }
  assert (Hpartial : Typed Γ (app op d') (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))).
  { eapply arrow_application; eassumption. }
  apply (transitivity Γ (app (app op d) e) (app (app op d') e) (app (app op d') e')).
  - eapply arrow_application; [eapply arrow_application; [exact Hop |exact Hd] |exact He].
  - eapply arrow_application; [exact Hpartial |exact He].
  - eapply arrow_application; [exact Hpartial |exact He'].
  - exact Hleft.
  - apply congruence; assumption.
Qed.
Lemma related_shift {k n} (Γ : Ctx nat n) (env env' : Fin k -> Term nat n) B :
  (forall i, inhabited Γ (Unary.E (env i) (env' i))) ->
  forall i, inhabited (Γ & B) (Unary.E (shift (env i)) (shift (env' i))).
Proof.
  intros H i. rewrite <- Unary.shift_E. apply inhabited_shift. apply H.
Qed.
Theorem formula_transport {k} (A : Relational.formula k) : forall n (Γ : Ctx nat n) env env',
  (forall i, Typed Γ (env i) (lift_closed Unary.Domain)) ->
  (forall i, Typed Γ (env' i) (lift_closed Unary.Domain)) ->
  (forall i, inhabited Γ (Unary.E (env i) (env' i))) ->
  inhabited Γ (formula A env) -> inhabited Γ (formula A env').
Proof.
  induction A; intros m Γ env env' Henv Henv' HE Hp; cbn [formula] in Hp |- *.
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
  - apply (equality_transport Γ
      (app (app (lift_closed Unary.addition) (term env t)) (term env t0))
      (app (app (lift_closed Unary.addition) (term env' t)) (term env' t0))
      (term env t1) (term env' t1)).
    + apply binary_operation_typed; [apply Unary.addition_typed | |]; apply term_typed; exact Henv.
    + apply binary_operation_typed; [apply Unary.addition_typed | |]; apply term_typed; exact Henv'.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply binary_congruence.
      * exact (lift_closed_typed Γ _ _ Unary.addition_typed).
      * apply term_typed. exact Henv.
      * apply term_typed. exact Henv'.
      * apply term_typed. exact Henv.
      * apply term_typed. exact Henv'.
      * apply term_congruence; assumption.
      * apply term_congruence; assumption.
    + apply term_congruence; assumption.
    + exact Hp.
  - apply (equality_transport Γ
      (app (app (lift_closed Unary.multiplication) (term env t)) (term env t0))
      (app (app (lift_closed Unary.multiplication) (term env' t)) (term env' t0))
      (term env t1) (term env' t1)).
    + apply binary_operation_typed; [apply Unary.multiplication_typed | |]; apply term_typed; exact Henv.
    + apply binary_operation_typed; [apply Unary.multiplication_typed | |]; apply term_typed; exact Henv'.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply binary_congruence.
      * exact (lift_closed_typed Γ _ _ Unary.multiplication_typed).
      * apply term_typed. exact Henv.
      * apply term_typed. exact Henv'.
      * apply term_typed. exact Henv.
      * apply term_typed. exact Henv'.
      * apply term_congruence; assumption.
      * apply term_congruence; assumption.
    + apply term_congruence; assumption.
    + exact Hp.
  - exact Hp.
  - apply arrow_intro.
    + exists (formula_rank A1). apply formula_typed. exact Henv'.
    + rewrite formula_shift.
      apply (IHA2 _ _ (fun i => shift (env i)) (fun i => shift (env' i))).
      * apply environment_shift. exact Henv.
      * apply environment_shift. exact Henv'.
      * apply related_shift. exact HE.
      * pose proof (inhabited_shift _ _ (formula A1 env') Hp) as Himp.
        rewrite shift_arrow, !formula_shift in Himp.
        eapply arrow_elim; [exact Himp |].
        apply (IHA1 _ _ (fun i => shift (env' i)) (fun i => shift (env i))).
        -- apply environment_shift. exact Henv'.
        -- apply environment_shift. exact Henv.
        -- apply related_shift. intro i. apply symmetry; [apply Henv |apply Henv' |apply HE].
        -- rewrite <- formula_shift. apply newest.
  - change (inhabited Γ (formula (Relational.all A) env)) in Hp.
    change (inhabited Γ (formula (Relational.all A) env')).
    apply universal_introduction.
    apply (IHA _ _ (fun i => shift (transpose env i)) (fun i => shift (transpose env' i))).
    + apply environment_shift, environment_transpose. exact Henv.
    + apply environment_shift, environment_transpose. exact Henv'.
    + intro i. dependent elimination i.
      * apply equality_reflexivity_in_context.
        pose proof (weakening RankSorts _ _ (Unary.admitted V0)
          (tV (Γ & lift_closed Unary.Domain) fzero)) as Hv.
        change (Typed (Γ & lift_closed Unary.Domain & Unary.admitted V0)
          (shift V0) (shift (shift (lift_closed Unary.Domain)))) in Hv.
        rewrite <- !lift_closed_shift in Hv. exact Hv.
      * cbn [transpose fin_match].
        pose proof (inhabited_shift _ _ (Unary.admitted V0)
          (inhabited_shift Γ _ (lift_closed Unary.Domain) (HE f))) as Heq.
        rewrite !Unary.shift_E in Heq. exact Heq.
    + replace (formula A (fun i => shift (transpose env i))) with
        (formula A (fin_match (shift V0) (fun i => shift (shift (env i))))).
      * apply universal_instance.
        -- pose proof (weakening RankSorts _ _ (Unary.admitted V0)
             (tV (Γ & lift_closed Unary.Domain) fzero)) as Hv.
           change (Typed (Γ & lift_closed Unary.Domain & Unary.admitted V0)
             (shift V0) (shift (shift (lift_closed Unary.Domain)))) in Hv.
           rewrite <- !lift_closed_shift in Hv. exact Hv.
        -- exact (newest (Γ & lift_closed Unary.Domain) (Unary.admitted V0)).
        -- rewrite <- !formula_shift. apply inhabited_shift, inhabited_shift. exact Hp.
      * apply formula_ext. intro i. dependent elimination i; reflexivity.
Qed.
Theorem equality_replacement {k n} (Γ : Ctx nat n) env (A : Relational.formula (S k)) t u :
  (forall i, Typed Γ (env i) (lift_closed Unary.Domain)) ->
  inhabited Γ (formula (Relational.equal t u) env) ->
  inhabited Γ (formula (Relational.instantiate A t) env) ->
  inhabited Γ (formula (Relational.instantiate A u) env).
Proof.
  intros Henv Heq Ht. rewrite !instantiate_translation, !formula_instance in Ht |- *.
  apply (formula_transport A _ Γ (fin_match (term env t) env) (fin_match (term env u) env)).
  - apply instance_environment; [exact Henv |apply term_typed; exact Henv].
  - apply instance_environment; [exact Henv |apply term_typed; exact Henv].
  - intro i. dependent elimination i; [exact Heq |apply equality_reflexivity_in_context, Henv].
  - exact Ht.
Qed.
End RelationalEquality.
