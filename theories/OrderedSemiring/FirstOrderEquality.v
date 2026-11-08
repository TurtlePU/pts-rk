(** Equality replacement for the new G15/diagonal-E/difference-O model.
    Arithmetic congruence uses the two actual Church operations and
    certified admitted environments, never arbitrary-function congruence. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import AbstractRewriting DefEq Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural
  DirectRLogic DirectRFiniteUp DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRRelationalSyntax.
From OrderedSemiring Require Import RigCodes ObservationEquality ArithmeticCongruence
  SemiringLaws OrderLaws ModelInterface FirstOrderTranslation.
Import ListNotations.
Module FirstOrderEquality.
Import CommonCodes Core Structural NegativeLogic FirstOrderTranslation.

Module Codes.
Import ObservationEquality ArithmeticCongruence.
Definition g15 x := NApp (RigCodes.nGood 15) x.
Definition lower7 x g := napps (NClosed (RigCodes.lowering 15 7)) [x;g].
Definition fields := [(100,nD);(101,nD);(102,nD);(103,nD);
  (110,g15 (NVar 100));(111,g15 (NVar 101));(112,g15 (NVar 102));(113,g15 (NVar 103));
  (114,nEq (NVar 100) (NVar 101));(115,nEq (NVar 102) (NVar 103))].
Definition source op x y := napps (NClosed op) [x;y].
Definition source_congruence_type op := close
  (npis fields (nEq (source op (NVar 100) (NVar 102))
    (source op (NVar 101) (NVar 103)))) eq_refl.
Definition addition_congruence := close (nlams fields
  (trans (add (NVar 102) (NVar 100)) (add (NVar 103) (NVar 100)) (add (NVar 103) (NVar 101))
    (add_first (NVar 102) (NVar 103) (NVar 100) (NVar 115))
    (add_second (NVar 103) (NVar 100) (NVar 101) (lower7 (NVar 103) (NVar 113)) (NVar 114)))) eq_refl.
Definition multiplication_congruence := close (nlams fields
  (trans (mul (NVar 102) (NVar 100)) (mul (NVar 103) (NVar 100)) (mul (NVar 103) (NVar 101))
    (mul_first (NVar 102) (NVar 103) (NVar 100) (lower7 (NVar 100) (NVar 110)) (NVar 115))
    (mul_second (NVar 103) (NVar 100) (NVar 101)
      (lower7 (NVar 103) (NVar 113)) (lower7 (NVar 101) (NVar 111)) (NVar 114)))) eq_refl.
Lemma addition_congruence_typed : Typed ε addition_congruence (source_congruence_type Model.addition).
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_congruence_typed : Typed ε multiplication_congruence (source_congruence_type Model.multiplication).
Proof. RkCheck.certify_with 4096. Qed.
End Codes.

Lemma symmetry {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d e) -> inhabited Γ (Model.E e d).
Proof.
  intros Hd He [p Hp]. pose proof (lift_closed_typed Γ _ _ ObservationEquality.symmetry_typed) as H.
  change (Typed Γ (lift_closed ObservationEquality.symmetry)
    (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
      (Arrow (Model.E (shift V0) V0) (Model.E V0 (shift V0)))))) in H.
  Model.feed H Hd. Model.feed H He. Model.feed_arrow H Hp. eexists. exact H.
Qed.
Lemma transitivity {n} (Γ : Ctx nat n) d e f :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  Typed Γ f (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d e) -> inhabited Γ (Model.E e f) -> inhabited Γ (Model.E d f).
Proof.
  intros Hd He Hf [p Hp] [q Hq].
  pose proof (lift_closed_typed Γ _ _ ObservationEquality.transitivity_typed) as H.
  change (Typed Γ (lift_closed ObservationEquality.transitivity)
    (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
      (Arrow (Model.E (shift (shift V0)) (shift V0))
        (Arrow (Model.E (shift V0) V0) (Model.E (shift (shift V0)) V0))))))) in H.
  Model.feed H Hd. Model.feed H He. Model.feed H Hf.
  Model.feed_arrow H Hp. Model.feed_arrow H Hq. eexists. exact H.
Qed.
Lemma successor_congruence {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d e) ->
  inhabited Γ (Model.E (app (lift_closed Model.successor) d) (app (lift_closed Model.successor) e)).
Proof.
  intros Hd He [p Hp]. pose proof (lift_closed_typed Γ _ _ ObservationEquality.successor_congruence_typed) as H.
  change (Typed Γ (lift_closed ObservationEquality.successor_congruence)
    (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
      (Arrow (Model.E (shift V0) V0)
        (Model.E (app (lift_closed Model.successor) (shift V0)) (app (lift_closed Model.successor) V0)))))) in H.
  Model.feed H Hd. Model.feed H He. Model.feed_arrow H Hp. eexists. exact H.
Qed.
Lemma term_congruence {k} (t : Relational.term k) : forall n (Γ : Ctx nat n) env env',
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  (forall i, Typed Γ (env' i) (lift_closed Model.Domain)) ->
  (forall i, inhabited Γ (Model.E (env i) (env' i))) ->
  inhabited Γ (Model.E (term env t) (term env' t)).
Proof.
  induction t; intros m Γ env env' Henv Henv' HE; cbn [term].
  - apply HE.
  - apply equality_reflexivity_in_context. exact (lift_closed_typed Γ _ _ Model.zero_typed).
  - apply successor_congruence.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply IHt; assumption.
Qed.
Lemma equality_transport {n} (Γ : Ctx nat n) d d' e e' :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ d' (lift_closed Model.Domain) ->
  Typed Γ e (lift_closed Model.Domain) -> Typed Γ e' (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d d') -> inhabited Γ (Model.E e e') ->
  inhabited Γ (Model.E d e) -> inhabited Γ (Model.E d' e').
Proof.
  intros Hd Hd' He He' Hdd Hee Hde.
  eapply transitivity; [exact Hd' |exact He |exact He' | |exact Hee].
  eapply transitivity; [exact Hd' |exact Hd |exact He | |exact Hde].
  apply symmetry; assumption.
Qed.
Lemma order_transport {n} (Γ : Ctx nat n) d d' e e' :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ d' (lift_closed Model.Domain) ->
  Typed Γ e (lift_closed Model.Domain) -> Typed Γ e' (lift_closed Model.Domain) ->
  inhabited Γ (Model.E d d') -> inhabited Γ (Model.E e e') ->
  inhabited Γ (Model.O d e) -> inhabited Γ (Model.O d' e').
Proof.
  intros Hd Hd' He He' [p Hp] [q Hq] [r Hr].
  pose proof (lift_closed_typed Γ _ _ OrderLaws.order_congruence_typed) as H.
  change (Typed Γ (lift_closed OrderLaws.order_congruence)
    (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
      (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
        (Arrow (Model.E (shift (shift (shift V0))) (shift (shift V0)))
          (Arrow (Model.E (shift V0) V0)
            (Arrow (Model.O (shift (shift (shift V0))) (shift V0))
              (Model.O (shift (shift V0)) V0))))))))) in H.
  Model.feed H Hd. Model.feed H Hd'. Model.feed H He. Model.feed H He'.
  Model.feed_arrow H Hp. Model.feed_arrow H Hq. Model.feed_arrow H Hr. eexists. exact H.
Qed.

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
Proof.
  intros Hw Hd Hd' He He' [gd Hgd] [gd' Hgd'] [ge Hge] [ge' Hge'] [p Hp] [q Hq].
  pose proof (lift_closed_typed Γ _ _ Hw) as H.
  destruct b; cbn [source_operator] in Hw, H |- *.
  all: lazymatch goal with
  | |- inhabited _ (Model.E (app (app (lift_closed ?op) _) _) _) =>
  change (Typed Γ (lift_closed witness)
    (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
      (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
        (Arrow (Model.admitted (shift (shift (shift V0))))
          (Arrow (Model.admitted (shift (shift V0)))
            (Arrow (Model.admitted (shift V0)) (Arrow (Model.admitted V0)
              (Arrow (Model.E (shift (shift (shift V0))) (shift (shift V0)))
                (Arrow (Model.E (shift V0) V0)
                  (Model.E
                    (app (app (lift_closed op) (shift (shift (shift V0)))) (shift V0))
                    (app (app (lift_closed op) (shift (shift V0))) V0))))))))))))) in H
  end.
  all: Model.feed H Hd; Model.feed H Hd'; Model.feed H He; Model.feed H He';
    Model.feed_arrow H Hgd; Model.feed_arrow H Hgd'; Model.feed_arrow H Hge; Model.feed_arrow H Hge';
    Model.feed_arrow H Hp; Model.feed_arrow H Hq; eexists; exact H.
Qed.
Lemma shift_E {n} (d e : Term nat n) : shift (Model.E d e) = Model.E (shift d) (shift e).
Proof.
  unfold Model.E. change
    (app (app (shift (lift_closed ObservationEquality.Equality)) (shift d)) (shift e) =
     app (app (lift_closed ObservationEquality.Equality) (shift d)) (shift e)).
  rewrite <- lift_closed_shift. reflexivity.
Qed.
Lemma related_shift {k n} (Γ : Ctx nat n) (env env' : Fin k -> Term nat n) B :
  (forall i, inhabited Γ (Model.E (env i) (env' i))) ->
  forall i, inhabited (Γ & B) (Model.E (shift (env i)) (shift (env' i))).
Proof. intros H i. rewrite <- shift_E. apply inhabited_shift. apply H. Qed.

Theorem formula_transport {k} (A : Relational.formula k) : forall n (Γ : Ctx nat n) env env',
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
  - apply (equality_transport Γ
      (app (app (lift_closed Model.addition) (term env t)) (term env t0))
      (app (app (lift_closed Model.addition) (term env' t)) (term env' t0))
      (term env t1) (term env' t1)).
    + apply binary_operation_typed; [apply Model.addition_typed | |]; apply term_typed; exact Henv.
    + apply binary_operation_typed; [apply Model.addition_typed | |]; apply term_typed; exact Henv'.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply (source_binary_congruence Γ true Codes.addition_congruence).
      * apply Codes.addition_congruence_typed.
      * apply term_typed. exact Henv.
      * apply term_typed. exact Henv'.
      * apply term_typed. exact Henv.
      * apply term_typed. exact Henv'.
      * apply term_admitted; assumption.
      * apply term_admitted; assumption.
      * apply term_admitted; assumption.
      * apply term_admitted; assumption.
      * apply term_congruence; assumption.
      * apply term_congruence; assumption.
    + apply term_congruence; assumption.
    + exact Hp.
  - apply (equality_transport Γ
      (app (app (lift_closed Model.multiplication) (term env t)) (term env t0))
      (app (app (lift_closed Model.multiplication) (term env' t)) (term env' t0))
      (term env t1) (term env' t1)).
    + apply binary_operation_typed; [apply Model.multiplication_typed | |]; apply term_typed; exact Henv.
    + apply binary_operation_typed; [apply Model.multiplication_typed | |]; apply term_typed; exact Henv'.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv'.
    + apply (source_binary_congruence Γ false Codes.multiplication_congruence).
      * apply Codes.multiplication_congruence_typed.
      * apply term_typed. exact Henv.
      * apply term_typed. exact Henv'.
      * apply term_typed. exact Henv.
      * apply term_typed. exact Henv'.
      * apply term_admitted; assumption.
      * apply term_admitted; assumption.
      * apply term_admitted; assumption.
      * apply term_admitted; assumption.
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
  - change (inhabited Γ (formula (Relational.all A) env)) in Hp.
    change (inhabited Γ (formula (Relational.all A) env')).
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

Theorem equality_replacement {k n} (Γ : Ctx nat n) env (A : Relational.formula (S k)) t u :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  (forall i, inhabited Γ (Model.admitted (env i))) ->
  inhabited Γ (formula (Relational.equal t u) env) ->
  inhabited Γ (formula (Relational.instantiate A t) env) ->
  inhabited Γ (formula (Relational.instantiate A u) env).
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
Print Assumptions Codes.addition_congruence_typed.
Print Assumptions Codes.multiplication_congruence_typed.
Print Assumptions formula_transport.
Print Assumptions equality_replacement.
End FirstOrderEquality.
