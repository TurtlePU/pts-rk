(** Direct interpretation of arbitrary functional arithmetic terms in the
    existing G15 / diagonal-E7 / difference-O15 native PTS model. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural DirectRLogic DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryAxioms
  DirectRUnaryBounded.
From OrderedSemiring Require Import RigCodes DomainClosure ModelInterface.
From OrderedSemiringFunctional Require Import Source.
Import ListNotations.
Module FunctionalTranslation.
Import CommonCodes Core Structural NegativeLogic.
Fixpoint term {k n} (env : Fin k -> Term nat n) (t : FunctionalSource.term k) : Term nat n :=
  match t with
  | FunctionalSource.variable i => env i
  | FunctionalSource.zero => lift_closed Model.zero
  | FunctionalSource.successor u => app (lift_closed Model.successor) (term env u)
  | FunctionalSource.addition u v => app (app (lift_closed Model.addition) (term env u)) (term env v)
  | FunctionalSource.multiplication u v => app (app (lift_closed Model.multiplication) (term env u)) (term env v)
  end.
Fixpoint formula {k} (A : FunctionalSource.formula k) {n} (env : Fin k -> Term nat n) : Term nat n :=
  match A with
  | FunctionalSource.equal t u => Model.E (term env t) (term env u)
  | FunctionalSource.less_equal t u => Model.O (term env t) (term env u)
  | FunctionalSource.falsity => lift_closed Bottom
  | FunctionalSource.implies B C => Arrow (formula B env) (formula C env)
  | FunctionalSource.all B => Π (lift_closed Model.Domain)
      (Arrow (Model.admitted V0) (formula B (transpose env)))
  end.
Lemma term_ext {k n} (env env' : Fin k -> Term nat n) t :
  (forall i, env i = env' i) -> term env t = term env' t.
Proof. intro H. induction t; cbn [term]; congruence. Qed.
Lemma formula_ext {k n} A (env env' : Fin k -> Term nat n) :
  (forall i, env i = env' i) -> formula A env = formula A env'.
Proof.
  revert n env env'. induction A; intros m env env' H; cbn [formula];
    try (rewrite !(term_ext env env' _ H); reflexivity).
  - reflexivity.
  - rewrite IHA1 with (env':=env'), IHA2 with (env':=env'); auto.
  - f_equal. f_equal. apply IHA. intro i. dependent elimination i; cbn [transpose fin_match]; congruence.
Qed.
Lemma term_rename {k m n} (f : Fin m -> Fin n) env (t : FunctionalSource.term k) :
  rename f (term env t) = term (fun i => rename f (env i)) t.
Proof.
  induction t; cbn [term]; auto using rename_lift_closed.
  - rewrite rename_application, rename_lift_closed, IHt. reflexivity.
  - rewrite !rename_application, rename_lift_closed, IHt1, IHt2. reflexivity.
  - rewrite !rename_application, rename_lift_closed, IHt1, IHt2. reflexivity.
Qed.
Lemma term_replace {k m n} (f : Fin m -> Term nat n) env (t : FunctionalSource.term k) :
  replace f (term env t) = term (fun i => replace f (env i)) t.
Proof.
  induction t; cbn [term]; auto using replace_lift_closed.
  - rewrite replace_application, replace_lift_closed, IHt. reflexivity.
  - rewrite !replace_application, replace_lift_closed, IHt1, IHt2. reflexivity.
  - rewrite !replace_application, replace_lift_closed, IHt1, IHt2. reflexivity.
Qed.
Lemma term_source_rename {k m n} (f : Fin k -> Fin m) (env : Fin m -> Term nat n) t :
  term env (FunctionalSource.trename f t) = term (fun i => env (f i)) t.
Proof. induction t; cbn; congruence. Qed.
Lemma term_source_subst {k m n} (f : Fin k -> FunctionalSource.term m) (env : Fin m -> Term nat n) t :
  term env (FunctionalSource.tsubst f t) = term (fun i => term env (f i)) t.
Proof. induction t; cbn; congruence. Qed.
Lemma formula_replace {k m n} (f : Fin m -> Term nat n) A (env : Fin k -> Term nat m) :
  replace f (formula A env) = formula A (fun i => replace f (env i)).
Proof.
  revert m n f env. induction A; intros m' n' f env; cbn [formula].
  all: try (unfold Model.E, Model.O; rewrite !replace_application, !replace_lift_closed,
    !term_replace; reflexivity).
  - apply replace_lift_closed.
  - rewrite replace_arrow, IHA1, IHA2. reflexivity.
  - rewrite replace_product, replace_lift_closed, replace_arrow, IHA.
    unfold Model.admitted. rewrite replace_application, replace_lift_closed.
    f_equal. f_equal. apply formula_ext. intro i. dependent elimination i.
    + reflexivity.
    + cbn [transpose fin_match]. apply replace_shift.
Qed.
Lemma formula_rename {k m n} (f : Fin m -> Fin n) A (env : Fin k -> Term nat m) :
  rename f (formula A env) = formula A (fun i => rename f (env i)).
Proof.
  rewrite rename_as_replace, formula_replace. apply formula_ext. intro i.
  symmetry. apply rename_as_replace.
Qed.
Lemma formula_source_subst {k m n} A (f : Fin k -> FunctionalSource.term m) (env : Fin m -> Term nat n) :
  formula (FunctionalSource.fsubst f A) env = formula A (fun i => term env (f i)).
Proof.
  revert m n f env. induction A; intros m' n' f env; cbn [FunctionalSource.fsubst formula].
  all: try (rewrite !term_source_subst; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. f_equal. f_equal. apply formula_ext. intro i. dependent elimination i.
    + reflexivity.
    + cbn [FunctionalSource.lift_sub fin_match transpose]. rewrite term_source_rename.
      symmetry. apply term_rename.
Qed.
Lemma formula_source_rename {k m n} A (f : Fin k -> Fin m) (env : Fin m -> Term nat n) :
  formula (FunctionalSource.frename f A) env = formula A (fun i => env (f i)).
Proof.
  revert m n f env. induction A; intros m' n' f env; cbn [FunctionalSource.frename formula].
  all: try (rewrite !term_source_rename; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. f_equal. f_equal. apply formula_ext. intro i.
    dependent elimination i; reflexivity.
Qed.
Theorem instantiate_translation {k n} A t (env : Fin k -> Term nat n) :
  formula (FunctionalSource.instantiate A t) env =
  subst (formula A (transpose env)) (term env t).
Proof.
  unfold FunctionalSource.instantiate, subst. rewrite formula_source_subst, formula_replace.
  apply formula_ext. intro i. dependent elimination i; cbn [fin_match transpose term]; [reflexivity |].
  symmetry. apply replace_shift_substitution.
Qed.
Lemma binary_operation_typed {n} (Γ : Ctx nat n) op d e :
  Typed ε op (Arrow Model.Domain (Arrow Model.Domain Model.Domain)) ->
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  Typed Γ (app (app (lift_closed op) d) e) (lift_closed Model.Domain).
Proof.
  intros Hop Hd He. pose proof (lift_closed_typed Γ _ _ Hop) as H.
  change (Typed Γ (lift_closed op)
    (Arrow (lift_closed Model.Domain) (Arrow (lift_closed Model.Domain) (lift_closed Model.Domain)))) in H.
  eapply arrow_application; [eapply arrow_application; [exact H |exact Hd] |exact He].
Qed.
(** These source-oriented adapters retain the existing Good15 domain.
    Reversing the two native Church arguments is only beta conversion. *)
Definition good_fields := [(100,Unary.nDomain);(101,Unary.nDomain);
  (110,NApp (RigCodes.nGood 15) (NVar 100));
  (111,NApp (RigCodes.nGood 15) (NVar 101))].
Definition binary_good_type op : closed_term := close
  (npis good_fields (NApp (RigCodes.nGood 15)
    (napps (NClosed op) [NVar 100;NVar 101]))) eq_refl.
Definition addition_good : closed_term := close (nlams good_fields
  (napps (NClosed (DomainClosure.good_addition 15))
    [NVar 101;NVar 100;NVar 111;NVar 110])) eq_refl.
Definition multiplication_good : closed_term := close (nlams good_fields
  (napps (NClosed (DomainClosure.good_multiplication 15))
    [NVar 101;NVar 100;NVar 111;NVar 110])) eq_refl.
Lemma addition_good_typed :
  Typed ε addition_good (binary_good_type Model.addition).
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_good_typed :
  Typed ε multiplication_good (binary_good_type Model.multiplication).
Proof. RkCheck.certify_with 4096. Qed.
Definition source_operator (addition : bool) :=
  if addition then Model.addition else Model.multiplication.
Lemma binary_admitted {n} (Γ : Ctx nat n) b witness d e :
  Typed ε witness (binary_good_type (source_operator b)) ->
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  inhabited Γ (Model.admitted d) -> inhabited Γ (Model.admitted e) ->
  inhabited Γ (Model.admitted (app (app (lift_closed (source_operator b)) d) e)).
Proof.
  intros Hw Hd He [gd Hgd] [ge Hge].
  pose proof (lift_closed_typed Γ _ _ Hw) as H.
  destruct b; cbn [source_operator] in Hw, H |- *.
  all: lazymatch goal with
  | |- inhabited _ (Model.admitted (app (app (lift_closed ?op) _) _)) =>
  change (Typed Γ (lift_closed witness)
    (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
      (Arrow (Model.admitted (shift V0)) (Arrow (Model.admitted V0)
        (Model.admitted (app (app (lift_closed op) (shift V0)) V0))))))) in H
  end.
  all: Model.feed H Hd; Model.feed H He;
    Model.feed_arrow H Hgd; Model.feed_arrow H Hge; eexists; exact H.
Qed.
Lemma addition_admitted {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  inhabited Γ (Model.admitted d) -> inhabited Γ (Model.admitted e) ->
  inhabited Γ (Model.admitted (app (app (lift_closed Model.addition) d) e)).
Proof. apply (binary_admitted Γ true addition_good), addition_good_typed. Qed.
Lemma multiplication_admitted {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  inhabited Γ (Model.admitted d) -> inhabited Γ (Model.admitted e) ->
  inhabited Γ (Model.admitted (app (app (lift_closed Model.multiplication) d) e)).
Proof. apply (binary_admitted Γ false multiplication_good), multiplication_good_typed. Qed.

Lemma term_typed {k n} (Γ : Ctx nat n) env (t : FunctionalSource.term k) :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) -> Typed Γ (term env t) (lift_closed Model.Domain).
Proof.
  intro Henv. induction t; cbn [term]; auto.
  - apply lift_closed_typed, Model.zero_typed.
  - eapply arrow_application; [apply Model.successor_in_context |exact IHt].
  - apply binary_operation_typed; [apply Model.addition_typed |exact IHt1 |exact IHt2].
  - apply binary_operation_typed; [apply Model.multiplication_typed |exact IHt1 |exact IHt2].
Qed.
Lemma term_admitted {k n} (Γ : Ctx nat n) env (t : FunctionalSource.term k) :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  (forall i, inhabited Γ (Model.admitted (env i))) -> inhabited Γ (Model.admitted (term env t)).
Proof.
  intros Henv Hgood. induction t; cbn [term]; auto.
  - exists (lift_closed Model.good_zero).
    exact (lift_closed_typed Γ _ _ Model.good_zero_typed).
  - destruct IHt as [g Hg].
    pose proof (lift_closed_typed Γ _ _ Model.good_successor_typed) as H.
    change (Typed Γ (lift_closed Model.good_successor)
      (Π (lift_closed Model.Domain) (Arrow (Model.admitted V0)
        (Model.admitted (app (lift_closed Model.successor) V0))))) in H.
    pose proof (term_typed Γ env t Henv) as Ht.
    Model.feed H Ht. Model.feed_arrow H Hg. eexists. exact H.
  - apply addition_admitted; try assumption; apply term_typed; exact Henv.
  - apply multiplication_admitted; try assumption; apply term_typed; exact Henv.
Qed.
Fixpoint formula_rank {k} (A : FunctionalSource.formula k) : nat :=
  match A with
  | FunctionalSource.equal _ _ => 7
  | FunctionalSource.less_equal _ _ => 15
  | FunctionalSource.falsity => 1
  | FunctionalSource.implies B C => Nat.max (S (formula_rank B)) (formula_rank C)
  | FunctionalSource.all B => Nat.max 18 (formula_rank B)
  end.
Theorem formula_typed {k} (A : FunctionalSource.formula k) : forall n (Γ : Ctx nat n) env,
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  Typed Γ (formula A env) (𝓤 (formula_rank A)).
Proof.
  induction A; intros m Γ env Henv; cbn [formula formula_rank].
  - apply Model.equality_in_context; apply term_typed; exact Henv.
  - apply Model.order_in_context; apply term_typed; exact Henv.
  - apply bottom_in_context.
  - apply arrow_formation; [apply IHA1 |apply IHA2]; exact Henv.
  - replace (Nat.max 18 (formula_rank A)) with (Nat.max 4 (Nat.max 18 (formula_rank A))) by lia.
    apply (tPi (lift_closed_typed Γ _ _ Model.domain_formation)).
    apply (arrow_formation _ _ _ 17 (formula_rank A)).
    + apply Model.admitted_formation_in_context.
      pose proof (tV (Γ & lift_closed Model.Domain) fzero) as H.
      change (Typed (Γ & lift_closed Model.Domain) V0 (shift (lift_closed Model.Domain))) in H.
      rewrite <- lift_closed_shift in H. exact H.
    + apply IHA. intro i. dependent elimination i.
      * exact (tV (Γ & lift_closed Model.Domain) fzero).
      * cbn [transpose fin_match]. rewrite lift_closed_shift. apply weakening. apply Henv.
Qed.
Lemma numeral_translation {k n} (env : Fin k -> Term nat n) v :
  term env (FunctionalSource.numeral v) = lift_closed (Model.numeral v).
Proof. induction v; cbn [FunctionalSource.numeral Model.numeral term]; [reflexivity |rewrite IHv; reflexivity]. Qed.
Definition empty_env : Fin 0 -> Term nat 0 := fun i => match i with end.
Definition sentence (A : FunctionalSource.formula 0) : closed_term := formula A empty_env.
Fixpoint value (t : FunctionalSource.term 0) : nat :=
  match t with FunctionalSource.variable i => match i with end | FunctionalSource.zero => 0
  | FunctionalSource.successor u => S (value u)
  | FunctionalSource.addition u v => value u + value v
  | FunctionalSource.multiplication u v => value u * value v end.
Theorem implication_elimination {k n} (Γ : Ctx nat n) env (A B : FunctionalSource.formula k) :
  inhabited Γ (formula (FunctionalSource.implies A B) env) ->
  inhabited Γ (formula A env) -> inhabited Γ (formula B env).
Proof. apply arrow_elim. Qed.
Theorem implication_introduction {k n} (Γ : Ctx nat n) env (A B : FunctionalSource.formula k) :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  inhabited (Γ & formula A env) (formula B (fun i => shift (env i))) ->
  inhabited Γ (formula (FunctionalSource.implies A B) env).
Proof.
  intros Henv H. apply arrow_intro.
  - exists (formula_rank A). apply formula_typed. exact Henv.
  - unfold shift. rewrite formula_rename. exact H.
Qed.
Theorem universal_introduction {k n} (Γ : Ctx nat n) env (A : FunctionalSource.formula (S k)) :
  inhabited ((Γ & lift_closed Model.Domain) & Model.admitted V0)
    (formula A (fun i => shift (transpose env i))) ->
  inhabited Γ (formula (FunctionalSource.all A) env).
Proof.
  intro H. cbn [formula].
  assert (HB : inhabited (Γ & lift_closed Model.Domain)
    (Arrow (Model.admitted V0) (formula A (transpose env)))).
  { apply arrow_intro.
    - exists 17. apply Model.admitted_formation_in_context.
      exact (tV (Γ & lift_closed Model.Domain) fzero).
    - unfold shift. rewrite formula_rename. exact H. }
  destruct HB as [p Hp]. exists (lam (lift_closed Model.Domain) p).
  exact (tLam (lift_closed_typed Γ _ _ Model.domain_formation) Hp).
Qed.
Lemma environment_shift {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) B :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  forall i, Typed (Γ & B) (shift (env i)) (lift_closed Model.Domain).
Proof. intros H i. rewrite lift_closed_shift. apply weakening. apply H. Qed.
Lemma environment_transpose {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  forall i, Typed (Γ & lift_closed Model.Domain) (transpose env i) (lift_closed Model.Domain).
Proof.
  intros H i. dependent elimination i.
  - exact (tV (Γ & lift_closed Model.Domain) fzero).
  - cbn [transpose fin_match]. apply environment_shift. exact H.
Qed.
Lemma admitted_environment_shift {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) B :
  (forall i, inhabited Γ (Model.admitted (env i))) ->
  forall i, inhabited (Γ & B) (Model.admitted (shift (env i))).
Proof. intros H i. exact (inhabited_shift Γ (Model.admitted (env i)) B (H i)). Qed.
Lemma admitted_environment_transpose {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) :
  (forall i, inhabited Γ (Model.admitted (env i))) ->
  forall i, inhabited ((Γ & lift_closed Model.Domain) & Model.admitted V0)
    (Model.admitted (shift (transpose env i))).
Proof.
  intros H i. dependent elimination i.
  - exact (newest (Γ & lift_closed Model.Domain) (Model.admitted V0)).
  - cbn [transpose fin_match].
    exact (inhabited_shift _ _ (Model.admitted V0)
      (inhabited_shift Γ _ (lift_closed Model.Domain) (H f))).
Qed.
Theorem universal_elimination {k n} (Γ : Ctx nat n) env A (t : FunctionalSource.term k) :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  (forall i, inhabited Γ (Model.admitted (env i))) ->
  inhabited Γ (formula (FunctionalSource.all A) env) ->
  inhabited Γ (formula (FunctionalSource.instantiate A t) env).
Proof.
  intros Henv Hg [p Hp]. pose proof (term_typed Γ env t Henv) as Ht.
  pose proof (tApp Hp Ht) as H.
  change (Typed Γ (app p (term env t))
    (subst (Arrow (Model.admitted V0) (formula A (transpose env))) (term env t))) in H.
  rewrite subst_arrow in H.
  change (Typed Γ (app p (term env t))
    (Arrow (Model.admitted (term env t)) (subst (formula A (transpose env)) (term env t)))) in H.
  rewrite <- instantiate_translation in H.
  eapply arrow_elim; [exists (app p (term env t)); exact H |].
  apply term_admitted; assumption.
Qed.
Lemma formula_shift {k n} A (env : Fin k -> Term nat n) :
  shift (formula A env) = formula A (fun i => shift (env i)).
Proof. apply formula_rename. Qed.
Lemma formula_instance {k n} A (env : Fin k -> Term nat n) d :
  subst (formula A (transpose env)) d = formula A (fin_match d env).
Proof.
  unfold subst. rewrite formula_replace. apply formula_ext. intro i.
  dependent elimination i; cbn [transpose fin_match]; [reflexivity |].
  apply replace_shift_substitution.
Qed.
Lemma universal_instance {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) A d :
  Typed Γ d (lift_closed Model.Domain) -> inhabited Γ (Model.admitted d) ->
  inhabited Γ (formula (FunctionalSource.all A) env) ->
  inhabited Γ (formula A (fin_match d env)).
Proof.
  intros Hd Hg [p Hp]. pose proof (tApp Hp Hd) as H.
  change (Typed Γ (app p d)
    (subst (Arrow (Model.admitted V0) (formula A (transpose env))) d)) in H.
  rewrite subst_arrow in H.
  change (Typed Γ (app p d)
    (Arrow (Model.admitted d) (subst (formula A (transpose env)) d))) in H.
  rewrite formula_instance in H.
  eapply arrow_elim; [exists (app p d); exact H |exact Hg].
Qed.
Lemma instance_environment {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) d :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  Typed Γ d (lift_closed Model.Domain) ->
  forall i, Typed Γ (fin_match d env i) (lift_closed Model.Domain).
Proof. intros H Hd i. dependent elimination i; [exact Hd |apply H]. Qed.
Lemma universal_instance_arrow {k n} (Γ : Ctx nat n) (env : Fin k -> Term nat n) A d :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  Typed Γ d (lift_closed Model.Domain) -> inhabited Γ (Model.admitted d) ->
  inhabited Γ (Arrow (formula (FunctionalSource.all A) env) (formula A (fin_match d env))).
Proof.
  intros Henv Hd Hg. apply arrow_intro.
  - exists (formula_rank (FunctionalSource.all A)). apply formula_typed. exact Henv.
  - rewrite formula_shift.
    replace (formula A (fun i => shift (fin_match d env i))) with
      (formula A (fin_match (shift d) (fun i => shift (env i)))).
    + apply universal_instance.
      * rewrite lift_closed_shift. apply weakening. exact Hd.
      * exact (inhabited_shift _ _ _ Hg).
      * rewrite <- formula_shift. apply newest.
    + apply formula_ext. intro i. dependent elimination i; reflexivity.
Qed.
Lemma equality_stable_in_context {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Model.Domain) -> Typed Γ e (lift_closed Model.Domain) ->
  stable Γ (Model.E d e).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ Model.equality_stability_typed) as H.
  change (Typed Γ (lift_closed Model.equality_stability)
    (Π (lift_closed Model.Domain) (Π (lift_closed Model.Domain)
      (Arrow (Neg (Neg (Model.E (shift V0) V0))) (Model.E (shift V0) V0))))) in H.
  unfold Neg in H. Model.feed H Hd. Model.feed H He. eexists. exact H.
Qed.
Theorem formula_stable {k} (A : FunctionalSource.formula k) : forall n (Γ : Ctx nat n) env,
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) -> stable Γ (formula A env).
Proof.
  induction A; intros m Γ env Henv; cbn [formula].
  - apply equality_stable_in_context; apply term_typed; exact Henv.
  - apply Model.order_stable_in_context; apply term_typed; exact Henv.
  - apply bottom_stable.
  - apply arrow_stable.
    + exists (formula_rank A1). apply formula_typed. exact Henv.
    + exists (formula_rank A2). apply formula_typed. exact Henv.
    + apply IHA2. exact Henv.
  - change (stable Γ (formula (FunctionalSource.all A) env)).
    unfold stable. set (H := Neg (Neg (formula (FunctionalSource.all A) env))).
    apply arrow_intro.
    + unfold H. apply neg_formed, neg_formed.
      exists (formula_rank (FunctionalSource.all A)). apply formula_typed. exact Henv.
    + rewrite formula_shift. apply universal_introduction.
      set (env2 := fun i => shift (transpose (fun j => shift (env j)) i)).
      set (env3 := fun i => shift (shift (shift (env i)))).
      assert (HT2 : forall i, Typed ((Γ & H) & lift_closed Model.Domain & Model.admitted V0)
        (env2 i) (lift_closed Model.Domain)).
      { unfold env2. apply environment_shift, environment_transpose, environment_shift. exact Henv. }
      eapply arrow_elim; [exact (IHA _ _ env2 HT2) |].
      assert (HT3 : forall i, Typed ((Γ & H) & lift_closed Model.Domain & Model.admitted V0)
        (env3 i) (lift_closed Model.Domain)).
      { unfold env3. apply environment_shift, environment_shift, environment_shift. exact Henv. }
      assert (HE : formula A env2 = formula A (fin_match (shift V0) env3)).
      { apply formula_ext. intro i. dependent elimination i; reflexivity. }
      rewrite HE.
      assert (Hd : Typed ((Γ & H) & lift_closed Model.Domain & Model.admitted V0)
        (shift V0) (lift_closed Model.Domain)).
      { pose proof (weakening RankSorts _ _ (Model.admitted V0)
          (tV ((Γ & H) & lift_closed Model.Domain) fzero)) as Hv.
        change (Typed ((Γ & H) & lift_closed Model.Domain & Model.admitted V0)
          (shift V0) (shift (shift (lift_closed Model.Domain)))) in Hv.
        rewrite <- !lift_closed_shift in Hv. exact Hv. }
      eapply double_negation_map.
      * exists (formula_rank (FunctionalSource.all A)). apply formula_typed. exact HT3.
      * exists (formula_rank A). apply formula_typed, instance_environment; eassumption.
      * apply universal_instance_arrow; [exact HT3 |exact Hd |].
        exact (newest ((Γ & H) & lift_closed Model.Domain) (Model.admitted V0)).
      * pose proof (newest Γ H) as Hnn.
        unfold H in Hnn. normalize_shifts Hnn.
        weaken_copy Hnn (@lift_closed (S m) Model.Domain) Hnn2.
        weaken_copy Hnn2 (Model.admitted (@V0 (S m))) Hnn3.
        rewrite !formula_shift in Hnn3. exact Hnn3.
Qed.
Theorem classical_elimination {k n} (Γ : Ctx nat n) env (A : FunctionalSource.formula k) :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  inhabited Γ (formula (FunctionalSource.neg (FunctionalSource.neg A)) env) ->
  inhabited Γ (formula A env).
Proof. intros Henv H. eapply arrow_elim; [apply formula_stable; exact Henv |exact H]. Qed.
Lemma equality_reflexivity_in_context {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Model.Domain) -> inhabited Γ (Model.E d d).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ Model.equality_reflexivity_typed) as H.
  change (Typed Γ (lift_closed Model.equality_reflexivity)
    (Π (lift_closed Model.Domain) (Model.E V0 V0))) in H.
  Model.feed H Hd. eexists. exact H.
Qed.
Theorem equality_reflexivity {k n} (Γ : Ctx nat n) env (t : FunctionalSource.term k) :
  (forall i, Typed Γ (env i) (lift_closed Model.Domain)) ->
  inhabited Γ (formula (FunctionalSource.equal t t) env).
Proof. intro Henv. apply equality_reflexivity_in_context, term_typed. exact Henv. Qed.
Print Assumptions addition_good_typed.
Print Assumptions multiplication_good_typed.
Print Assumptions term_admitted.
Print Assumptions universal_elimination.
End FunctionalTranslation.
