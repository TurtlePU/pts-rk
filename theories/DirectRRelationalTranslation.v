(** Structural guarded translation of the independent relational syntax. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRUnary DirectRUnaryAxioms DirectRRelationalSyntax.
Module RelationalTranslation.
Import Codes Core Structural NegativeLogic.
Fixpoint term {k n} (env : Fin k -> Term nat n) (t : Relational.term k) : Term nat n :=
  match t with
  | Relational.variable i => env i
  | Relational.zero => lift_closed Unary.zero
  | Relational.successor u => app (lift_closed Unary.successor) (term env u)
  end.
Fixpoint formula {k} (A : Relational.formula k) {n} (env : Fin k -> Term nat n) : Term nat n :=
  match A with
  | Relational.equal t u => Unary.E (term env t) (term env u)
  | Relational.less_equal t u => Unary.O (term env t) (term env u)
  | Relational.add_graph t u v => Unary.E
      (app (app (lift_closed Unary.addition) (term env t)) (term env u)) (term env v)
  | Relational.mul_graph t u v => Unary.E
      (app (app (lift_closed Unary.multiplication) (term env t)) (term env u)) (term env v)
  | Relational.falsity => lift_closed Bottom
  | Relational.implies B C => Arrow (formula B env) (formula C env)
  | Relational.all B => Π (lift_closed Unary.Domain)
      (Arrow (Unary.admitted V0) (formula B (transpose env)))
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
Lemma term_rename {k m n} (f : Fin m -> Fin n) env (t : Relational.term k) :
  rename f (term env t) = term (fun i => rename f (env i)) t.
Proof.
  induction t; cbn [term]; auto using rename_lift_closed.
  rewrite rename_application, rename_lift_closed, IHt. reflexivity.
Qed.
Lemma term_replace {k m n} (f : Fin m -> Term nat n) env (t : Relational.term k) :
  replace f (term env t) = term (fun i => replace f (env i)) t.
Proof.
  induction t; cbn [term]; auto using replace_lift_closed.
  rewrite replace_application, replace_lift_closed, IHt. reflexivity.
Qed.
Lemma term_source_rename {k m n} (f : Fin k -> Fin m) (env : Fin m -> Term nat n) t :
  term env (Relational.trename f t) = term (fun i => env (f i)) t.
Proof. induction t; cbn; congruence. Qed.
Lemma term_source_subst {k m n} (f : Fin k -> Relational.term m) (env : Fin m -> Term nat n) t :
  term env (Relational.tsubst f t) = term (fun i => term env (f i)) t.
Proof. induction t; cbn; congruence. Qed.
Lemma formula_replace {k m n} (f : Fin m -> Term nat n) A (env : Fin k -> Term nat m) :
  replace f (formula A env) = formula A (fun i => replace f (env i)).
Proof.
  revert m n f env. induction A; intros m' n' f env; cbn [formula].
  all: try (unfold Unary.E, Unary.O; rewrite !replace_application, !replace_lift_closed,
    !term_replace; reflexivity).
  - apply replace_lift_closed.
  - rewrite replace_arrow, IHA1, IHA2. reflexivity.
  - rewrite replace_product, replace_lift_closed, replace_arrow, IHA.
    unfold Unary.admitted. rewrite replace_application, replace_lift_closed.
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
Lemma formula_source_subst {k m n} A (f : Fin k -> Relational.term m) (env : Fin m -> Term nat n) :
  formula (Relational.fsubst f A) env = formula A (fun i => term env (f i)).
Proof.
  revert m n f env. induction A; intros m' n' f env; cbn [Relational.fsubst formula].
  all: try (rewrite !term_source_subst; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. f_equal. f_equal. apply formula_ext. intro i. dependent elimination i.
    + reflexivity.
    + cbn [Relational.lift_sub fin_match transpose]. rewrite term_source_rename.
      symmetry. apply term_rename.
Qed.
Lemma formula_source_rename {k m n} A (f : Fin k -> Fin m) (env : Fin m -> Term nat n) :
  formula (Relational.frename f A) env = formula A (fun i => env (f i)).
Proof.
  revert m n f env. induction A; intros m' n' f env; cbn [Relational.frename formula].
  all: try (rewrite !term_source_rename; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. f_equal. f_equal. apply formula_ext. intro i.
    dependent elimination i; reflexivity.
Qed.
Theorem instantiate_translation {k n} A t (env : Fin k -> Term nat n) :
  formula (Relational.instantiate A t) env =
  subst (formula A (transpose env)) (term env t).
Proof.
  unfold Relational.instantiate, subst. rewrite formula_source_subst, formula_replace.
  apply formula_ext. intro i. dependent elimination i; cbn [fin_match transpose term]; [reflexivity |].
  symmetry. apply replace_shift_substitution.
Qed.
Lemma term_typed {k n} (Γ : Ctx nat n) env (t : Relational.term k) :
  (forall i, Typed Γ (env i) (lift_closed Unary.Domain)) -> Typed Γ (term env t) (lift_closed Unary.Domain).
Proof.
  intro Henv. induction t; cbn [term]; auto.
  - apply lift_closed_typed, Unary.zero_typed.
  - eapply arrow_application; [apply Unary.successor_in_context |exact IHt].
Qed.
Lemma term_admitted {k n} (Γ : Ctx nat n) env (t : Relational.term k) :
  (forall i, Typed Γ (env i) (lift_closed Unary.Domain)) ->
  (forall i, inhabited Γ (Unary.admitted (env i))) -> inhabited Γ (Unary.admitted (term env t)).
Proof.
  intros Henv Hgood. induction t; cbn [term]; auto.
  - exists (lift_closed Unary.good_zero).
    exact (lift_closed_typed Γ _ _ Unary.good_zero_typed).
  - destruct IHt as [g Hg].
    pose proof (lift_closed_typed Γ _ _ Unary.good_successor_typed) as H.
    change (Typed Γ (lift_closed Unary.good_successor)
      (Π (lift_closed Unary.Domain) (Arrow (Unary.admitted V0)
        (Unary.admitted (app (lift_closed Unary.successor) V0))))) in H.
    pose proof (term_typed Γ env t Henv) as Ht.
    Unary.feed H Ht. Unary.feed_arrow H Hg. eexists. exact H.
Qed.
Fixpoint formula_rank {k} (A : Relational.formula k) : nat :=
  match A with
  | Relational.equal _ _ | Relational.add_graph _ _ _ | Relational.mul_graph _ _ _ => 5
  | Relational.less_equal _ _ => 6
  | Relational.falsity => 1
  | Relational.implies B C => Nat.max (S (formula_rank B)) (formula_rank C)
  | Relational.all B => Nat.max 13 (formula_rank B)
  end.
Lemma binary_operation_typed {n} (Γ : Ctx nat n) op d e :
  Typed ε op (Arrow Unary.Domain (Arrow Unary.Domain Unary.Domain)) ->
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ (app (app (lift_closed op) d) e) (lift_closed Unary.Domain).
Proof.
  intros Hop Hd He. pose proof (lift_closed_typed Γ _ _ Hop) as H.
  change (Typed Γ (lift_closed op)
    (Arrow (lift_closed Unary.Domain) (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain)))) in H.
  eapply arrow_application; [eapply arrow_application; [exact H |exact Hd] |exact He].
Qed.
Theorem formula_typed {k} (A : Relational.formula k) : forall n (Γ : Ctx nat n) env,
  (forall i, Typed Γ (env i) (lift_closed Unary.Domain)) ->
  Typed Γ (formula A env) (𝓤 (formula_rank A)).
Proof.
  induction A; intros m Γ env Henv; cbn [formula formula_rank].
  - apply Unary.equality_in_context; apply term_typed; exact Henv.
  - apply Unary.order_in_context; apply term_typed; exact Henv.
  - apply Unary.equality_in_context.
    + apply binary_operation_typed; [apply Unary.addition_typed | |]; apply term_typed; exact Henv.
    + apply term_typed; exact Henv.
  - apply Unary.equality_in_context.
    + apply binary_operation_typed; [apply Unary.multiplication_typed | |]; apply term_typed; exact Henv.
    + apply term_typed; exact Henv.
  - apply bottom_in_context.
  - apply arrow_formation; [apply IHA1 |apply IHA2]; exact Henv.
  - replace (Nat.max 13 (formula_rank A)) with (Nat.max 4 (Nat.max 13 (formula_rank A))) by lia.
    apply (tPi (lift_closed_typed Γ _ _ Unary.domain_formation)).
    apply (arrow_formation _ _ _ 12 (formula_rank A)).
    + apply UnaryAxioms.admitted_formation_in_context.
      pose proof (tV (Γ & lift_closed Unary.Domain) fzero) as H.
      change (Typed (Γ & lift_closed Unary.Domain) V0 (shift (lift_closed Unary.Domain))) in H.
      rewrite <- lift_closed_shift in H. exact H.
    + apply IHA. intro i. dependent elimination i.
      * exact (tV (Γ & lift_closed Unary.Domain) fzero).
      * cbn [transpose fin_match]. rewrite lift_closed_shift. apply weakening. apply Henv.
Qed.
Lemma numeral_translation {k n} (env : Fin k -> Term nat n) v :
  term env (Relational.numeral v) = lift_closed (Unary.numeral v).
Proof. induction v; cbn [Relational.numeral Unary.numeral term]; [reflexivity |rewrite IHv; reflexivity]. Qed.
Definition empty_env : Fin 0 -> Term nat 0 := fun i => match i with end.
Definition sentence (A : Relational.formula 0) : closed_term := formula A empty_env.
Fixpoint value (t : Relational.term 0) : nat :=
  match t with Relational.variable i => match i with end | Relational.zero => 0
  | Relational.successor u => S (value u) end.
Theorem closed_term_translation t : term empty_env t = Unary.numeral (value t).
Proof.
  induction t; cbn [term value Unary.numeral].
  - exact (match f with end).
  - apply lift_closed_zero.
  - rewrite IHt, lift_closed_zero. reflexivity.
Qed.
Theorem implication_elimination {k n} (Γ : Ctx nat n) env (A B : Relational.formula k) :
  inhabited Γ (formula (Relational.implies A B) env) ->
  inhabited Γ (formula A env) -> inhabited Γ (formula B env).
Proof. apply arrow_elim. Qed.
Theorem universal_elimination {k n} (Γ : Ctx nat n) env A (t : Relational.term k) :
  (forall i, Typed Γ (env i) (lift_closed Unary.Domain)) ->
  (forall i, inhabited Γ (Unary.admitted (env i))) ->
  inhabited Γ (formula (Relational.all A) env) ->
  inhabited Γ (formula (Relational.instantiate A t) env).
Proof.
  intros Henv Hg [p Hp]. pose proof (term_typed Γ env t Henv) as Ht.
  pose proof (tApp Hp Ht) as H.
  change (Typed Γ (app p (term env t))
    (subst (Arrow (Unary.admitted V0) (formula A (transpose env))) (term env t))) in H.
  rewrite subst_arrow in H.
  change (Typed Γ (app p (term env t))
    (Arrow (Unary.admitted (term env t)) (subst (formula A (transpose env)) (term env t)))) in H.
  rewrite <- instantiate_translation in H.
  eapply arrow_elim; [exists (app p (term env t)); exact H |].
  apply term_admitted; assumption.
Qed.
End RelationalTranslation.
