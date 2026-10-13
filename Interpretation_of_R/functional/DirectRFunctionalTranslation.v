(** Structural laws for the original, annotation-preserving functional
    translation. Adapted from the independent relational translation proofs. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From Interpretation_of_R Require Import DirectRStructural.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFirstOrder
  DirectRFunctionalSyntax.
Module FunctionalTranslation.
Import Codes Structural FirstOrder.
Lemma term_ext {k n} (env env' : Fin k -> Term nat n) t :
  (forall i, env i = env' i) -> translate_term env t = translate_term env' t.
Proof. intro H. induction t; cbn [translate_term]; congruence. Qed.
Lemma formula_ext {k n} A (env env' : Fin k -> Term nat n) :
  (forall i, env i = env' i) -> translate_formula A env = translate_formula A env'.
Proof.
  revert n env env'. induction A; intros m env env' H; cbn [translate_formula];
    try (rewrite !(term_ext env env' _ H); reflexivity).
  - reflexivity.
  - rewrite IHA1 with (env':=env'), IHA2 with (env':=env'); auto.
  - rewrite IHA1 with (env':=env'), IHA2 with (env':=env'); auto.
  - rewrite IHA1 with (env':=env'), IHA2 with (env':=env'); auto.
  - f_equal. f_equal. apply IHA. intro i. dependent elimination i;
      cbn [extend fin_match]; congruence.
  - f_equal. f_equal. f_equal. f_equal. apply IHA. intro i. dependent elimination i;
      cbn [extend fin_match]; congruence.
Qed.
Lemma term_rename {k m n} (f : Fin m -> Fin n) env (t : term k) :
  rename f (translate_term env t) = translate_term (fun i => rename f (env i)) t.
Proof.
  induction t; cbn [translate_term]; auto using rename_lift_closed;
    rewrite !rename_application, !rename_lift_closed; congruence.
Qed.
Lemma term_replace {k m n} (f : Fin m -> Term nat n) env (t : term k) :
  replace f (translate_term env t) = translate_term (fun i => replace f (env i)) t.
Proof.
  induction t; cbn [translate_term]; auto using replace_lift_closed;
    rewrite !replace_application, !replace_lift_closed; congruence.
Qed.
Lemma term_source_rename {k m n} (f : Fin k -> Fin m) (env : Fin m -> Term nat n) t :
  translate_term env (FunctionalSyntax.trename f t) = translate_term (fun i => env (f i)) t.
Proof. induction t; cbn; congruence. Qed.
Lemma term_source_subst {k m n} (f : Fin k -> term m) (env : Fin m -> Term nat n) t :
  translate_term env (FunctionalSyntax.tsubst f t) =
  translate_term (fun i => translate_term env (f i)) t.
Proof. induction t; cbn; congruence. Qed.
Lemma formula_replace {k m n} (f : Fin m -> Term nat n) A (env : Fin k -> Term nat m) :
  replace f (translate_formula A env) = translate_formula A (fun i => replace f (env i)).
Proof.
  revert m n f env. induction A; intros m' n' f env; cbn [translate_formula].
  all: try (unfold EqAt, LeAt; rewrite !replace_application, !replace_lift_closed,
    !term_replace; reflexivity).
  - apply replace_lift_closed.
  - rewrite replace_arrow, IHA1, IHA2. reflexivity.
  - unfold Conj, Neg. rewrite !replace_arrow, !replace_lift_closed, IHA1, IHA2. reflexivity.
  - cbn [FlatOr fold_right]. unfold Neg.
    rewrite !replace_arrow, !replace_lift_closed, IHA1, IHA2. reflexivity.
  - rewrite replace_product, replace_lift_closed, replace_arrow, IHA.
    unfold GoodAt. rewrite replace_application, replace_lift_closed.
    f_equal. f_equal. apply formula_ext. intro i. dependent elimination i.
    + reflexivity.
    + cbn [extend fin_match]. apply replace_shift.
  - unfold Neg. rewrite replace_arrow, replace_product, !replace_lift_closed,
      !replace_arrow, !replace_lift_closed, IHA.
    unfold GoodAt. rewrite replace_application, replace_lift_closed.
    f_equal. f_equal. f_equal. f_equal. apply formula_ext. intro i. dependent elimination i.
    + reflexivity.
    + cbn [extend fin_match]. apply replace_shift.
Qed.
Lemma formula_rename {k m n} (f : Fin m -> Fin n) A (env : Fin k -> Term nat m) :
  rename f (translate_formula A env) = translate_formula A (fun i => rename f (env i)).
Proof.
  rewrite rename_as_replace, formula_replace. apply formula_ext. intro i.
  symmetry. apply rename_as_replace.
Qed.
Lemma formula_source_subst {k m n} A (f : Fin k -> term m) (env : Fin m -> Term nat n) :
  translate_formula (FunctionalSyntax.fsubst f A) env =
  translate_formula A (fun i => translate_term env (f i)).
Proof.
  revert m n f env. induction A; intros m' n' f env;
    cbn [FunctionalSyntax.fsubst translate_formula].
  all: try (rewrite !term_source_subst; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. f_equal. f_equal. apply formula_ext. intro i. dependent elimination i.
    + reflexivity.
    + cbn [FunctionalSyntax.lift_sub fin_match extend]. rewrite term_source_rename.
      symmetry. apply term_rename.
  - rewrite IHA. f_equal. f_equal. f_equal. f_equal.
    apply formula_ext. intro i. dependent elimination i.
    + reflexivity.
    + cbn [FunctionalSyntax.lift_sub fin_match extend]. rewrite term_source_rename.
      symmetry. apply term_rename.
Qed.
Lemma formula_source_rename {k m n} A (f : Fin k -> Fin m) (env : Fin m -> Term nat n) :
  translate_formula (FunctionalSyntax.frename f A) env = translate_formula A (fun i => env (f i)).
Proof.
  revert m n f env. induction A; intros m' n' f env;
    cbn [FunctionalSyntax.frename translate_formula].
  all: try (rewrite !term_source_rename; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. f_equal. f_equal. apply formula_ext. intro i.
    dependent elimination i; reflexivity.
  - rewrite IHA. f_equal. f_equal. f_equal. f_equal. apply formula_ext. intro i.
    dependent elimination i; reflexivity.
Qed.
Theorem instantiate_translation {k n} A t (env : Fin k -> Term nat n) :
  translate_formula (FunctionalSyntax.instantiate A t) env =
  subst (translate_formula A (extend env)) (translate_term env t).
Proof.
  unfold FunctionalSyntax.instantiate, subst. rewrite formula_source_subst, formula_replace.
  apply formula_ext. intro i. dependent elimination i;
    cbn [fin_match extend translate_term]; [reflexivity |].
  symmetry. apply replace_shift_substitution.
Qed.
End FunctionalTranslation.
