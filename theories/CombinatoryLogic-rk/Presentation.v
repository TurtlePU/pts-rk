From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  Congruence AbstractRewriting.
Require Import PTSrk.Combinatory.Core.

(** A sound combinatory core, not a completeness theorem.  Subjects contain
    only universe atoms, four numerical combinator families and application.
    This is a MIXED presentation: types still use original annotated syntax,
    and conversion is original beta conversion of expansions.  In particular
    no binder-elimination or decision procedure is assumed by the typing
    relation below. *)
Module Presentation.

Inductive Expression : Type :=
| Universe : nat -> Expression
| Identity : nat -> Expression
| Constant : nat -> nat -> Expression
| Substitution : nat -> nat -> nat -> Expression
| Product : nat -> nat -> Expression
| Apply : Expression -> Expression -> Expression.

Fixpoint expand (p : Expression) : Term nat 0 :=
  match p with
  | Universe i => 𝓤 i
  | Identity a => Core.identity a
  | Constant a b => Core.constant_simple a b
  | Substitution a b c => Core.substitution a b c
  | Product a b => Core.product a b
  | Apply f x => app (expand f) (expand x)
  end.

(** This is an independent rule system: none of its constructors has the
    target original typing judgment as a premise.  Its conversion rule
    requires an independently derived combinatory type expression. *)
Inductive HasType : Expression -> Term nat 0 -> Prop :=
| type_universe i : HasType (Universe i) (𝓤 0)
| type_identity a : HasType (Identity a) (Core.identity_type a)
| type_constant a b :
    HasType (Constant a b) (Core.constant_simple_type a b)
| type_substitution a b c :
    HasType (Substitution a b c) (Core.substitution_type a b c)
| type_product a b : HasType (Product a b) (Core.product_type a b)
| type_apply f x A B :
    HasType f (Π A B) -> HasType x A ->
    HasType (Apply f x) (subst B (expand x))
| type_convert p q A r :
    HasType p A -> HasType q (𝓤 r) -> A =ᵝ expand q ->
    HasType p (expand q).

Theorem has_type_sound p A :
  HasType p A -> @typ nat RankSorts 0 ε (expand p) A.
Proof.
  intro H. induction H; cbn [expand].
  - apply typ_𝓤. reflexivity.
  - apply Core.identity_typed.
  - apply Core.constant_simple_typed.
  - apply Core.substitution_typed.
  - apply Core.product_typed.
  - eapply typ_app; eassumption.
  - eapply typ_conv; eassumption.
Qed.

Definition code_eq (p q : Expression) : Prop := expand p =ᵝ expand q.

Theorem code_eq_refl p : code_eq p p.
Proof. unfold code_eq. reflexivity. Qed.

Theorem code_eq_sym p q : code_eq p q -> code_eq q p.
Proof. unfold code_eq. intro H. symmetry. exact H. Qed.

Theorem code_eq_trans p q r : code_eq p q -> code_eq q r -> code_eq p r.
Proof. unfold code_eq. intros H H'. transitivity (expand q); assumption. Qed.

Theorem code_eq_apply f f' x x' :
  code_eq f f' -> code_eq x x' -> code_eq (Apply f x) (Apply f' x').
Proof.
  unfold code_eq. cbn [expand]. intros H H'.
  apply app_cong_par; auto; typeclasses eauto.
Qed.

(** Weak combinatory reduction contracts the saturated I, K and S spines.
    The type former P has a binder in its ORIGINAL reduct, so it has an
    expansion theorem below rather than an expression rewrite rule. *)
Inductive weak_step : Expression -> Expression -> Prop :=
| weak_identity a A x :
    weak_step (Apply (Apply (Identity a) A) x) x
| weak_constant a b A B x y :
    weak_step (Apply (Apply (Apply (Apply (Constant a b) A) B) x) y) x
| weak_substitution a b c A B C f g x :
    weak_step
      (Apply (Apply (Apply (Apply (Apply (Apply
        (Substitution a b c) A) B) C) f) g) x)
      (Apply (Apply f x) (Apply g x))
| weak_apply_left f f' x :
    weak_step f f' -> weak_step (Apply f x) (Apply f' x)
| weak_apply_right f x x' :
    weak_step x x' -> weak_step (Apply f x) (Apply f x').

Theorem weak_step_sound p q :
  weak_step p q -> expand p ↠ᵝ expand q.
Proof.
  intro H. induction H; cbn [expand].
  - apply Core.identity_beta.
  - apply Core.constant_simple_beta.
  - apply Core.substitution_beta.
  - apply app_cong_l. exact IHweak_step.
  - apply app_cong_r. exact IHweak_step.
Qed.

Definition weak_reduces : Expression -> Expression -> Prop := RTC weak_step.

Theorem weak_reduces_sound p q :
  weak_reduces p q -> expand p ↠ᵝ expand q.
Proof.
  intro H. induction H.
  - reflexivity.
  - transitivity (expand y); [apply weak_step_sound; exact H | exact IHRTC].
Qed.

Theorem weak_reduces_code_eq p q : weak_reduces p q -> code_eq p q.
Proof.
  intro H. unfold code_eq. apply def_equiv_prop.
  exists (expand q). split; [apply weak_reduces_sound; exact H | reflexivity].
Qed.

Theorem product_expansion a b A B :
  expand (Apply (Apply (Product a b) A) B) ↠ᵝ
    Π (expand A) (app (shift (expand B)) (var fzero)).
Proof. cbn [expand]. apply Core.product_beta. Qed.

Print Assumptions has_type_sound.
Print Assumptions code_eq_refl.
Print Assumptions code_eq_sym.
Print Assumptions code_eq_trans.
Print Assumptions code_eq_apply.
Print Assumptions weak_step_sound.
Print Assumptions weak_reduces_sound.
Print Assumptions weak_reduces_code_eq.
Print Assumptions product_expansion.

End Presentation.
