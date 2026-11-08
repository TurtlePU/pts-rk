(** Independent functional source language and classical deduction.
    Only finite indices are shared with PTS syntax; no target interpretation,
    typing, or inhabitation occurs in the source axioms or deduction rules. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
Import ListNotations.
Module FunctionalSource.

Inductive term (n : nat) : Type :=
| variable : Fin n -> term n
| zero : term n
| successor : term n -> term n
| addition : term n -> term n -> term n
| multiplication : term n -> term n -> term n.
Arguments variable {n} _.
Arguments zero {n}.
Arguments successor {n} _.
Arguments addition {n} _ _.
Arguments multiplication {n} _ _.

Fixpoint trename {m n} (f : Fin m -> Fin n) (t : term m) : term n :=
  match t with
  | variable i => variable (f i) | zero => zero
  | successor u => successor (trename f u)
  | addition u v => addition (trename f u) (trename f v)
  | multiplication u v => multiplication (trename f u) (trename f v)
  end.
Fixpoint tsubst {m n} (f : Fin m -> term n) (t : term m) : term n :=
  match t with
  | variable i => f i | zero => zero
  | successor u => successor (tsubst f u)
  | addition u v => addition (tsubst f u) (tsubst f v)
  | multiplication u v => multiplication (tsubst f u) (tsubst f v)
  end.
Definition lift_sub {m n} (f : Fin m -> term n) :=
  fin_match (variable fzero) (fun i => trename fsucc (f i)).

Inductive formula (n : nat) : Type :=
| equal : term n -> term n -> formula n
| less_equal : term n -> term n -> formula n
| falsity : formula n
| implies : formula n -> formula n -> formula n
| all : formula (S n) -> formula n.
Arguments equal {n} _ _.
Arguments less_equal {n} _ _.
Arguments falsity {n}.
Arguments implies {n} _ _.
Arguments all {n} _.
Fixpoint frename {m n} (f : Fin m -> Fin n) (A : formula m) : formula n :=
  match A with
  | equal t u => equal (trename f t) (trename f u)
  | less_equal t u => less_equal (trename f t) (trename f u)
  | falsity => falsity
  | implies B C => implies (frename f B) (frename f C)
  | all B => all (frename (weak f) B)
  end.
Fixpoint fsubst {m n} (f : Fin m -> term n) (A : formula m) : formula n :=
  match A with
  | equal t u => equal (tsubst f t) (tsubst f u)
  | less_equal t u => less_equal (tsubst f t) (tsubst f u)
  | falsity => falsity
  | implies B C => implies (fsubst f B) (fsubst f C)
  | all B => all (fsubst (lift_sub f) B)
  end.
Definition instantiate {n} (A : formula (S n)) (t : term n) :=
  fsubst (fin_match t variable) A.

(** The same complete classical basis as the relational development.
    These are source-level abbreviations, not target-typing definitions. *)
Definition neg {n} (A : formula n) := implies A falsity.
Definition conj {n} (A B : formula n) := neg (implies A (implies B falsity)).
Definition iff {n} (A B : formula n) := conj (implies A B) (implies B A).
Definition disj {n} (xs : list (formula n)) :=
  fold_right (fun A B => implies (neg A) B) falsity xs.
Definition some {n} (A : formula (S n)) := neg (all (neg A)).
Fixpoint numeral {n} k : term n :=
  match k with 0 => zero | S k => successor (numeral k) end.
Definition x0 {n} : term (S n) := variable fzero.
Definition x1 {n} : term (S (S n)) := variable (fsucc fzero).
Definition x2 {n} : term (S (S (S n))) := variable (fsucc (fsucc fzero)).
Fixpoint close_formula (n : nat) : formula n -> formula 0 :=
  match n with 0 => fun A => A | S k => fun A => close_formula k (all A) end.
Definition close {n} := close_formula n.
Definition lt {n} (x y : term n) := conj (less_equal x y) (neg (equal x y)).
Definition one {n} : term n := successor zero.

Definition add_commutative := close (n:=2)
  (equal (addition x1 x0) (addition x0 x1)).
Definition mul_commutative := close (n:=2)
  (equal (multiplication x1 x0) (multiplication x0 x1)).
Definition add_associative := close (n:=3)
  (equal (addition (addition x2 x1) x0) (addition x2 (addition x1 x0))).
Definition mul_associative := close (n:=3)
  (equal (multiplication (multiplication x2 x1) x0)
    (multiplication x2 (multiplication x1 x0))).
Definition add_zero := close (n:=1) (equal (addition x0 zero) x0).
Definition mul_zero := close (n:=1) (equal (multiplication x0 zero) zero).
Definition mul_one := close (n:=1) (equal (multiplication x0 one) x0).
Definition distributivity := close (n:=3)
  (equal (multiplication x2 (addition x1 x0))
    (addition (multiplication x2 x1) (multiplication x2 x0))).
Definition additive_cancellation := close (n:=3)
  (implies (equal (addition x2 x1) (addition x2 x0)) (equal x1 x0)).
Definition order_refl := close (n:=1) (less_equal x0 x0).
Definition order_trans := close (n:=3)
  (implies (less_equal x2 x1) (implies (less_equal x1 x0) (less_equal x2 x0))).
Definition order_antisym := close (n:=2)
  (implies (less_equal x1 x0) (implies (less_equal x0 x1) (equal x1 x0))).
Definition zero_least := close (n:=1) (less_equal zero x0).
Definition nontrivial : formula 0 := neg (equal zero one).
Definition add_monotone := close (n:=3)
  (implies (less_equal x2 x1) (less_equal (addition x2 x0) (addition x1 x0))).
Definition mul_monotone := close (n:=3)
  (implies (less_equal x2 x1)
    (less_equal (multiplication x2 x0) (multiplication x1 x0))).
Definition addition_strict_monotone := close (n:=3)
  (implies (lt x2 x1) (lt (addition x2 x0) (addition x1 x0))).
Definition multiplication_strict_monotone := close (n:=3)
  (implies (lt x2 x1) (implies (lt zero x0)
    (lt (multiplication x2 x0) (multiplication x1 x0)))).
Definition successor_add_one := close (n:=1)
  (equal (addition x0 one) (successor x0)).
Definition rig_laws : list (formula 0) :=
  [add_commutative; mul_commutative; add_associative; mul_associative;
   add_zero; mul_zero; mul_one; distributivity; additive_cancellation;
   order_refl; order_trans; order_antisym; zero_least; nontrivial;
   add_monotone; mul_monotone; addition_strict_monotone;
   multiplication_strict_monotone; successor_add_one].

(** Original functional R4 is the implication. The strict bounded-case
    schema below is additionally a biconditional, including cutoff zero. *)
Definition bounded n : formula 0 := all
  (implies (less_equal x0 (numeral n))
    (disj (map (fun i => equal x0 (numeral i)) (seq 0 (S n))))).
Definition comparison n : formula 0 := all
  (disj [less_equal x0 (numeral n); less_equal (numeral n) x0]).
Definition strict_bounded n : formula 0 := all
  (iff (lt x0 (numeral n))
    (disj (map (fun i => equal x0 (numeral i)) (seq 0 n)))).
Inductive r_axiom : formula 0 -> Prop :=
| ax_add m n : r_axiom (equal (addition (numeral m) (numeral n)) (numeral (m+n)))
| ax_mul m n : r_axiom (equal (multiplication (numeral m) (numeral n)) (numeral (m*n)))
| ax_neq m n : m <> n -> r_axiom (neg (equal (numeral m) (numeral n)))
| ax_bound n : r_axiom (bounded n)
| ax_compare n : r_axiom (comparison n).
Inductive axiom : formula 0 -> Prop :=
| arithmetic_R A : r_axiom A -> axiom A
| ordered_rig A : In A rig_laws -> axiom A
| finite_strict_cut n : axiom (strict_bounded n).

Definition closed_instance {n} (A : formula 0) : formula n :=
  frename (fun i : Fin 0 => match i with end) A.
Inductive derives : forall n, list (formula n) -> formula n -> Prop :=
| hypothesis n Γ A : In A Γ -> derives n Γ A
| theory n Γ A : axiom A -> derives n Γ (closed_instance A)
| implication_intro n Γ A B : derives n (A::Γ) B -> derives n Γ (implies A B)
| implication_elim n Γ A B : derives n Γ (implies A B) -> derives n Γ A -> derives n Γ B
| universal_intro n Γ A : derives (S n) (map (frename fsucc) Γ) A -> derives n Γ (all A)
| universal_elim n Γ A t : derives n Γ (all A) -> derives n Γ (instantiate A t)
| classical n Γ A : derives n Γ (neg (neg A)) -> derives n Γ A
| equality_refl n Γ t : derives n Γ (equal t t)
| equality_replace n Γ (A : formula (S n)) t u :
    derives n Γ (equal t u) -> derives n Γ (instantiate A t) -> derives n Γ (instantiate A u).
Arguments derives {n} Γ A.

Lemma trename_ext {m n} (f g : Fin m -> Fin n) t :
  (forall i, f i = g i) -> trename f t = trename g t.
Proof. intro H. induction t; cbn; congruence. Qed.
Lemma tsubst_ext {m n} (f g : Fin m -> term n) t :
  (forall i, f i = g i) -> tsubst f t = tsubst g t.
Proof. intro H. induction t; cbn; congruence. Qed.
Lemma fsubst_ext {m n} (f g : Fin m -> term n) A :
  (forall i, f i = g i) -> fsubst f A = fsubst g A.
Proof.
  revert n f g. induction A; intros n' f g H; cbn; f_equal; auto using tsubst_ext.
  apply IHA. intro i. dependent elimination i; cbn [lift_sub fin_match];
    [reflexivity |rewrite H; reflexivity].
Qed.
Lemma weakening {n} Γ (A : formula n) : derives Γ A -> forall Δ,
  (forall B, In B Γ -> In B Δ) -> derives Δ A.
Proof.
  intro H. induction H; intros Δ Hin.
  - apply hypothesis, Hin. assumption.
  - apply theory. assumption.
  - apply implication_intro, IHderives. intros C [<-|HC]; [left; reflexivity |right; auto].
  - eapply implication_elim; [apply IHderives1 |apply IHderives2]; exact Hin.
  - apply universal_intro, IHderives. intros C HC.
    apply in_map_iff in HC. destruct HC as [D [<- HD]]. apply in_map. auto.
  - eapply universal_elim, IHderives. exact Hin.
  - apply classical, IHderives. exact Hin.
  - apply equality_refl.
  - eapply equality_replace; [apply IHderives1 |apply IHderives2]; exact Hin.
Qed.
Lemma source_ex_falso {n} Γ (A : formula n) : derives Γ falsity -> derives Γ A.
Proof.
  intro H. apply classical, implication_intro.
  eapply weakening; [exact H |]. intros B HB. right. exact HB.
Qed.
End FunctionalSource.
