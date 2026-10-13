(** Independent relational first-order syntax and classical natural deduction.
    Only finite indices are shared with the PTS syntax; no target typing or
    inhabitation occurs in the definition of source derivability. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
Import ListNotations.
Module Relational.
Inductive term (n : nat) : Type :=
| variable : Fin n -> term n
| zero : term n
| successor : term n -> term n.
Arguments variable {n} _.
Arguments zero {n}.
Arguments successor {n} _.
Fixpoint trename {m n} (f : Fin m -> Fin n) (t : term m) : term n :=
  match t with variable i => variable (f i) | zero => zero | successor u => successor (trename f u) end.
Fixpoint tsubst {m n} (f : Fin m -> term n) (t : term m) : term n :=
  match t with variable i => f i | zero => zero | successor u => successor (tsubst f u) end.
Definition lift_sub {m n} (f : Fin m -> term n) :=
  fin_match (variable fzero) (fun i => trename fsucc (f i)).
Inductive formula (n : nat) : Type :=
| equal : term n -> term n -> formula n
| less_equal : term n -> term n -> formula n
| add_graph : term n -> term n -> term n -> formula n
| mul_graph : term n -> term n -> term n -> formula n
| falsity : formula n
| implies : formula n -> formula n -> formula n
| all : formula (S n) -> formula n.
Arguments equal {n} _ _.
Arguments less_equal {n} _ _.
Arguments add_graph {n} _ _ _.
Arguments mul_graph {n} _ _ _.
Arguments falsity {n}.
Arguments implies {n} _ _.
Arguments all {n} _.
Fixpoint frename {m n} (f : Fin m -> Fin n) (A : formula m) : formula n :=
  match A with
  | equal t u => equal (trename f t) (trename f u)
  | less_equal t u => less_equal (trename f t) (trename f u)
  | add_graph t u v => add_graph (trename f t) (trename f u) (trename f v)
  | mul_graph t u v => mul_graph (trename f t) (trename f u) (trename f v)
  | falsity => falsity
  | implies B C => implies (frename f B) (frename f C)
  | all B => all (frename (weak f) B)
  end.
Fixpoint fsubst {m n} (f : Fin m -> term n) (A : formula m) : formula n :=
  match A with
  | equal t u => equal (tsubst f t) (tsubst f u)
  | less_equal t u => less_equal (tsubst f t) (tsubst f u)
  | add_graph t u v => add_graph (tsubst f t) (tsubst f u) (tsubst f v)
  | mul_graph t u v => mul_graph (tsubst f t) (tsubst f u) (tsubst f v)
  | falsity => falsity
  | implies B C => implies (fsubst f B) (fsubst f C)
  | all B => all (fsubst (lift_sub f) B)
  end.
Definition instantiate {n} (A : formula (S n)) (t : term n) :=
  fsubst (fin_match t variable) A.

(** Classical abbreviations use exactly the fixed negative encodings of the
    paper. Implication, falsity and universal quantification are primitive. *)
Definition neg {n} (A : formula n) := implies A falsity.
Definition conj {n} (A B : formula n) := neg (implies A (implies B falsity)).
Definition iff {n} (A B : formula n) := conj (implies A B) (implies B A).
Definition disj {n} (xs : list (formula n)) := fold_right (fun A B => implies (neg A) B) falsity xs.
Definition some {n} (A : formula (S n)) := neg (all (neg A)).
Fixpoint numeral {n} k : term n := match k with 0 => zero | S k => successor (numeral k) end.

Inductive axiom {n} : formula n -> Prop :=
| ax_add m k : axiom (all (iff (add_graph (numeral m) (numeral k) (variable fzero))
    (equal (numeral (m+k)) (variable fzero))))
| ax_mul m k : axiom (all (iff (mul_graph (numeral m) (numeral k) (variable fzero))
    (equal (numeral (m*k)) (variable fzero))))
| ax_neq m k : m <> k -> axiom (neg (equal (numeral m) (numeral k)))
| ax_bound k : axiom (all (iff (less_equal (variable fzero) (numeral k))
    (disj (map (fun i => equal (variable fzero) (numeral i)) (seq 0 (S k))))))
| ax_compare k : axiom (all (disj [less_equal (variable fzero) (numeral k);
    less_equal (numeral k) (variable fzero)])).

Inductive derives : forall n, list (formula n) -> formula n -> Prop :=
| hypothesis n Γ A : In A Γ -> derives n Γ A
| theory n Γ A : axiom A -> derives n Γ A
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
  revert n f g. induction A; intros n' f g H; cbn; f_equal;
    auto using tsubst_ext.
  apply IHA. intro i. dependent elimination i; cbn [lift_sub fin_match]; [reflexivity |rewrite H; reflexivity].
Qed.
Lemma source_modus_ponens {n} Γ (A B : formula n) :
  derives Γ (implies A B) -> derives Γ A -> derives Γ B.
Proof. apply implication_elim. Qed.
Lemma source_ex_falso {n} Γ (A : formula n) : derives Γ falsity -> derives Γ A.
Proof.
  intro H. assert (HW : forall n Γ B, @derives n Γ B -> forall Δ,
    (forall C, In C Γ -> In C Δ) -> derives Δ B).
  { intros m Δ B HD. induction HD; intros Ξ Hin.
    - apply hypothesis, Hin. assumption.
    - apply theory. assumption.
    - apply implication_intro, IHHD. intros C [<-|HC]; [left; reflexivity |right; auto].
    - eapply implication_elim; [apply IHHD1 |apply IHHD2]; exact Hin.
    - apply universal_intro, IHHD. intros C HC.
      apply in_map_iff in HC. destruct HC as [D [<- Hmember]]. apply in_map. auto.
    - apply universal_elim, IHHD. exact Hin.
    - apply classical, IHHD. exact Hin.
    - apply equality_refl.
    - eapply equality_replace; [apply IHHD1 |apply IHHD2]; exact Hin. }
  apply classical, implication_intro. apply (HW n Γ falsity H).
  intros C HC. right. exact HC.
Qed.
End Relational.
