(** Independent relational source theory. No PTS typing/inhabitation occurs
    in these definitions. Addition and multiplication remain graph symbols. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From Interpretation_of_R.relational Require Import DirectRRelationalSyntax.
Import ListNotations.
Module Source.
Import Relational.
Definition x0 {n} : term (S n) := variable fzero.
Definition x1 {n} : term (S (S n)) := variable (fsucc fzero).
Definition x2 {n} : term (S (S (S n))) := variable (fsucc (fsucc fzero)).
Definition x3 {n} : term (S (S (S (S n)))) := variable (fsucc (fsucc (fsucc fzero))).
Definition x4 {n} : term (S (S (S (S (S n))))) := variable (fsucc (fsucc (fsucc (fsucc fzero)))).
Definition x5 {n} : term (S (S (S (S (S (S n)))))) := variable (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).
Definition x6 {n} : term (S (S (S (S (S (S (S n))))))) := variable (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))).
Fixpoint close_formula (n : nat) : formula n -> formula 0 :=
  match n with 0 => fun A => A | S k => fun A => close_formula k (all A) end.
Definition close {n} := close_formula n.
Definition lt {n} (x y : term n) := conj (less_equal x y) (neg (equal x y)).
Definition one {n} : term n := successor zero.

Definition graph_total (op : forall n, term n -> term n -> term n -> formula n) :=
  close (n:=2) (some (op _ x2 x1 x0)).
Definition graph_unique (op : forall n, term n -> term n -> term n -> formula n) :=
  close (n:=4) (implies (op _ x3 x2 x1) (implies (op _ x3 x2 x0) (equal x1 x0))).
Definition graph_commutative (op : forall n, term n -> term n -> term n -> formula n) :=
  close (n:=3) (implies (op _ x2 x1 x0) (op _ x1 x2 x0)).
Definition graph_associative (op : forall n, term n -> term n -> term n -> formula n) :=
  close (n:=6) (implies (op _ x5 x4 x2)
    (implies (op _ x2 x3 x0) (implies (op _ x4 x3 x1) (op _ x5 x1 x0)))).
Definition add_zero := close (n:=1) (add_graph x0 zero x0).
Definition mul_zero := close (n:=1) (mul_graph x0 zero zero).
Definition mul_one := close (n:=1) (mul_graph x0 one x0).
Definition successor_add_one := close (n:=1)
  (add_graph x0 one (successor x0)).
Definition distributivity := close (n:=7)
  (implies (add_graph x5 x4 x3)
    (implies (mul_graph x6 x3 x2)
      (implies (mul_graph x6 x5 x1)
        (implies (mul_graph x6 x4 x0) (add_graph x1 x0 x2))))).
Definition additive_cancellation := close (n:=4)
  (implies (add_graph x3 x2 x0) (implies (add_graph x3 x1 x0) (equal x2 x1))).
Definition order_refl := close (n:=1) (less_equal x0 x0).
Definition order_trans := close (n:=3)
  (implies (less_equal x2 x1) (implies (less_equal x1 x0) (less_equal x2 x0))).
Definition order_antisym := close (n:=2)
  (implies (less_equal x1 x0) (implies (less_equal x0 x1) (equal x1 x0))).
Definition zero_least := close (n:=1) (less_equal zero x0).
Definition nontrivial : formula 0 := neg (equal zero one).
Definition graph_monotone (op : forall n, term n -> term n -> term n -> formula n) :=
  close (n:=5) (implies (op _ x4 x2 x1)
    (implies (op _ x3 x2 x0) (implies (less_equal x4 x3) (less_equal x1 x0)))).
Definition addition_strict_monotone := close (n:=5)
  (implies (add_graph x4 x2 x1)
    (implies (add_graph x3 x2 x0) (implies (lt x4 x3) (lt x1 x0)))).
Definition multiplication_strict_monotone := close (n:=5)
  (implies (mul_graph x4 x2 x1)
    (implies (mul_graph x3 x2 x0)
      (implies (lt x4 x3) (implies (lt zero x2) (lt x1 x0))))).
Definition strict_bounded n : formula 0 := all
  (iff (lt x0 (numeral n))
    (disj (map (fun i => equal x0 (numeral i)) (seq 0 n)))).
Definition rig_laws : list (formula 0) :=
  [graph_total (@add_graph); graph_total (@mul_graph);
   graph_unique (@add_graph); graph_unique (@mul_graph);
   graph_commutative (@add_graph); graph_commutative (@mul_graph);
   graph_associative (@add_graph); graph_associative (@mul_graph);
   add_zero; mul_zero; mul_one; distributivity; additive_cancellation;
   order_refl; order_trans; order_antisym; zero_least; nontrivial;
   graph_monotone (@add_graph); graph_monotone (@mul_graph);
   addition_strict_monotone; multiplication_strict_monotone; successor_add_one].
Inductive axiom : formula 0 -> Prop :=
| arithmetic_R A : Relational.axiom A -> axiom A
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
End Source.
