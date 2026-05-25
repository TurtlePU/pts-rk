Require Import Stdlib.Program.Equality.
Require Import Stdlib.Relations.Relations.
Require Import Syntax.
Require Import Reduction.
Require Import Atomic.

Inductive Acc {A} (R: relation A): A -> Prop :=
| acc x: (forall y, R x y -> Acc R y) -> Acc R x.

Definition SN {L n}: Term L n -> Prop := Acc (step L n).

Lemma head_SN {L n} (t u: Term L n): SN (t $ u) -> SN t.
Proof.
intro. dependent induction H. constructor. intros.
apply H0 with (y := y $ u) (u := u).
- apply step_app_left. auto.
- auto.
Qed.

Lemma atomic_app_SN {L n} (t u: Term L n):
  Atomic t -> SN t -> SN u -> SN (t $ u).
Proof.
intros. induction H0. induction H1.
constructor. intros. inversion H4.
- apply H2. auto.
  apply atomic_preservation with (t := x); auto.
- apply H3. auto. intros.
  assert (H': SN (y0 $ x0)). { apply H2; auto. }
  dependent destruction H'.
  apply H11, step_app_right. auto.
- subst. inversion H.
Qed.

Lemma rename_SN {L m n}
  (f: Fin m -> Fin n) (t: Term L m):
  SN t -> SN (rename f t).
Proof.
intro. generalize dependent n. induction H. constructor.
intros. apply rename_step_is_renamed in H1.
destruct H1 as [v [H1 H2]]. subst. apply H0. auto.
Qed.
