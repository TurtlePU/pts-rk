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

(* WHE stands for Weak Head Expansion *)
Inductive WHE {L n}: relation (Term L n) :=
| whe_there t t' u: WHE t t' -> WHE (t $ u) (t' $ u)
| whe_here U t u:
    SN U -> SN u -> WHE (λ U t $ u) (t ◁ u).

Fixpoint adjust {m n}: Fin n -> Fin (m + n) :=
match m with
| 0 => fun i => i
| S m => fun i => fsucc (adjust i)
end.

Lemma adjust_SN {L n} m (t: Term L n):
  SN (rename (@adjust m _) t) -> SN t.
Proof. intros. dependent induction H. constructor.
intros. apply H0 with (m := m) (y := rename adjust y);
auto. apply rename_step. auto. Qed.

Lemma rename_whe {L m n} (f: Fin m -> Fin n)
  (t t': Term L m):
  WHE t t' -> WHE (rename f t) (rename f t').
Proof. intros. induction H.
- constructor. auto.
- rewrite rename_subst.
  constructor; apply rename_SN; auto.
Qed.

Lemma whe_SN {L n} (t t' u: Term L n):
  WHE t t' -> SN (t' $ u) -> SN (t $ u).
Proof. Admitted. (* FIXME: adapt Altenkirch *)
