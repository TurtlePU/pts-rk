From Equations Require Import Equations.

Inductive Fin: nat -> Type :=
| fzero {n}: Fin (S n)
| fsucc {n}: Fin n -> Fin (S n).

Inductive Term (L: Type) (n: nat) : Type :=
| 𝓤: L -> Term L n
| Π: Term L n -> Term L (S n) -> Term L n
| var: Fin n -> Term L n
| lam: Term L n -> Term L (S n) -> Term L n
| app: Term L n -> Term L n -> Term L n.
Arguments 𝓤 [_] [_] _.
Arguments Π [_] [_] _ _.
Arguments var [_] [_] _.
Arguments lam [_] [_] _ _.
Arguments app [_] [_] _ _.
Notation "[ T ] t" := (lam T t) (at level 30).
Infix "$" := app (at level 40, left associativity).
Derive NoConfusion NoConfusionHom for Term.

Definition fin_match {A: Type} {n} (z: A)
  (s: Fin n -> A) (x: Fin (S n)) : A :=
match x with
| fzero => fun _ => z
| @fsucc n' x => fun eq: n' = n =>
    s (eq_rect _ Fin x _ eq)
end eq_refl.

Definition weak {m n} (f: Fin m -> Fin n):
  Fin (S m) -> Fin (S n) :=
fin_match fzero (fun x => fsucc (f x)).

Fixpoint rename {L m n} (f: Fin m -> Fin n)
  (t: Term L m): Term L n :=
match t with
| 𝓤 ℓ => 𝓤 ℓ
| Π T U => Π (rename f T) (rename (weak f) U)
| var x => var (f x)
| [ T ] t => [ rename f T ] rename (weak f) t
| g $ t => rename f g $ rename f t
end.

Definition shift {L n} (t: Term L n) : Term L (S n) :=
  rename (fun x => fsucc x) t.

Definition transpose {L m n} (f: Fin m -> Term L n):
  Fin (S m) -> Term L (S n) :=
fin_match (var fzero) (fun x => shift (f x)).

Fixpoint replace {L m n} (f: Fin m -> Term L n)
  (t: Term L m) : Term L n :=
match t with
| 𝓤 ℓ => 𝓤 ℓ
| Π T U => Π (replace f T) (replace (transpose f) U)
| var x => f x
| [ T ] t => [ replace f T ] replace (transpose f) t
| g $ t => replace f g $ replace f t
end.

Definition subst {L n}
  (f: Term L (S n)) (t: Term L n): Term L n :=
replace (fin_match t (fun x => var x)) f.
Infix "◁" := subst (at level 45, left associativity).

Fixpoint push {L m n} (t: Term L n):
  Fin (S m + n) -> Term L (m + n) :=
match m with
| 0 => fin_match t (fun x => var x)
| S m =>
  fin_match (var fzero) (fun i => shift (push t i))
end.

Definition subst_at {L m n}
  (f: Term L (S (m + n))) (t: Term L n):
  Term L (m + n) := replace (push t) f.
Infix "◁ᵢ" :=
  subst_at (at level 45, left associativity).

Lemma rename_ext {L m n} (f g: Fin m -> Fin n):
  (forall i, f i = g i) ->
  forall t: Term L m, rename f t = rename g t.
Proof.
intros. generalize dependent n.
induction t; intros; auto; simpl; f_equal; auto;
apply IHt2; intros; dependent elimination i; auto;
simpl; rewrite H; reflexivity.
Qed.

Lemma replace_ext {L m n} (f g: Fin m -> Term L n):
  (forall i, f i = g i) ->
  forall t, replace f t = replace g t.
Proof.
assert (transpose_ext: forall L m n
  (f g: Fin m -> Term L n),
  (forall j, f j = g j) ->
  forall i, transpose f i = transpose g i).
  { clear. intros. dependent elimination i.
    - reflexivity.
    - simpl. rewrite H. reflexivity.
  }
intros. generalize dependent n.
induction t; intros; simpl; f_equal; auto.
Qed.

Create Rewrite HintDb syntax.
Ltac syntax_simp :=
  simpl; unfold shift, push, subst, subst_at; simpl;
  autorewrite with syntax; auto.

Lemma rename_id {L n} (t: Term L n):
  rename (fun i => i) t = t.
Proof.
induction t; simpl; f_equal; auto;
transitivity (rename (fun i => i) t2); auto;
apply rename_ext; intros; dependent elimination i; auto.
Qed.
Hint Rewrite @rename_id: syntax.

Lemma rename_comp {L l m n}
  (f: Fin m -> Fin n) (g: Fin l -> Fin m) (t: Term L l):
  rename f (rename g t) = rename (fun i => f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; apply rename_ext;
intros; dependent elimination i; auto.
Qed.
Hint Rewrite @rename_comp: syntax.

Lemma rename_replace {L l m n} (f: Fin m -> Fin n)
  (g: Fin l -> Term L m) (t: Term L l):
  rename f (replace g t) =
  replace (fun i => rename f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto; rewrite IHt2;
apply replace_ext; intros;
dependent elimination i; syntax_simp.
Qed.
Hint Rewrite @rename_replace: syntax.

Lemma replace_rename {L l m n} (f: Fin m -> Term L n)
  (g: Fin l -> Fin m) (t: Term L l):
  replace f (rename g t) = replace (fun i => f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; apply replace_ext; intros;
dependent elimination i; auto.
Qed.
Hint Rewrite @replace_rename: syntax.

Lemma replace_var {L n} (t: Term L n):
  replace (fun x => var x) t = t.
Proof.
induction t; simpl; f_equal; auto;
transitivity (replace (fun x => var x) t2); auto;
apply replace_ext;
intros; dependent elimination i; auto.
Qed.
Hint Rewrite @replace_var: syntax.

Lemma replace_replace {L l m n} (f: Fin m -> Term L n)
  (g: Fin l -> Term L m) (t: Term L l):
  replace f (replace g t) =
  replace (fun i => replace f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; apply replace_ext; intros;
dependent elimination i; syntax_simp.
Qed.
Hint Rewrite @replace_replace: syntax.

Lemma rename_subst {L n} {t: Term L (S n)}:
  forall u m (f: Fin n -> Fin m),
  rename f (t ◁ u) = rename (weak f) t ◁ rename f u.
Proof.
unfold subst. intros.
autorewrite with syntax.
apply replace_ext. intros.
dependent elimination i; reflexivity.
Qed.
Hint Rewrite @rename_subst: syntax.

Lemma replace_subst {L n} {t: Term L (S n)}:
  forall u m (f: Fin n -> Term L m),
  replace f (t ◁ u) =
  replace (transpose f) t ◁ replace f u.
Proof.
unfold subst. intros.
autorewrite with syntax.
apply replace_ext. intros.
dependent elimination i; syntax_simp.
Qed.
Hint Rewrite @replace_subst: syntax.

Fixpoint up {m n}: Fin n -> Fin (m + n) :=
match m with
| 0 => fun x => x
| S m => fun x => fsucc (up x)
end.

Lemma shift_up {L m n} (t: Term L n):
  shift (rename (@up m n) t) = rename (@up (S m) n) t.
Proof. syntax_simp. Qed.

Fixpoint division {m n}: Fin (S m + n) :=
match m with
| 0 => fzero
| S m => fsucc division
end.

Lemma subst_at_var {L m n}
  (f: Fin (S m + n)) (u: Term L n):
  (f = division /\ var f ◁ᵢ u = rename up u)
  \/ exists i, var f ◁ᵢ u = var i.
Proof. unfold subst_at. induction m.
- dependent elimination f; simpl.
  + syntax_simp.
  + right. eexists. auto.
- dependent elimination f as [fzero | fsucc f]; simpl.
  + right. eexists. auto.
  + specialize IHm with (f := f). destruct IHm.
    * unfold shift. simpl in H. destruct H.
      rewrite H0, H. syntax_simp.
    * simpl in H. destruct H. rewrite H.
      right. eexists. reflexivity.
Qed.
