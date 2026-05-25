Require Import Stdlib.Program.Equality.

Inductive Fin: nat -> Type :=
| fzero {n}: Fin (S n)
| fsucc {n}: Fin n -> Fin (S n).

Inductive Term (L: Type) (n: nat) : Type :=
| 𝓤: L -> Term L n
| Π: Term L n -> Term L (S n) -> Term L n
| var: Fin n -> Term L n
| λ: Term L n -> Term L (S n) -> Term L n
| app: Term L n -> Term L n -> Term L n.
Arguments 𝓤 [_] [_] _.
Arguments Π [_] [_] _ _.
Arguments var [_] [_] _.
Arguments λ [_] [_] _ _.
Arguments app [_] [_] _ _.
Infix "$" := app (at level 40, left associativity).

Definition fin_match {A n} (z: A) (s: Fin n -> A)
  (x: Fin (S n)) : A :=
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
| λ T t => λ (rename f T) (rename (weak f) t)
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
| λ T t => λ (replace f T) (replace (transpose f) t)
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
apply IHt2; intros; dependent destruction i; auto;
simpl; rewrite H; reflexivity.
Qed.

Lemma transpose_ext {L m n} (f g: Fin m -> Term L n):
  (forall j, f j = g j) ->
  forall i, transpose f i = transpose g i.
Proof.
dependent destruction i.
- reflexivity.
- simpl. rewrite H. reflexivity.
Qed.

Lemma replace_ext {L m n} (f g: Fin m -> Term L n):
  (forall i, f i = g i) ->
  forall t, replace f t = replace g t.
Proof.
intros. generalize dependent n.
induction t; intros; simpl; f_equal; auto;
apply IHt2, transpose_ext; auto.
Qed.

Lemma rename_comp {L l m n}
  (f: Fin m -> Fin n) (g: Fin l -> Fin m) (t: Term L l):
  rename f (rename g t) = rename (fun i => f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; apply rename_ext;
intros; dependent destruction i; auto.
Qed.

Lemma rename_replace {L l m n} (f: Fin m -> Fin n)
  (g: Fin l -> Term L m) (t: Term L l):
  rename f (replace g t) =
  replace (fun i => rename f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto; rewrite IHt2;
apply replace_ext; intros; dependent destruction i;
auto; simpl; unfold shift;
rewrite rename_comp, rename_comp; reflexivity.
Qed.

Lemma replace_rename {L l m n} (f: Fin m -> Term L n)
  (g: Fin l -> Fin m) (t: Term L l):
  replace f (rename g t) = replace (fun i => f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; apply replace_ext; intros;
dependent destruction i; auto.
Qed.

Lemma replace_var {L n} (t: Term L n):
  replace (fun x => var x) t = t.
Proof.
induction t; simpl; f_equal; auto;
transitivity (replace (fun x => var x) t2); auto;
apply replace_ext; dependent destruction i; auto.
Qed.

Lemma replace_replace {L l m n} (f: Fin m -> Term L n)
  (g: Fin l -> Term L m) (t: Term L l):
  replace f (replace g t) =
  replace (fun i => replace f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; apply replace_ext;
dependent destruction i; auto; simpl; unfold shift;
rewrite replace_rename, rename_replace;
apply replace_ext; auto.
Qed.

Lemma rename_subst {L n} {t: Term L (S n)}:
  forall u m (f: Fin n -> Fin m),
  rename f (t ◁ u) = rename (weak f) t ◁ rename f u.
Proof.
unfold subst. intros.
rewrite rename_replace, replace_rename.
apply replace_ext. intros.
dependent destruction i; reflexivity.
Qed.

Lemma replace_subst {L n} {t: Term L (S n)}:
  forall u m (f: Fin n -> Term L m),
  replace f (t ◁ u) =
  replace (transpose f) t ◁ replace f u.
Proof.
unfold subst. intros.
rewrite replace_replace, replace_replace.
apply replace_ext. dependent destruction i; simpl.
- reflexivity.
- unfold shift. rewrite replace_rename. symmetry.
  transitivity (replace (fun x => var x) (f i)).
  + apply replace_ext. auto.
  + apply replace_var.
Qed.

Lemma shift_subst {L n} (t u: Term L n):
  shift t ◁ u = t.
Proof.
unfold shift, subst. rewrite replace_rename.
transitivity (replace (fun x => var x) t).
- apply replace_ext. destruct i; reflexivity.
- apply replace_var.
Qed.

Lemma shift_subst_at {L m n}
  (t: Term L (S m + n)) (u: Term L n):
  shift t ◁ᵢ u = shift (t ◁ᵢ u).
Proof.
unfold shift, subst_at.
rewrite replace_rename, rename_replace.
apply replace_ext. reflexivity.
Qed.
