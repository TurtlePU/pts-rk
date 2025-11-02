Require Import Stdlib.Program.Equality.

(* Fin type with helpers *)

Inductive Fin: nat -> Type :=
| fzero {n}: Fin (S n)
| fsucc {n}: Fin n -> Fin (S n).

Definition fin_match {A n} (z: A) (s: Fin n -> A)
  (x: Fin (S n)) : A :=
match x with
| fzero => fun _ => z
| @fsucc n' x => fun eq: n' = n =>
    s (eq_rect _ Fin x _ eq)
end eq_refl.

(* Definition of a term *)

Inductive Term (n: nat) : Type :=
| Rank: nat -> Term n
| Π: Term n -> Term (S n) -> Term n
| var: Fin n -> Term n
| λ: Term n -> Term (S n) -> Term n
| app: Term n -> Term n -> Term n.
Arguments Rank [_] _.
Arguments Π [_] _ _.
Arguments var [_] _.
Arguments λ [_] _ _.
Arguments app [_] _ _.
Infix "$" := app (at level 40, left associativity).

(* Term renaming *)

Definition weak {m n} (f: Fin m -> Fin n)
  : Fin (S m) -> Fin (S n) :=
  fin_match fzero (fun x => fsucc (f x)).

Fixpoint rename {m n} (f: Fin m -> Fin n) (t: Term m)
  : Term n :=
match t with
| Rank l => Rank l
| Π T U => Π (rename f T) (rename (weak f) U)
| var x => var (f x)
| λ T t => λ (rename f T) (rename (weak f) t)
| g $ t => rename f g $ rename f t
end.

Lemma rename_ext {m n} {f g: Fin m -> Fin n}:
  (forall i, f i = g i) ->
  forall t, rename f t = rename g t.
Proof.
intros. generalize dependent n.
induction t; intros; auto; simpl; f_equal; auto;
apply IHt2; intros; dependent destruction i; auto;
simpl; rewrite H; reflexivity.
Qed.

Lemma rename_comp {l m n}
  {f: Fin m -> Fin n} {g: Fin l -> Fin m} {t: Term l}:
  rename f (rename g t) = rename (fun i => f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; apply rename_ext;
intros; dependent destruction i; auto.
Qed.

(* Term substitution *)

Definition shift {n} (t: Term n) : Term (S n) :=
  rename (fun x => fsucc x) t.

Definition transpose {m n} (f: Fin m -> Term n)
  : Fin (S m) -> Term (S n) :=
  fin_match (var fzero) (fun x => shift (f x)).

Lemma transpose_ext {m n} (f g: Fin m -> Term n):
  (forall j, f j = g j) ->
  forall i, transpose f i = transpose g i.
Proof.
dependent destruction i.
- reflexivity.
- simpl. rewrite H. reflexivity.
Qed.

Fixpoint replace {m n} (f: Fin m -> Term n)
  (t: Term m) : Term n :=
match t with
| Rank l => Rank l
| Π T U => Π (replace f T) (replace (transpose f) U)
| var x => f x
| λ T t => λ (replace f T) (replace (transpose f) t)
| g $ t => replace f g $ replace f t
end.

Lemma replace_ext
  {m n} (f g: Fin m -> Term n) (t: Term m):
  (forall i, f i = g i) -> replace f t = replace g t.
Proof.
generalize dependent n.
induction t; intros; simpl; auto;
f_equal; auto; apply IHt2; intros;
rewrite transpose_ext with (g := g); auto.
Qed.

Lemma rename_replace {l m n}
  (f: Fin m -> Fin n) (g: Fin l -> Term m) (t: Term l):
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

Lemma replace_var {n} {f: Fin n -> Term n} {t: Term n}:
  (forall i, f i = var i) -> replace f t = t.
Proof.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; auto; dependent destruction i; auto;
simpl; rewrite H; auto.
Qed.

Lemma replace_rename {l m n}
  (f: Fin m -> Term n) (g: Fin l -> Fin m) (t: Term l):
  replace f (rename g t) =
  replace (fun i => f (g i)) t.
Proof.
generalize dependent n.
generalize dependent m.
induction t; intros; simpl; f_equal; auto;
rewrite IHt2; apply replace_ext; intros;
dependent destruction i; auto.
Qed.

Lemma replace_replace {l m n}
  (f: Fin m -> Term n) (g: Fin l -> Term m) (t: Term l):
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

Definition subst {n} (f: Term (S n)) (t: Term n)
  : Term n := replace (fin_match t (fun x => var x)) f.
Infix "◁" := subst (at level 45, left associativity).

Lemma rename_subst {n} {t: Term (S n)}:
  forall u m (f: Fin n -> Fin m),
  rename f (t ◁ u) = rename (weak f) t ◁ rename f u.
Proof.
unfold subst. intros.
rewrite rename_replace, replace_rename.
apply replace_ext. intros.
dependent destruction i; reflexivity.
Qed.

Lemma replace_subst {n} {t: Term (S n)}:
  forall u m (f: Fin n -> Term m),
  replace f (t ◁ u) =
  replace (transpose f) t ◁ replace f u.
Proof.
unfold subst. intros.
rewrite replace_replace, replace_replace.
apply replace_ext. dependent destruction i; simpl.
- reflexivity.
- unfold shift. rewrite replace_rename.
  rewrite replace_var. auto.
  dependent destruction i; auto.
Qed.
