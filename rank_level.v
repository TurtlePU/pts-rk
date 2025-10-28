Require Import Classes.RelationClasses.
Require Import Program.Equality.
Import Logic.

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

(* Term reduction *)

Reserved Notation "t ↠ t'"
  (at level 50, no associativity).
Inductive step {n}: Term n -> Term n -> Prop :=
| step_pi_left {T T' U}: (T ↠ T') -> Π T U ↠ Π T' U
| step_pi_right {T U U'}: (U ↠ U') -> Π T U ↠ Π T U'
| step_lam_left {T T' t}: (T ↠ T') -> λ T t ↠ λ T' t
| step_lam_right {T t t'}: (t ↠ t') -> λ T t ↠ λ T t'
| step_app_left {f f' t}: (f ↠ f') -> f $ t ↠ f' $ t
| step_app_right {f t t'}: (t ↠ t') -> f $ t ↠ f $ t'
| step_beta T f t: (λ T f) $ t ↠ f ◁ t
where "t ↠ t'" := (step t t').

Reserved Notation "t ⇉ t'"
  (at level 50, no associativity).
Inductive par_step {n}: Term n -> Term n -> Prop :=
| par_step_refl t: t ⇉ t
| par_step_pi {T T' U U'}:
  (T ⇉ T') -> (U ⇉ U') -> Π T U ⇉ Π T' U'
| par_step_lam {T T' t t'}:
  (T ⇉ T') -> (t ⇉ t') -> λ T t ⇉ λ T' t'
| par_step_app {f f' t t'}:
  (f ⇉ f') -> (t ⇉ t') -> f $ t ⇉ f' $ t'
| par_step_beta {T f f' t t'}:
  (f ⇉ f') -> (t ⇉ t') -> (λ T f) $ t ⇉ f' ◁ t'
where "t ⇉ t'" := (par_step t t').

Instance par_step_reflexive {n}
  : Reflexive (@par_step n).
Proof. exact par_step_refl. Qed.

Lemma step_par_step {n} {t t': Term n}:
  (t ↠ t') -> (t ⇉ t').
Proof.
intro. induction H; constructor;
try constructor; assumption.
Qed.

Lemma rename_par_step {m} {t t': Term m}:
  t ⇉ t' ->
  forall n (f: Fin m -> Fin n),
  rename f t ⇉ rename f t'.
Proof.
intro. induction H; try constructor; auto.
intros. rewrite rename_subst. constructor; auto.
Qed.

Lemma shift_par_step {n} {t t': Term n}:
  t ⇉ t' -> shift t ⇉ shift t'.
Proof.
intro. unfold shift. apply rename_par_step. auto.
Qed.

Lemma transpose_par_step
  {m n} {f f': Fin m -> Term n}:
  (forall i, f i ⇉ f' i) ->
  forall j, transpose f j ⇉ transpose f' j.
Proof.
intros. dependent destruction j; simpl.
- reflexivity.
- apply shift_par_step. auto.
Qed.

Lemma replace_par_step {m} {t: Term m}:
  forall {n} {f f': Fin m -> Term n},
  (forall i, f i ⇉ f' i) ->
  replace f t ⇉ replace f' t.
Proof.
induction t; simpl; intros; try constructor; auto;
apply IHt2; intro; dependent destruction i;
try reflexivity; simpl; apply shift_par_step; auto.
Qed.

Lemma par_step_replace
  {m n} {f f': Fin m -> Term n} {t t': Term m}:
  (forall i, f i ⇉ f' i) -> t ⇉ t' ->
  replace f t ⇉ replace f' t'.
Proof.
intros. generalize dependent n.
induction H0; intros; simpl; try constructor; auto.
- apply replace_par_step. auto.
- apply IHpar_step2, transpose_par_step. auto.
- apply IHpar_step2, transpose_par_step. auto.
- rewrite replace_subst. constructor; auto.
  apply IHpar_step1, transpose_par_step. auto.
Qed.

Lemma sub_par_step {n} {f: Term (S n)}:
  forall {t} {t'}, (t ⇉ t') -> f ◁ t ⇉ f ◁ t'.
Proof.
intros. unfold subst. apply replace_par_step.
dependent destruction i; simpl; auto; reflexivity.
Qed.

Lemma par_step_sub
  {n} {f f': Term (S n)} {t t': Term n}:
  (f ⇉ f') -> (t ⇉ t') -> f ◁ t ⇉ f' ◁ t'.
Proof.
intros. unfold subst. apply par_step_replace; auto.
dependent destruction i; auto; reflexivity.
Qed.

Lemma par_step_lam_fun
  {n} {T t': Term n} {f: Term (S n)}:
  λ T f ⇉ t' -> exists T' f', and (t' = λ T' f')
                          (and (T ⇉ T') (f ⇉ f')).
Proof.
intro. inversion H; subst.
- exists T, f. repeat constructor.
- exists T', t'0. repeat constructor; auto.
Qed.

Lemma par_step_diamond {n} {t t₁ t₂: Term n}:
  (t ⇉ t₁) -> (t ⇉ t₂) ->
  exists u, and (t₁ ⇉ u) (t₂ ⇉ u).
Proof.
intros. induction H.
- exists t₂. repeat constructor; auto.
- inversion H0; subst.
  exists (Π T' U'). repeat constructor; auto.
  apply IHpar_step1 in H4. destruct H4 as [T₁ [H2 H4]].
  apply IHpar_step2 in H6. destruct H6 as [U₁ [H3 H6]].
  exists (Π T₁ U₁). repeat constructor; auto.
- inversion H0; subst.
  exists (λ T' t'). repeat constructor; auto.
  apply IHpar_step1 in H4. destruct H4 as [T₁ [H2 H4]].
  apply IHpar_step2 in H6. destruct H6 as [t₁ [H3 H6]].
  exists (λ T₁ t₁). repeat constructor; auto.
- inversion H0; subst.
  exists (f' $ t'). repeat constructor; auto.
  apply IHpar_step1 in H4. destruct H4 as [f₁ [H2 H4]].
  apply IHpar_step2 in H6. destruct H6 as [t₁ [H3 H6]].
  exists (f₁ $ t₁). repeat constructor; auto.
  apply par_step_lam_fun in H.
  destruct H as [T' [f'' [H [H7 H8]]]]. subst.
  apply @par_step_lam with (T := T) (T' := T) in H4.
  apply IHpar_step1 in H4. destruct H4 as [f₁ [H2 H4]].
  apply IHpar_step2 in H6. destruct H6 as [t₁ [H3 H6]].
  apply par_step_lam_fun in H2.
  destruct H2 as [T'0 [f' [H2 [H5 H9]]]]. subst.
  exists (f' ◁ t₁). repeat constructor; auto.
  apply par_step_lam_fun in H4.
  destruct H4 as [T'1 [f'1 [H4 [H10 H11]]]].
  inversion H4. subst. apply par_step_sub; auto.
  reflexivity.
Qed.

Inductive RTC {A} (R: A -> A -> Prop): A -> A -> Prop :=
| rtc_refl x: RTC R x x
| rtc_step {x y z}: R x y -> RTC R y z -> RTC R x z.

Inductive Sym {A} (R: A -> A -> Prop): A -> A -> Prop :=
| forward {x y}: R x y -> Sym R x y
| backwards {x y}: R y x -> Sym R x y.

Definition term_equiv {n}: Term n -> Term n -> Prop :=
  RTC (Sym step).
Infix "≡" := term_equiv (at level 50, no associativity).

(* Context with helpers *)

Inductive Ctx: nat -> Type :=
| ε: Ctx 0
| cons {n}: Ctx n -> Term n -> Ctx (S n).
Infix "&" := cons (at level 50, left associativity).

Definition ctx_pred {n} (Γ: Ctx (S n)) : Ctx n :=
match Γ with
| Γ & _ => Γ
end.

Definition ctx_top {n} (Γ: Ctx (S n)) : Term n :=
match Γ with
| _ & T => T
end.

(* Context indesing *)

Fixpoint index {n} : Ctx n -> Fin n -> Term n :=
match n with
| 0 => fun _ (i : Fin 0) => match i with end
| S n => fun (Γ : Ctx (S n)) i =>
  shift (fin_match (ctx_top Γ) (index (ctx_pred Γ)) i)
end.
Infix "!!" := index (at level 55, left associativity).

(* Typing in RLTT & context well-formedness *)

Reserved Notation "Γ ⊢ t ⇐ T" (at level 60).
Inductive wf : forall {n}, Ctx n -> Type :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx n} {T ℓ}:
    wf Γ -> Γ ⊢ T ⇐ Rank ℓ -> wf (Γ & T)
with typ : forall {n},
  Ctx n -> Term n -> Term n -> Type :=
| typ_rank {n} {Γ : Ctx n} ℓ:
    wf Γ -> Γ ⊢ Rank ℓ ⇐ Rank 0
| typ_pi {n} {Γ : Ctx n} {T U ℓₛ ℓₜ}:
    Γ ⊢ T ⇐ Rank ℓₛ -> Γ & T ⊢ U ⇐ Rank ℓₜ ->
    Γ ⊢ Π T U ⇐ Rank (max (S ℓₛ) ℓₜ)
| typ_var {n} {Γ : Ctx n} i:
    wf Γ -> Γ ⊢ var i ⇐ Γ !! i
| typ_lam {n} {Γ : Ctx n} {S t T ℓₛ ℓₜ}:
    Γ ⊢ S ⇐ Rank ℓₛ -> Γ & S ⊢ t ⇐ T ->
    Γ & S ⊢ T ⇐ Rank ℓₜ -> Γ ⊢ λ S t ⇐ Π S T
| typ_app {n} {Γ : Ctx n} {t S T s}:
    Γ ⊢ t ⇐ Π S T -> Γ ⊢ s ⇐ S ->
    Γ ⊢ t $ s ⇐ T ◁ s
| typ_conv {n} {Γ: Ctx n} {t T T'}:
    Γ ⊢ t ⇐ T -> T ≡ T' -> Γ ⊢ t ⇐ T'
where "Γ ⊢ t ⇐ T" := (typ Γ t T).

Lemma typToWF {n Γ t} {T: Term n} : Γ ⊢ t ⇐ T -> wf Γ.
Proof. intro; induction H; assumption. Qed.

Fixpoint ranks {n} {Γ: Ctx n} (H: wf Γ): list nat :=
match H with
| wf_empty => nil
| @wf_cons _ _ _ ℓ H _ => (ℓ :: ranks H)%list
end.

(* In predicate *)

Fixpoint In {A} (x: A) (xs: list A) : Prop :=
match xs with
| nil => False
| (x'::xs)%list => or (x = x') (In x xs)
end.

Lemma here {A} {x: A} {xs}: In x (x::xs).
Proof. left. reflexivity. Qed.

Lemma there {A} {x: A} {y xs}: In x xs -> In x (y::xs).
Proof. intro H. right. assumption. Qed.

(* New Foundations *)

Inductive Formula (ls : list nat) : Type :=
| nf_eq {ℓ}: In ℓ ls -> In ℓ ls -> Formula ls
| nf_in {ℓ}: In ℓ ls -> In (S ℓ) ls -> Formula ls
| nf_not: Formula ls -> Formula ls
| nf_to: Formula ls -> Formula ls -> Formula ls
| nf_all ℓ: Formula (ℓ :: ls) -> Formula ls.
Arguments nf_eq [_] [_] _ _.
Arguments nf_in [_] [_] _ _.
Arguments nf_not [_] _.
Arguments nf_to [_] _ _.
Arguments nf_all [_] _ _.
Infix "~" := nf_eq (at level 45, no associativity).
Infix "∈" := nf_in (at level 45, no associativity).
Notation "¬ φ" := (nf_not φ) (at level 40).
Infix "→" := nf_to (at level 60, right associativity).
Notation "∀ ℓ . φ" := (nf_all ℓ φ) (at level 65).

Definition lift {ℓ ks ls}
  (f: forall κ, In κ ks -> In κ ls) (κ: nat)
  (i: In κ (ℓ::ks)) : In κ (ℓ::ls) :=
match i with
| or_introl i => or_introl i
| or_intror i => or_intror (f _ i)
end.

Lemma lower {ℓ ls} (i: In ℓ ls) (κ: nat)
  (j: In κ (ℓ::ls)) : In κ ls.
Proof.
induction ls.
- inversion i.
- inversion j.
  + rewrite H; assumption.
  + assumption.
Qed.

Fixpoint remap {ks ls}
  (f: forall ℓ, In ℓ ks -> In ℓ ls) (φ: Formula ks)
  : Formula ls :=
match φ with
| x ~ y => f _ x ~ f _ y
| x ∈ y => f _ x ∈ f _ y
| ¬ φ => ¬ remap f φ
| φ → ψ => remap f φ → remap f ψ
| (∀ ℓ . φ) => (∀ ℓ . remap (lift f) φ)
end.

Definition nf_and {ls} (φ ψ: Formula ls): Formula ls :=
  ¬ (φ → ¬ ψ).
Infix "∧" := nf_and (at level 50, left associativity).

Definition nf_equiv {ls} (φ ψ: Formula ls)
  : Formula ls := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := nf_equiv (at level 60, no associativity).

Definition nf_exists {ls} ℓ (φ: Formula (ℓ::ls))
  : Formula ls := (¬ ∀ ℓ . ¬ φ).
Notation "∃ ℓ . φ" := (nf_exists ℓ φ) (at level 65).

Inductive true {ls}: Formula ls -> Prop :=
| true_ext {ℓ} (A B : In (S ℓ) ls) : true (
    (∀ ℓ . here ∈ there A ↔ here ∈ there B) → A ~ B
  )
| true_comp {ℓ} (φ: Formula (ℓ::ls)): true (
    ∃ S ℓ . ∀ ℓ .
      here ∈ there here ↔
      remap (lift (fun _ => there)) φ
  )
| mp φ ψ: true (φ → ψ) -> true φ -> true ψ
| K φ ψ: true (φ → ψ → φ)
| S φ ψ χ: true ((φ → ψ → χ) → (φ → ψ) → φ → χ)
| DNE φ: true (¬ ¬ φ → φ)
| allK ℓ φ ψ: true ((∀ ℓ . φ → ψ) → (∀ ℓ . φ) → ∀ ℓ . ψ)
| gen φ ℓ: true (φ → ∀ ℓ. remap (fun _ => there) φ)
| inst ℓ φ (i: In ℓ ls): true (
    (∀ ℓ . φ) → remap (lower i) φ
  ).

Fixpoint eval_type
  {n Γ ℓ} {T: Term n} (H: Γ ⊢ T ⇐ Rank ℓ)
  : Formula (ℓ :: ranks (typToWF H)) :=
match H with
| typ_rank ℓ _ => _
| typ_pi typT typU => _
| typ_var i _ => _
| typ_app f t => _
| typ_conv typT TeqT' => _
end.
