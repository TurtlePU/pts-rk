Import Logic.

(* Fin type with helpers *)

Inductive Fin: nat -> Type :=
| fzero {n}: Fin (S n)
| fsucc {n}: Fin n -> Fin (S n).
Arguments fsucc [_] _.

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

(* Term substitution *)

Definition shift {n} (t: Term n) : Term (S n) :=
  rename (fun x => fsucc x) t.

Definition transpose {m n} (f: Fin m -> Term n)
  : Fin (S m) -> Term (S n) :=
  fin_match (var fzero) (fun x => shift (f x)).

Fixpoint replace {m n} (f: Fin m -> Term n)
  (t: Term m) : Term n :=
match t with
| Rank l => Rank l
| Π T U => Π (replace f T) (replace (transpose f) U)
| var x => f x
| λ T t => λ (replace f T) (replace (transpose f) t)
| g $ t => replace f g $ replace f t
end.

Definition subst {n} (f: Term (S n)) (t: Term n)
  : Term n := replace (fin_match t (fun x => var x)) f.
Infix "◁" := subst (at level 45, left associativity).

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

Reserved Notation "Γ ⊢ t ∈ T" (at level 60).
Inductive wf : forall {n}, Ctx n -> Prop :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx n} {T ℓ}:
    wf Γ -> Γ ⊢ T ∈ Rank ℓ -> wf (Γ & T)
with typ : forall {n},
  Ctx n -> Term n -> Term n -> Prop :=
| typ_rank {n} {Γ : Ctx n} ℓ:
    wf Γ -> Γ ⊢ Rank ℓ ∈ Rank 0
| typ_pi {n} {Γ : Ctx n} {T U ℓₛ ℓₜ}:
    Γ ⊢ T ∈ Rank ℓₛ -> Γ & T ⊢ U ∈ Rank ℓₜ ->
    Γ ⊢ Π T U ∈ Rank (max (S ℓₛ) ℓₜ)
| typ_var {n} {Γ : Ctx n} i:
    wf Γ -> Γ ⊢ var i ∈ Γ !! i
| typ_lam {n} {Γ : Ctx n} {S t T ℓₛ ℓₜ}:
    Γ ⊢ S ∈ Rank ℓₛ -> Γ & S ⊢ t ∈ T ->
    Γ & S ⊢ T ∈ Rank ℓₜ -> Γ ⊢ λ S t ∈ Π S T
| typ_app {n} {Γ : Ctx n} {t S T s}:
    Γ ⊢ t ∈ Π S T -> Γ ⊢ s ∈ S ->
    Γ ⊢ t $ s ∈ T ◁ s
where "Γ ⊢ t ∈ T" := (typ Γ t T).

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
| nf_eq {l}: In l ls -> In l ls -> Formula ls
| nf_in {l}: In l ls -> In (S l) ls -> Formula ls
| nf_not: Formula ls -> Formula ls
| nf_to: Formula ls -> Formula ls -> Formula ls
| nf_all l: Formula (l :: ls) -> Formula ls.
Arguments nf_eq [_] [_] _ _.
Arguments nf_in [_] [_] _ _.
Arguments nf_not [_] _.
Arguments nf_to [_] _ _.
Arguments nf_all [_] _ _.
Infix "~" := nf_eq (at level 45, no associativity).
Infix "∈" := nf_in (at level 45, no associativity).
Notation "¬ f" := (nf_not f) (at level 40).
Infix "→" := nf_to (at level 60, right associativity).
Notation "∀ l . f" := (nf_all l f) (at level 65).

Definition lift {l ks ls}
  (f: forall k, In k ks -> In k ls) (k: nat)
  (i: In k (l::ks)) : In k (l::ls) :=
match i with
| or_introl i => or_introl i
| or_intror i => or_intror (f _ i)
end.

Lemma lower {l ls} (i: In l ls) (k: nat)
  (j: In k (l::ls)) : In k ls.
Proof.
induction ls.
- inversion i.
- inversion j.
  + rewrite H; assumption.
  + assumption.
Qed.

Fixpoint remap {ks ls}
  (f: forall l, In l ks -> In l ls) (g: Formula ks)
  : Formula ls :=
match g with
| x ~ y => f _ x ~ f _ y
| x ∈ y => f _ x ∈ f _ y
| ¬ g => ¬ remap f g
| g → h => remap f g → remap f h
| (∀ l . g) => (∀ l . remap (lift f) g)
end.

Definition nf_and {ls} (f g: Formula ls): Formula ls :=
  ¬ (f → ¬ g).
Infix "∧" := nf_and (at level 50, left associativity).

Definition nf_equiv {ls} (f g: Formula ls)
  : Formula ls := (f → g) ∧ (g → f).
Infix "↔" := nf_equiv (at level 60, no associativity).

Definition nf_exists {ls} l (f: Formula (l::ls))
  : Formula ls := (¬ ∀ l . ¬ f).
Notation "∃ l . f" := (nf_exists l f) (at level 65).

Inductive true {ls}: Formula ls -> Prop :=
| true_ext {l} (A B : In (S l) ls) : true (
    (∀ l . here ∈ there A ↔ here ∈ there B) → A ~ B
  )
| true_comp {l} (φ: Formula (l::ls)): true (
    ∃ S l . ∀ l .
      here ∈ there here ↔
      remap (lift (fun _ => there)) φ
  )
| mp φ ψ: true (φ → ψ) -> true φ -> true ψ
| K φ ψ: true (φ → ψ → φ)
| S φ ψ χ: true ((φ → ψ → χ) → (φ → ψ) → φ → χ)
| DNE φ: true (¬ ¬ φ → φ)
| allK l φ ψ: true ((∀ l . φ → ψ) → (∀ l . φ) → ∀ l . ψ)
| gen φ l: true (φ → ∀ l . remap (fun _ => there) φ)
| inst l φ (i: In l ls): true (
    (∀ l . φ) → remap (lower i) φ
  ).
