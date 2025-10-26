Import Logic.

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
Infix "$" := app (at level 130, left associativity).

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
Infix "◁" := subst (at level 120, left associativity).

Inductive Ctx: nat -> Type :=
| ε: Ctx 0
| cons {n}: Ctx n -> Term n -> Ctx (S n).
Infix "∧" := cons (at level 110, left associativity).

Definition ctx_pred {n} (Γ: Ctx (S n)) : Ctx n :=
match Γ with
| Γ ∧ _ => Γ
end.

Definition ctx_top {n} (Γ: Ctx (S n)) : Term n :=
match Γ with
| _ ∧ T => T
end.

Fixpoint index {n} : Ctx n -> Fin n -> Term n :=
match n with
| 0 => fun _ (i : Fin 0) => match i with end
| S n => fun (Γ : Ctx (S n)) i =>
  shift (fin_match (ctx_top Γ) (index (ctx_pred Γ)) i)
end.
Infix "!!" := index (at level 110, left associativity).

Reserved Notation "Γ ⊢ t ∈ T" (at level 30).
Inductive wf : forall {n}, Ctx n -> Prop :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx n} {T ℓ}:
    wf Γ -> Γ ⊢ T ∈ Rank ℓ -> wf (Γ ∧ T)
with typ : forall {n},
  Ctx n -> Term n -> Term n -> Prop :=
| typ_rank {n} {Γ : Ctx n} {ℓ}:
    wf Γ -> Γ ⊢ Rank ℓ ∈ Rank 0
| typ_pi {n} {Γ : Ctx n} {T U ℓₛ ℓₜ}:
    Γ ⊢ T ∈ Rank ℓₛ -> (Γ ∧ T) ⊢ U ∈ Rank ℓₜ ->
    Γ ⊢ Π T U ∈ Rank (max (S ℓₛ) ℓₜ)
| typ_var {n} {Γ : Ctx n} {i}:
    Γ ⊢ var i ∈ (Γ !! i)
| typ_lam {n} {Γ : Ctx n} {S t T ℓₛ ℓₜ}:
    Γ ⊢ S ∈ Rank ℓₛ -> (Γ ∧ S) ⊢ t ∈ T ->
    (Γ ∧ S) ⊢ T ∈ Rank ℓₜ -> Γ ⊢ λ S t ∈ Π S T
| typ_app {n} {Γ : Ctx n} {t S T s}:
    Γ ⊢ t ∈ Π S T -> Γ ⊢ s ∈ S ->
    Γ ⊢ (t $ s) ∈ (T ◁ s)
where "Γ ⊢ t ∈ T" := (typ Γ t T).
