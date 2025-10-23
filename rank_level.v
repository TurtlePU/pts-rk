Inductive ℕ : Type := zero | succ (pred : ℕ).

Definition pi_level : ℕ -> ℕ -> ℕ := fun x y => x.

Inductive Fin : ℕ -> Type :=
| fzero : forall n, Fin (succ n)
| fsucc : forall n, Fin n -> Fin (succ n).

Inductive Term (n : ℕ) : Type :=
| 𝒰 : ℕ -> Term n
| Π : Term n -> Term (succ n) -> Term n
| var : Fin n -> Term n
| λ : Term n -> Term (succ n) -> Term n
| app : Term n -> Term n -> Term n.
Arguments 𝒰 [_] _.
Arguments Π [_] _ _.
Arguments var [_] _.
Arguments λ [_] _ _.
Infix "$" := app (at level 90, left associativity).

Definition subst : forall {n},
  Term (succ n) -> Term n -> Term n := fun _ x y => y.
Notation "s ◁ t" := (subst s t) (at level 80, left associativity).

Inductive Ctx : ℕ -> Type :=
| ε : Ctx zero
| cons : forall {n}, Ctx n -> Term n -> Ctx (succ n).
Infix "," := cons (at level 40, left associativity).

Inductive index : forall {n : ℕ},
  Ctx n -> Fin n -> Term n -> Prop :=.

Reserved Notation "Γ ⊢ t ∈ T" (at level 30).
Inductive wf : forall {n : ℕ}, Ctx n -> Prop :=
| wf_empty : wf ε
| wf_cons : forall n (Γ : Ctx n) T ℓ,
    wf Γ -> Γ ⊢ T ∈ 𝒰 ℓ -> wf (Γ, T)
with typ : forall {n : ℕ},
  Ctx n -> Term n -> Term n -> Prop :=
| typ_univ : forall n (Γ : Ctx n) ℓ,
    wf Γ -> Γ ⊢ 𝒰 ℓ ∈ 𝒰 zero
| typ_pi : forall n (Γ : Ctx n) S T ℓₛ ℓₜ ℓ,
    Γ ⊢ S ∈ 𝒰 ℓₛ -> (Γ, S) ⊢ T ∈ 𝒰 ℓₜ ->
    pi_level ℓₛ ℓₜ ℓ -> Γ ⊢ Π S T ∈ 𝒰 ℓ
| typ_var : forall n (Γ : Ctx n) i T,
    index Γ i T -> Γ ⊢ var i ∈ T
| typ_lam : forall n (Γ : Ctx n) S t T ℓₛ ℓₜ,
    Γ ⊢ S ∈ 𝒰 ℓₛ -> (Γ, S) ⊢ t ∈ T -> (Γ, S) ⊢ T ∈ 𝒰 ℓₜ ->
    Γ ⊢ λ S t ∈ Π S T
| typ_app : forall n (Γ : Ctx n) t S T s,
    Γ ⊢ t ∈ Π S T -> Γ ⊢ s ∈ S ->
    Γ ⊢ t $ s ∈ T ◁ s
where "Γ ⊢ t ∈ T" := (typ Γ t T).
