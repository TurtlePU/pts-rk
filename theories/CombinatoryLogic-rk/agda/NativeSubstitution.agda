{-# OPTIONS --cubical --safe --guardedness #-}
module NativeSubstitution where

-- Original derivations are preserved by well-typed context morphisms.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction
open import NativeTyping
open import NativeAlgebra

private
  variable
    m n : Nat

StrictRen : Context m → Context n → (Fin m → Fin n) → Set
StrictRen Γ Δ ρ = ∀ i → rename ρ (lookup Γ i) ≡ lookup Δ (ρ i)

strict-lift : ∀ {Γ : Context m} {Δ : Context n} {ρ}
  → StrictRen Γ Δ ρ → (A : Term m)
  → StrictRen (extend Γ A) (extend Δ (rename ρ A)) (liftRenaming ρ)
strict-lift {Γ = Γ} {Δ} {ρ} h A i = fin-cases
  (λ i → rename (liftRenaming ρ) (lookup (extend Γ A) i)
    ≡ lookup (extend Δ (rename ρ A)) (liftRenaming ρ i))
  i (rename-shift ρ A)
  (λ j → rename-shift ρ (lookup Γ j) ∙ cong shift (h j))

strict-renaming : ∀ {Γ : Context m} {Δ : Context n} {ρ t T}
  → StrictRen Γ Δ ρ → Typ Γ t T → Typ Δ (rename ρ t) (rename ρ T)
strict-renaming h (universe i) = universe i
strict-renaming {Γ = Γ} {Δ} h (product p q) = product (strict-renaming h p)
  (strict-renaming (strict-lift {Γ = Γ} {Δ} h _) q)
strict-renaming {Δ = Δ} {ρ} h (lookup-var i) =
  subst (Typ Δ (var (ρ i))) (sym (h i)) (lookup-var (ρ i))
strict-renaming {Γ = Γ} {Δ} h (abstraction p q) = abstraction (strict-renaming h p)
  (strict-renaming (strict-lift {Γ = Γ} {Δ} h _) q)
strict-renaming {Δ = Δ} {ρ} h (application {y = y} {B = B} p q) =
  subst (Typ Δ _) (sym (rename-substitute ρ B y))
    (application (strict-renaming h p) (strict-renaming h q))
strict-renaming h (conversion p q b) = conversion
  (strict-renaming h p) (strict-renaming h q) (beta-rename _ b)

weakening : ∀ {Γ : Context n} {A t T}
  → Typ Γ t T → Typ (extend Γ A) (shift t) (shift T)
weakening = strict-renaming (λ i → refl)

TypedSub : Context m → Context n → (Fin m → Term n) → Set
TypedSub Γ Δ σ = ∀ i → Typ Δ (σ i) (replace σ (lookup Γ i))

typed-lift : ∀ {Γ : Context m} {Δ : Context n} {σ}
  → TypedSub Γ Δ σ → (A : Term m)
  → TypedSub (extend Γ A) (extend Δ (replace σ A)) (liftSubstitution σ)
typed-lift {Γ = Γ} {Δ} {σ} h A i = fin-cases
  (λ i → Typ (extend Δ (replace σ A)) (liftSubstitution σ i)
    (replace (liftSubstitution σ) (lookup (extend Γ A) i))) i
  (subst (Typ (extend Δ (replace σ A)) (var fzero))
    (sym (replace-shift σ A)) (lookup-var fzero))
  (λ j → subst (Typ (extend Δ (replace σ A)) (shift (σ j)))
    (sym (replace-shift σ (lookup Γ j))) (weakening (h j)))

typed-replace : ∀ {Γ : Context m} {Δ : Context n} {σ t T}
  → TypedSub Γ Δ σ → Typ Γ t T → Typ Δ (replace σ t) (replace σ T)
typed-replace h (universe i) = universe i
typed-replace {Γ = Γ} {Δ} h (product p q) = product (typed-replace h p)
  (typed-replace (typed-lift {Γ = Γ} {Δ} h _) q)
typed-replace h (lookup-var i) = h i
typed-replace {Γ = Γ} {Δ} h (abstraction p q) = abstraction (typed-replace h p)
  (typed-replace (typed-lift {Γ = Γ} {Δ} h _) q)
typed-replace {Δ = Δ} {σ} h (application {y = y} {B = B} p q) =
  subst (Typ Δ _) (sym (replace-substitute σ B y))
    (application (typed-replace h p) (typed-replace h q))
typed-replace h (conversion p q b) = conversion
  (typed-replace h p) (typed-replace h q) (beta-replace _ b)

single-typed : ∀ {Γ : Context n} {A y}
  → Typ Γ y A → TypedSub (extend Γ A) Γ (single y)
single-typed {Γ = Γ} {A} {y} p i = fin-cases
  (λ i → Typ Γ (single y i) (replace (single y) (lookup (extend Γ A) i))) i
  (subst (Typ Γ y) (sym (substitute-shift A y)) p)
  (λ j → subst (Typ Γ (var j)) (sym (substitute-shift (lookup Γ j) y)) (lookup-var j))

substitution : ∀ {Γ : Context n} {A b B y}
  → Typ (extend Γ A) b B → Typ Γ y A
  → Typ Γ (substitute b y) (substitute B y)
substitution p q = typed-replace (single-typed q) p

TypedRen : Context m → Context n → (Fin m → Fin n) → Set
TypedRen Γ Δ ρ = ∀ i → Typ Δ (var (ρ i)) (rename ρ (lookup Γ i))

typed-renaming : ∀ {Γ : Context m} {Δ : Context n} {ρ t T}
  → TypedRen Γ Δ ρ → Typ Γ t T → Typ Δ (rename ρ t) (rename ρ T)
typed-renaming {Γ = Γ} {Δ} {ρ} {t} {T} h p =
  subst (λ q → Typ Δ q (rename ρ T)) (replace-renaming ρ t)
    (subst (Typ Δ _) (replace-renaming ρ T)
      (typed-replace (λ i → subst (Typ Δ (var (ρ i)))
        (sym (replace-renaming ρ (lookup Γ i))) (h i)) p))

typed-ren-lift : ∀ {Γ : Context m} {Δ : Context n} {ρ}
  → TypedRen Γ Δ ρ → (A : Term m)
  → TypedRen (extend Γ A) (extend Δ (rename ρ A)) (liftRenaming ρ)
typed-ren-lift {Γ = Γ} {Δ} {ρ} h A i = fin-cases
  (λ i → Typ (extend Δ (rename ρ A)) (var (liftRenaming ρ i))
    (rename (liftRenaming ρ) (lookup (extend Γ A) i))) i
  (subst (Typ (extend Δ (rename ρ A)) (var fzero))
    (sym (rename-shift ρ A)) (lookup-var fzero))
  (λ j → subst (Typ (extend Δ (rename ρ A)) (var (fsuc (ρ j))))
    (sym (rename-shift ρ (lookup Γ j))) (weakening (h j)))

typed-ren-shift : ∀ {Γ : Context n} {A} → TypedRen Γ (extend Γ A) fsuc
typed-ren-shift i = lookup-var (fsuc i)

typed-ren-id : ∀ {Γ : Context n} → TypedRen Γ Γ (λ i → i)
typed-ren-id {Γ = Γ} i = subst (Typ Γ (var i))
  (sym (rename-id (lookup Γ i))) (lookup-var i)

typed-identity : ∀ {Γ Δ : Context n} {t T}
  → (∀ i → Typ Δ (var i) (lookup Γ i)) → Typ Γ t T → Typ Δ t T
typed-identity {Γ = Γ} {Δ} {t} {T} h p =
  subst (λ q → Typ Δ q T) (replace-id t)
    (subst (Typ Δ _) (replace-id T)
      (typed-replace (λ i → subst (Typ Δ (var i))
        (sym (replace-id (lookup Γ i))) (h i)) p))
