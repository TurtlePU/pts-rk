{-# OPTIONS --cubical --safe --guardedness #-}
module NativeAlgebra where

-- Binder-aware algebra of the original annotated terms.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction
open import NativeTyping using (Term; Beta; beta-refl; beta-step; beta-sym; beta-trans)
open import Cubical.Data.Unit using (Unit; tt)

private
  variable
    a : Set
    l m n : Nat

-- Dependent case analysis, with the index generalized before matching.
FinCases : (n : Nat) → (P : Fin n → Set) → Fin n → Set
FinCases zero P i = Unit
FinCases (suc n) P i = P fzero → (∀ j → P (fsuc j)) → P i

fin-cases : ∀ {n} (P : Fin n → Set) (i : Fin n) → FinCases n P i
fin-cases P fzero z s = z
fin-cases P (fsuc i) z s = s i

rename-cong : (ρ τ : Fin m → Fin n) → (∀ i → ρ i ≡ τ i)
  → (t : Raw a m) → rename ρ t ≡ rename τ t
rename-cong ρ τ h (U i) = refl
rename-cong ρ τ h (var i) = cong var (h i)
rename-cong ρ τ h (pi A B) = cong₂ pi (rename-cong ρ τ h A)
  (rename-cong (liftRenaming ρ) (liftRenaming τ)
    (λ i → caseFin-rel _≡_ i fzero (λ j → fsuc (ρ j))
      fzero (λ j → fsuc (τ j)) refl (λ j → cong fsuc (h j))) B)
rename-cong ρ τ h (lam A b) = cong₂ lam (rename-cong ρ τ h A)
  (rename-cong (liftRenaming ρ) (liftRenaming τ)
    (λ i → caseFin-rel _≡_ i fzero (λ j → fsuc (ρ j))
      fzero (λ j → fsuc (τ j)) refl (λ j → cong fsuc (h j))) b)
rename-cong ρ τ h (app f y) = cong₂ app (rename-cong ρ τ h f) (rename-cong ρ τ h y)

replace-cong : (σ τ : Fin m → Raw a n) → (∀ i → σ i ≡ τ i)
  → (t : Raw a m) → replace σ t ≡ replace τ t
replace-cong σ τ h (U i) = refl
replace-cong σ τ h (var i) = h i
replace-cong σ τ h (pi A B) = cong₂ pi (replace-cong σ τ h A)
  (replace-cong (liftSubstitution σ) (liftSubstitution τ)
    (λ i → caseFin-rel _≡_ i (var fzero) (λ j → shift (σ j))
      (var fzero) (λ j → shift (τ j)) refl (λ j → cong shift (h j))) B)
replace-cong σ τ h (lam A b) = cong₂ lam (replace-cong σ τ h A)
  (replace-cong (liftSubstitution σ) (liftSubstitution τ)
    (λ i → caseFin-rel _≡_ i (var fzero) (λ j → shift (σ j))
      (var fzero) (λ j → shift (τ j)) refl (λ j → cong shift (h j))) b)
replace-cong σ τ h (app f y) = cong₂ app (replace-cong σ τ h f) (replace-cong σ τ h y)

rename-compose : (ρ : Fin l → Fin m) (τ : Fin m → Fin n)
  (t : Raw a l) → rename τ (rename ρ t) ≡ rename (λ i → τ (ρ i)) t
rename-compose ρ τ (U i) = refl
rename-compose ρ τ (var i) = refl
rename-compose ρ τ (pi A B) = cong₂ pi (rename-compose ρ τ A)
  (rename-compose (liftRenaming ρ) (liftRenaming τ) B ∙
   rename-cong _ _ (λ i → fin-cases (λ i → liftRenaming τ (liftRenaming ρ i)
     ≡ liftRenaming (λ j → τ (ρ j)) i) i refl (λ j → refl)) B)
rename-compose ρ τ (lam A b) = cong₂ lam (rename-compose ρ τ A)
  (rename-compose (liftRenaming ρ) (liftRenaming τ) b ∙
   rename-cong _ _ (λ i → fin-cases (λ i → liftRenaming τ (liftRenaming ρ i)
     ≡ liftRenaming (λ j → τ (ρ j)) i) i refl (λ j → refl)) b)
rename-compose ρ τ (app f y) = cong₂ app (rename-compose ρ τ f) (rename-compose ρ τ y)

rename-id : (t : Raw a n) → rename (λ i → i) t ≡ t
rename-id (U i) = refl
rename-id (var i) = refl
rename-id (pi A B) = cong₂ pi (rename-id A)
  (rename-cong _ _ (λ i → fin-cases (λ i → liftRenaming (λ j → j) i ≡ i)
    i refl (λ j → refl)) B ∙ rename-id B)
rename-id (lam A b) = cong₂ lam (rename-id A)
  (rename-cong _ _ (λ i → fin-cases (λ i → liftRenaming (λ j → j) i ≡ i)
    i refl (λ j → refl)) b ∙ rename-id b)
rename-id (app f y) = cong₂ app (rename-id f) (rename-id y)

rename-shift : (ρ : Fin m → Fin n) (t : Raw a m)
  → rename (liftRenaming ρ) (shift t) ≡ shift (rename ρ t)
rename-shift ρ t = rename-compose fsuc (liftRenaming ρ) t
  ∙ sym (rename-compose ρ fsuc t)

replace-rename : (ρ : Fin l → Fin m) (σ : Fin m → Raw a n)
  (t : Raw a l) → replace σ (rename ρ t) ≡ replace (λ i → σ (ρ i)) t
replace-rename ρ σ (U i) = refl
replace-rename ρ σ (var i) = refl
replace-rename ρ σ (pi A B) = cong₂ pi (replace-rename ρ σ A)
  (replace-rename (liftRenaming ρ) (liftSubstitution σ) B ∙
   replace-cong _ _ (λ i → fin-cases (λ i → liftSubstitution σ (liftRenaming ρ i)
     ≡ liftSubstitution (λ j → σ (ρ j)) i) i refl (λ j → refl)) B)
replace-rename ρ σ (lam A b) = cong₂ lam (replace-rename ρ σ A)
  (replace-rename (liftRenaming ρ) (liftSubstitution σ) b ∙
   replace-cong _ _ (λ i → fin-cases (λ i → liftSubstitution σ (liftRenaming ρ i)
     ≡ liftSubstitution (λ j → σ (ρ j)) i) i refl (λ j → refl)) b)
replace-rename ρ σ (app f y) = cong₂ app (replace-rename ρ σ f) (replace-rename ρ σ y)

rename-replace : (σ : Fin l → Raw a m) (ρ : Fin m → Fin n)
  (t : Raw a l) → rename ρ (replace σ t) ≡ replace (λ i → rename ρ (σ i)) t
rename-replace σ ρ (U i) = refl
rename-replace σ ρ (var i) = refl
rename-replace σ ρ (pi A B) = cong₂ pi (rename-replace σ ρ A)
  (rename-replace (liftSubstitution σ) (liftRenaming ρ) B ∙
   replace-cong _ _ (λ i → fin-cases (λ i → rename (liftRenaming ρ) (liftSubstitution σ i)
     ≡ liftSubstitution (λ j → rename ρ (σ j)) i)
     i refl (λ j → rename-shift ρ (σ j))) B)
rename-replace σ ρ (lam A b) = cong₂ lam (rename-replace σ ρ A)
  (rename-replace (liftSubstitution σ) (liftRenaming ρ) b ∙
   replace-cong _ _ (λ i → fin-cases (λ i → rename (liftRenaming ρ) (liftSubstitution σ i)
     ≡ liftSubstitution (λ j → rename ρ (σ j)) i)
     i refl (λ j → rename-shift ρ (σ j))) b)
rename-replace σ ρ (app f y) = cong₂ app (rename-replace σ ρ f) (rename-replace σ ρ y)

replace-shift : (σ : Fin m → Raw a n) (t : Raw a m)
  → replace (liftSubstitution σ) (shift t) ≡ shift (replace σ t)
replace-shift σ t = replace-rename fsuc (liftSubstitution σ) t
  ∙ sym (rename-replace σ fsuc t)

replace-compose : (σ : Fin l → Raw a m) (τ : Fin m → Raw a n)
  (t : Raw a l) → replace τ (replace σ t) ≡ replace (λ i → replace τ (σ i)) t
replace-compose σ τ (U i) = refl
replace-compose σ τ (var i) = refl
replace-compose σ τ (pi A B) = cong₂ pi (replace-compose σ τ A)
  (replace-compose (liftSubstitution σ) (liftSubstitution τ) B ∙
   replace-cong _ _ (λ i → fin-cases (λ i → replace (liftSubstitution τ) (liftSubstitution σ i)
     ≡ liftSubstitution (λ j → replace τ (σ j)) i)
     i refl (λ j → replace-shift τ (σ j))) B)
replace-compose σ τ (lam A b) = cong₂ lam (replace-compose σ τ A)
  (replace-compose (liftSubstitution σ) (liftSubstitution τ) b ∙
   replace-cong _ _ (λ i → fin-cases (λ i → replace (liftSubstitution τ) (liftSubstitution σ i)
     ≡ liftSubstitution (λ j → replace τ (σ j)) i)
     i refl (λ j → replace-shift τ (σ j))) b)
replace-compose σ τ (app f y) = cong₂ app (replace-compose σ τ f) (replace-compose σ τ y)

replace-id : (t : Raw a n) → replace var t ≡ t
replace-id (U i) = refl
replace-id (var i) = refl
replace-id (pi A B) = cong₂ pi (replace-id A)
  (replace-cong _ var (λ i → fin-cases (λ i → liftSubstitution var i ≡ var i)
    i refl (λ j → refl)) B ∙ replace-id B)
replace-id (lam A b) = cong₂ lam (replace-id A)
  (replace-cong _ var (λ i → fin-cases (λ i → liftSubstitution var i ≡ var i)
    i refl (λ j → refl)) b ∙ replace-id b)
replace-id (app f y) = cong₂ app (replace-id f) (replace-id y)

substitute-shift : (t u : Raw a n) → substitute (shift t) u ≡ t
substitute-shift t u = replace-rename fsuc (single u) t ∙ replace-id t

rename-substitute : (ρ : Fin m → Fin n) (b : Raw a (suc m)) (u : Raw a m)
  → rename ρ (substitute b u) ≡ substitute (rename (liftRenaming ρ) b) (rename ρ u)
rename-substitute ρ b u = rename-replace (single u) ρ b
  ∙ replace-cong _ _ (λ i → fin-cases
    (λ i → rename ρ (single u i) ≡ single (rename ρ u) (liftRenaming ρ i))
    i refl (λ j → refl)) b
  ∙ sym (replace-rename (liftRenaming ρ) (single (rename ρ u)) b)

replace-substitute : (σ : Fin m → Raw a n) (b : Raw a (suc m)) (u : Raw a m)
  → replace σ (substitute b u) ≡ substitute (replace (liftSubstitution σ) b) (replace σ u)
replace-substitute σ b u = replace-compose (single u) σ b
  ∙ replace-cong _ _ (λ i → fin-cases
    (λ i → replace σ (single u i) ≡ substitute (liftSubstitution σ i) (replace σ u))
    i refl (λ j → sym (substitute-shift (σ j) (replace σ u)))) b
  ∙ sym (replace-compose (liftSubstitution σ) (single (replace σ u)) b)

step-rename : (ρ : Fin m → Fin n) {t u : Raw a m}
  → Step t u → Step (rename ρ t) (rename ρ u)
step-rename ρ (pi-left s) = pi-left (step-rename ρ s)
step-rename ρ (pi-right s) = pi-right (step-rename (liftRenaming ρ) s)
step-rename ρ (lam-left s) = lam-left (step-rename ρ s)
step-rename ρ (lam-right s) = lam-right (step-rename (liftRenaming ρ) s)
step-rename ρ (app-left s) = app-left (step-rename ρ s)
step-rename ρ (app-right s) = app-right (step-rename ρ s)
step-rename ρ (beta {A} {b} {u}) = subst
  (Step (app (lam (rename ρ A) (rename (liftRenaming ρ) b)) (rename ρ u)))
  (sym (rename-substitute ρ b u)) beta

step-replace : (σ : Fin m → Raw a n) {t u : Raw a m}
  → Step t u → Step (replace σ t) (replace σ u)
step-replace σ (pi-left s) = pi-left (step-replace σ s)
step-replace σ (pi-right s) = pi-right (step-replace (liftSubstitution σ) s)
step-replace σ (lam-left s) = lam-left (step-replace σ s)
step-replace σ (lam-right s) = lam-right (step-replace (liftSubstitution σ) s)
step-replace σ (app-left s) = app-left (step-replace σ s)
step-replace σ (app-right s) = app-right (step-replace σ s)
step-replace σ (beta {A} {b} {u}) = subst
  (Step (app (lam (replace σ A) (replace (liftSubstitution σ) b)) (replace σ u)))
  (sym (replace-substitute σ b u)) beta

beta-rename : (ρ : Fin m → Fin n) {t u : Term m}
  → Beta t u → Beta (rename ρ t) (rename ρ u)
beta-rename ρ beta-refl = beta-refl
beta-rename ρ (beta-step s) = beta-step (step-rename ρ s)
beta-rename ρ (beta-sym p) = beta-sym (beta-rename ρ p)
beta-rename ρ (beta-trans p q) = beta-trans (beta-rename ρ p) (beta-rename ρ q)

beta-replace : (σ : Fin m → Term n) {t u : Term m}
  → Beta t u → Beta (replace σ t) (replace σ u)
beta-replace σ beta-refl = beta-refl
beta-replace σ (beta-step s) = beta-step (step-replace σ s)
beta-replace σ (beta-sym p) = beta-sym (beta-replace σ p)
beta-replace σ (beta-trans p q) = beta-trans (beta-replace σ p) (beta-replace σ q)

beta-map : (F : Term m → Term n)
  → (∀ {t u} → Step t u → Step (F t) (F u))
  → ∀ {t u} → Beta t u → Beta (F t) (F u)
beta-map F h beta-refl = beta-refl
beta-map F h (beta-step s) = beta-step (h s)
beta-map F h (beta-sym p) = beta-sym (beta-map F h p)
beta-map F h (beta-trans p q) = beta-trans (beta-map F h p) (beta-map F h q)

beta-pi : ∀ {A A′ : Term n} {B B′ : Term (suc n)}
  → Beta A A′ → Beta B B′ → Beta (pi A B) (pi A′ B′)
beta-pi {A′ = A′} {B = B} p q = beta-trans
  (beta-map (λ A → pi A B) pi-left p) (beta-map (pi A′) pi-right q)

beta-lam : ∀ {A A′ : Term n} {b b′ : Term (suc n)}
  → Beta A A′ → Beta b b′ → Beta (lam A b) (lam A′ b′)
beta-lam {A′ = A′} {b = b} p q = beta-trans
  (beta-map (λ A → lam A b) lam-left p) (beta-map (lam A′) lam-right q)

beta-app : ∀ {f f′ y y′ : Term n}
  → Beta f f′ → Beta y y′ → Beta (app f y) (app f′ y′)
beta-app {f′ = f′} {y = y} p q = beta-trans
  (beta-map (λ f → app f y) app-left p) (beta-map (app f′) app-right q)

beta-replace-images : (σ τ : Fin m → Term n) → (∀ i → Beta (σ i) (τ i))
  → (t : Term m) → Beta (replace σ t) (replace τ t)
beta-replace-images σ τ h (U i) = beta-refl
beta-replace-images σ τ h (var i) = h i
beta-replace-images σ τ h (pi A B) = beta-pi (beta-replace-images σ τ h A)
  (beta-replace-images (liftSubstitution σ) (liftSubstitution τ)
    (λ i → fin-cases (λ i → Beta (liftSubstitution σ i) (liftSubstitution τ i))
      i beta-refl (λ j → beta-rename fsuc (h j))) B)
beta-replace-images σ τ h (lam A b) = beta-lam (beta-replace-images σ τ h A)
  (beta-replace-images (liftSubstitution σ) (liftSubstitution τ)
    (λ i → fin-cases (λ i → Beta (liftSubstitution σ i) (liftSubstitution τ i))
      i beta-refl (λ j → beta-rename fsuc (h j))) b)
beta-replace-images σ τ h (app f y) = beta-app
  (beta-replace-images σ τ h f) (beta-replace-images σ τ h y)

beta-substitute-argument : (b : Term (suc n)) {u v : Term n}
  → Beta u v → Beta (substitute b u) (substitute b v)
beta-substitute-argument b {u} {v} p = beta-replace-images (single u) (single v)
  (λ i → fin-cases (λ i → Beta (single u i) (single v i)) i p (λ j → beta-refl)) b

replace-renaming : (ρ : Fin m → Fin n) (t : Raw a m)
  → replace (λ i → var (ρ i)) t ≡ rename ρ t
replace-renaming ρ t = sym (replace-rename ρ var t) ∙ replace-id (rename ρ t)
