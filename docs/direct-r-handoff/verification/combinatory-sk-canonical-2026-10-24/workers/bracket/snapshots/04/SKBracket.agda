{-# OPTIONS --cubical --safe --guardedness #-}
module SKBracket where

-- Deterministic beta-only bracket abstraction. The returned closed syntax
-- has only the existing S/K atoms, universe labels and binary application.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping using (Term; Typ; empty)
open import NativeAlgebra
open import BinderFreeBoundary using (decode; decode-rename; decode-replace)
import BinderFreeBoundary as Boundary
import BinderFreeCore as SK
open SK using (Ty; ι; _⇒_)
import SKSource as L
open L using (Con; ε; _▻_; Var; vz; vs; Source)

private
  variable
    n m : Nat
    A D E : Ty
    Γ Δ : Con

-- An endpoint equality only transports the certificate, never the calculus.
finish : ∀ {t u v : Term n} → u ≡ v → Steps t u → Steps t v
finish e p = subst (Steps _) e p

head-beta : (T : Term n) (b : Term (suc n)) (x : Term n)
  → Steps (app (lam T b) x) (substitute b x)
head-beta T b x = next beta done

k-head : (x : Term n)
  → Steps (app (Boundary.expand (SK.K {A} {D})) x)
      (lam (decode D) (shift x))
k-head {D = D} x = finish
  (cong (λ T → lam T (shift x)) (decode-replace (single x) D))
  (next beta done)

k-applied : (x y : Term n)
  → Steps (app (app (Boundary.expand (SK.K {A} {D})) x) y) x
k-applied {A = A} {D = D} x y = steps-trans
  (steps-app (k-head {A = A} {D = D} x) done)
  (finish (substitute-shift x y) (next beta done))

s-first : (f : Term n)
  → Steps (app (Boundary.expand (SK.S {A} {D} {E})) f)
      (lam (decode (A ⇒ D)) (lam (decode A)
        (app (app (shift (shift f)) (var fzero))
          (app (var (fsuc fzero)) (var fzero)))))
s-first {A = A} {D = D} f = finish
  (cong₂ lam (decode-replace (single f) (A ⇒ D))
    (cong (λ T → lam T
      (app (app (shift (shift f)) (var fzero))
        (app (var (fsuc fzero)) (var fzero))))
      (decode-replace (liftSubstitution (single f)) A)))
  (next beta done)

s-head : (f g : Term n)
  → Steps (app (app (Boundary.expand (SK.S {A} {D} {E})) f) g)
      (lam (decode A)
        (app (app (shift f) (var fzero)) (app (shift g) (var fzero))))
s-head {A = A} {D = D} {E = E} f g = steps-trans
  (steps-app (s-first {A = A} {D = D} {E = E} f) done)
  (finish
    (cong₂ lam (decode-replace (single g) A)
      (cong (λ h → app (app h (var fzero)) (app (shift g) (var fzero)))
        (replace-shift (single g) (shift f) ∙ cong shift (substitute-shift f g))))
    (next beta done))

s-applied : (f g x : Term n)
  → Steps (app (app (app (Boundary.expand (SK.S {A} {D} {E})) f) g) x)
      (app (app f x) (app g x))
s-applied {A = A} {D = D} {E = E} f g x = steps-trans
  (steps-app (s-head {A = A} {D = D} {E = E} f g) done)
  (finish (cong₂ app
    (cong (λ h → app h x) (substitute-shift f x))
    (cong (λ h → app h x) (substitute-shift g x))) (next beta done))

expand-rename : (ρ : Fin m → Fin n) (t : SK.Tm A)
  → rename ρ (Boundary.expand t) ≡ Boundary.expand t
expand-rename ρ (SK.S {A} {D} {E}) = cong₂ lam
  (decode-rename ρ (A ⇒ D ⇒ E))
  (cong₂ lam (decode-rename (liftRenaming ρ) (A ⇒ D))
    (cong (λ T → lam T (app (app (var (fsuc (fsuc fzero))) (var fzero))
      (app (var (fsuc fzero)) (var fzero))))
      (decode-rename (liftRenaming (liftRenaming ρ)) A)))
expand-rename ρ (SK.K {A} {D}) = cong₂ lam (decode-rename ρ A)
  (cong (λ T → lam T (var (fsuc fzero))) (decode-rename (liftRenaming ρ) D))
expand-rename ρ (SK.ground j) = refl
expand-rename ρ (f SK.· x) = cong₂ app (expand-rename ρ f) (expand-rename ρ x)

identity-applied : (x : Term n)
  → Steps (app (Boundary.expand (SK.identity {A})) x) x
identity-applied {A = A} x = steps-trans
  (s-applied {A = A} {D = A ⇒ A} {E = A}
    (Boundary.expand SK.K) (Boundary.expand SK.K) x)
  (k-applied {A = A} {D = A ⇒ A} x (app (Boundary.expand (SK.K {A} {A})) x))

identity-head : Steps (Boundary.expand {n} (SK.identity {A}))
  (lam (decode A) (var fzero))
identity-head {n = n} {A = A} = steps-trans
  (finish (cong (lam (decode A)) (cong₂ app
    (cong (λ f → app f (var fzero)) (expand-rename fsuc (SK.K {A} {A ⇒ A})))
    (cong (λ f → app f (var fzero)) (expand-rename fsuc (SK.K {A} {A})))))
    (s-head {A = A} {D = A ⇒ A} {E = A}
      (Boundary.expand SK.K) (Boundary.expand SK.K)))
  (steps-lam done
    (k-applied {A = A} {D = A ⇒ A} (var fzero)
      (app (Boundary.expand (SK.K {A} {A})) (var fzero))))

infixl 30 _·_
data Code (Γ : Con) : Ty → Set where
  s : Code Γ ((A ⇒ D ⇒ E) ⇒ (A ⇒ D) ⇒ A ⇒ E)
  k : Code Γ (A ⇒ D ⇒ A)
  label : Nat → Code Γ ι
  cv : Var Γ A → Code Γ A
  _·_ : Code Γ (A ⇒ D) → Code Γ A → Code Γ D

identity : Code Γ (A ⇒ A)
identity {A = A} = s {A = A} {D = A ⇒ A} {E = A} · k · k

bracket : Code (Γ ▻ A) D → Code Γ (A ⇒ D)
bracket s = k · s
bracket k = k · k
bracket (label n) = k · label n
bracket (cv vz) = identity
bracket (cv (vs x)) = k · cv x
bracket (f · x) = s · bracket f · bracket x

Env : Con → Nat → Set
Env Γ n = ∀ {A} → Var Γ A → Term n

eval : Code Γ A → Env Γ n → Term n
eval s ρ = Boundary.expand SK.S
eval k ρ = Boundary.expand SK.K
eval (label n) ρ = U n
eval (cv x) ρ = ρ x
eval (f · x) ρ = app (eval f ρ) (eval x ρ)

extendEnv : Env Γ n → Env (Γ ▻ A) (suc n)
extendEnv ρ vz = var fzero
extendEnv ρ (vs x) = shift (ρ x)

plugEnv : Env Γ n → Term n → Env (Γ ▻ A) n
plugEnv ρ a vz = a
plugEnv ρ a (vs x) = ρ x

eval-rename : (ren : Fin m → Fin n) (p : Code Γ A) (ρ : Env Γ m)
  → rename ren (eval p ρ) ≡ eval p (λ x → rename ren (ρ x))
eval-rename ren s ρ = expand-rename ren SK.S
eval-rename ren k ρ = expand-rename ren SK.K
eval-rename ren (label n) ρ = refl
eval-rename ren (cv x) ρ = refl
eval-rename ren (f · x) ρ = cong₂ app (eval-rename ren f ρ) (eval-rename ren x ρ)

abstract-applied : (p : Code (Γ ▻ A) D) (ρ : Env Γ n) (a : Term n)
  → Steps (app (eval (bracket p) ρ) a) (eval p (plugEnv ρ a))
abstract-applied s ρ a = k-applied (Boundary.expand SK.S) a
abstract-applied k ρ a = k-applied (Boundary.expand SK.K) a
abstract-applied (label j) ρ a = k-applied (U j) a
abstract-applied (cv vz) ρ a = identity-applied a
abstract-applied (cv (vs x)) ρ a = k-applied (ρ x) a
abstract-applied (f · x) ρ a = steps-trans
  (s-applied (eval (bracket f) ρ) (eval (bracket x) ρ) a)
  (steps-app (abstract-applied f ρ a) (abstract-applied x ρ a))

abstract-correct : (p : Code (Γ ▻ A) D) (ρ : Env Γ n)
  → Steps (eval (bracket p) ρ) (lam (decode A) (eval p (extendEnv ρ)))
abstract-correct s ρ = finish (cong (lam _) (expand-rename fsuc SK.S))
  (k-head (Boundary.expand SK.S))
abstract-correct k ρ = finish (cong (lam _) (expand-rename fsuc SK.K))
  (k-head (Boundary.expand SK.K))
abstract-correct (label j) ρ = k-head (U j)
abstract-correct (cv vz) ρ = identity-head
abstract-correct (cv (vs x)) ρ = k-head (ρ x)
abstract-correct {A = A} (f · x) ρ = steps-trans
  (finish (cong (lam (decode A)) (cong₂ app
    (cong (λ t → app t (var fzero)) (eval-rename fsuc (bracket f) ρ))
    (cong (λ t → app t (var fzero)) (eval-rename fsuc (bracket x) ρ))))
    (s-head (eval (bracket f) ρ) (eval (bracket x) ρ)))
  (steps-lam done (steps-app
    (abstract-applied f (λ x → shift (ρ x)) (var fzero))
    (abstract-applied x (λ x → shift (ρ x)) (var fzero))))
