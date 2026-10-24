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

private
  variable
    n m : Nat
    A D E : Ty

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
