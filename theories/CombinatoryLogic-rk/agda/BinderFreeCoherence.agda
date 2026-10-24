{-# OPTIONS --cubical --safe --guardedness #-}
module BinderFreeCoherence where

-- The independent simply typed weak SK calculus admits a normal-form
-- algebra. These are combinatory equations, not native PTS beta equality.
open import BinderFreeCore
open import Cubical.Foundations.Prelude
  using (_≡_; refl; sym; cong; cong₂; _∙_; subst)
open import Cubical.Data.Sigma using (_,_; fst; snd)

private
  variable
    A D E : Ty

appNF : Nf (A ⇒ D) → Nf A → Nf D
appNF f x = fst (apply-normal f x)

appNF-evaluates : (f : Nf (A ⇒ D)) (x : Nf A) → f ∙ x ⇓ appNF f x
appNF-evaluates f x = fst (snd (apply-normal f x))

appNF-unique : ∀ {f : Nf (A ⇒ D)} {x : Nf A} {y : Nf D}
  → f ∙ x ⇓ y → appNF f x ≡ y
appNF-unique {f = f} {x = x} p =
  application-deterministic (appNF-evaluates f x) p

-- BEGINBINDERFREEALGEBRA
appNF-S : (f : Nf (A ⇒ D ⇒ E)) (g : Nf (A ⇒ D)) (x : Nf A)
  → appNF (appNF (appNF s0 f) g) x ≡ appNF (appNF f x) (appNF g x)
appNF-S f g x = appNF-unique
  (ap-s2 (appNF-evaluates f x) (appNF-evaluates g x)
    (appNF-evaluates (appNF f x) (appNF g x)))

appNF-K : (x : Nf A) (y : Nf D)
  → appNF (appNF k0 x) y ≡ x
appNF-K x y = refl

appNF-identity : (x : Nf A) → appNF identityNF x ≡ x
appNF-identity x = refl
-- ENDBINDERFREEALGEBRA

-- The algebraic fold exposes its homomorphism equation definitionally.
-- nf-is-normalize below proves it is exactly the certificate normalizer.
nf : Tm A → Nf A
nf S = s0
nf K = k0
nf (ground n) = lit n
nf (f · x) = appNF (nf f) (nf x)

private
  normal-app : (f : Tm (A ⇒ D)) (x : Tm A)
    → normal (normalize (f · x))
      ≡ appNF (normal (normalize f)) (normal (normalize x))
  normal-app f x with normalize f | normalize x
  ... | result fn pf | result xn px with apply-normal fn xn
  ... | y , p , py = refl

nf-is-normalize : (t : Tm A) → nf t ≡ normal (normalize t)
nf-is-normalize S = refl
nf-is-normalize K = refl
nf-is-normalize (ground n) = refl
nf-is-normalize (f · x) =
  cong₂ appNF (nf-is-normalize f) (nf-is-normalize x) ∙ sym (normal-app f x)

nf-erase : (n : Nf A) → nf (erase n) ≡ n
nf-erase n = nf-is-normalize (erase n) ∙ normalize-erase n

nf-sound : (t : Tm A) → t ↠ erase (nf t)
nf-sound t = subst (λ n → t ↠ erase n)
  (sym (nf-is-normalize t)) (sound (normalize t))

-- BEGINBINDERFREECOHERENCE
step-coherent : ∀ {t u : Tm A} → t ↝ u → nf t ≡ nf u
step-coherent (βS f g x) = appNF-S (nf f) (nf g) (nf x)
step-coherent (βK x y) = appNF-K (nf x) (nf y)
step-coherent (left {x = x} p) = cong (λ f → appNF f (nf x)) (step-coherent p)
step-coherent (right {f = f} p) = cong (appNF (nf f)) (step-coherent p)

steps-coherent : ∀ {t u : Tm A} → t ↠ u → nf t ≡ nf u
steps-coherent done = refl
steps-coherent (step p ps) = step-coherent p ∙ steps-coherent ps

data WeakConversion : Tm A → Tm A → Set where
  conv-refl : ∀ {t : Tm A} → WeakConversion t t
  conv-step : ∀ {t u : Tm A} → t ↝ u → WeakConversion t u
  conv-sym : ∀ {t u : Tm A} → WeakConversion t u → WeakConversion u t
  conv-trans : ∀ {t u v : Tm A}
    → WeakConversion t u → WeakConversion u v → WeakConversion t v

conversion-coherent : ∀ {t u : Tm A} → WeakConversion t u → nf t ≡ nf u
conversion-coherent conv-refl = refl
conversion-coherent (conv-step p) = step-coherent p
conversion-coherent (conv-sym p) = sym (conversion-coherent p)
conversion-coherent (conv-trans p q) = conversion-coherent p ∙ conversion-coherent q

steps-conversion : ∀ {t u : Tm A} → t ↠ u → WeakConversion t u
steps-conversion done = conv-refl
steps-conversion (step p ps) = conv-trans (conv-step p) (steps-conversion ps)

conversion-reflects : ∀ {t u : Tm A} → nf t ≡ nf u → WeakConversion t u
conversion-reflects {t = t} {u = u} p =
  conv-trans (steps-conversion (nf-sound t))
    (conv-trans (subst (WeakConversion (erase (nf t))) (cong erase p) conv-refl)
      (conv-sym (steps-conversion (nf-sound u))))
-- ENDBINDERFREECOHERENCE

normal-reduct-unique : ∀ {t : Tm A} {n : Nf A}
  → t ↠ erase n → nf t ≡ n
normal-reduct-unique {n = n} p = steps-coherent p ∙ nf-erase n
