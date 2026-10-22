{-# OPTIONS --cubical --safe --guardedness #-}
module NormalForms where

open import FiniteSyntax
open import BoundedReduction using (Normal; NotLambda; normal-isProp; notLambda-isProp)
open import FiniteCarriers using (AtMost; index; injective; Sized; sized-finite; closed-carrier-bound)
open import FiniteBounds using (capacity; tower; tetration; seed-bound)
open import Cubical.Foundations.Prelude using (isProp; isProp→PathP)
open import Cubical.Data.Nat.Order using (_≤_; isProp≤)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Data.Unit using (tt)

-- BEGINNORMALIIR
module _ (Label : Set) where
  data Nf (n : Nat) : Set
  data NonLamNf {n : Nat} : Nf n → Set
  erase : ∀ {n} → Nf n → Raw Label n

  data Nf n where
    nf-U   : Label → Nf n
    nf-var : Fin n → Nf n
    nf-pi nf-lam : Nf n → Nf (suc n) → Nf n
    nf-app : (f x : Nf n) → NonLamNf f → Nf n

  data NonLamNf {n} where
    non-lam : ∀ {f : Nf n} → NotLambda (erase f) → NonLamNf f

  erase (nf-U i) = U i
  erase (nf-var i) = var i
  erase (nf-pi A B) = pi (erase A) (erase B)
  erase (nf-lam A b) = lam (erase A) (erase b)
  erase (nf-app f x p) = app (erase f) (erase x)
-- ENDNORMALIIR

private
  variable
    Label : Set
    n : Nat

head-proof : ∀ {f : Nf Label n} → NonLamNf Label f → NotLambda (erase Label f)
head-proof (non-lam p) = p

head-isProp : ∀ {f : Nf Label n} → isProp (NonLamNf Label f)
head-isProp (non-lam p) (non-lam q) = cong non-lam (notLambda-isProp p q)

erase-normal : (t : Nf Label n) → Normal (erase Label t)
erase-normal (nf-U i) = tt
erase-normal (nf-var i) = tt
erase-normal (nf-pi A B) = erase-normal A , erase-normal B
erase-normal (nf-lam A b) = erase-normal A , erase-normal b
erase-normal (nf-app f x p) = erase-normal f , erase-normal x , head-proof p

mutual
  from-normal : (t : Raw Label n) → Normal t → Nf Label n
  from-normal (U i) p = nf-U i
  from-normal (var i) p = nf-var i
  from-normal (pi A B) (p , q) = nf-pi (from-normal A p) (from-normal B q)
  from-normal (lam A b) (p , q) = nf-lam (from-normal A p) (from-normal b q)
  from-normal (app f x) (p , q , h) = nf-app (from-normal f p) (from-normal x q)
    (non-lam (subst NotLambda (sym (erase-from-normal f p)) h))

  erase-from-normal : (t : Raw Label n) (p : Normal t)
    → erase Label (from-normal t p) ≡ t
  erase-from-normal (U i) p = refl
  erase-from-normal (var i) p = refl
  erase-from-normal (pi A B) (p , q) =
    cong₂ pi (erase-from-normal A p) (erase-from-normal B q)
  erase-from-normal (lam A b) (p , q) =
    cong₂ lam (erase-from-normal A p) (erase-from-normal b q)
  erase-from-normal (app f x) (p , q , h) =
    cong₂ app (erase-from-normal f p) (erase-from-normal x q)

private
  nf-app-path : {f f′ x x′ : Nf Label n} (p : f ≡ f′) (q : x ≡ x′)
    (h : NonLamNf Label f) (h′ : NonLamNf Label f′)
    → nf-app f x h ≡ nf-app f′ x′ h′
  nf-app-path p q h h′ i = nf-app (p i) (q i)
    (isProp→PathP (λ i → head-isProp {f = p i}) h h′ i)

from-erase : (t : Nf Label n) → from-normal (erase Label t) (erase-normal t) ≡ t
from-erase (nf-U i) = refl
from-erase (nf-var i) = refl
from-erase (nf-pi A B) = cong₂ nf-pi (from-erase A) (from-erase B)
from-erase (nf-lam A b) = cong₂ nf-lam (from-erase A) (from-erase b)
from-erase (nf-app f x p) = nf-app-path (from-erase f) (from-erase x) _ p

erase-injective : (t u : Nf Label n) → erase Label t ≡ erase Label u → t ≡ u
erase-injective t u p = sym (from-erase t) ∙
  cong (λ (v : Σ (Raw _ _) Normal) → from-normal (fst v) (snd v))
    (Σ≡Prop (λ _ → normal-isProp) p) ∙ from-erase u

-- BEGINNORMALFAMILY
SizedNf : (a n s : Nat) → Set
SizedNf a n s = Σ (Nf (Fin a) n) (λ t → nodes (erase (Fin a) t) ≤ s)

ExactNf : (a n N : Nat) → Set
ExactNf a n N = Σ (Nf (Fin a) n) (λ t → nodes (erase (Fin a) t) ≡ N)
-- ENDNORMALFAMILY

private
  erase-sized : ∀ {a n s} → SizedNf a n s → Sized a n s
  erase-sized {a} (t , p) = erase (Fin a) t , p

  lift-bound : ∀ {a n s k} → AtMost (Sized a n s) k → AtMost (SizedNf a n s) k
  lift-bound b .index t = index b (erase-sized t)
  lift-bound b .injective (t , p) (u , q) eq = Σ≡Prop (λ _ → isProp≤)
    (erase-injective t u (cong fst (injective b (erase-sized (t , p)) (erase-sized (u , q)) eq)))

normal-finite : (a n s : Nat) → AtMost (SizedNf a n s) (capacity a n s)
normal-finite a n s = lift-bound (sized-finite a n s)

-- BEGINNORMALBOUND
closed-normal-bound : (a d N : Nat) → a ≤ N
  → AtMost (SizedNf a 0 (tower d N)) (tetration (4 · N + 4) (d + 3))
closed-normal-bound a d N p = lift-bound (closed-carrier-bound a d N p)
-- ENDNORMALBOUND

-- BEGINEXACTNORMALBOUND
closed-exact-normal-bound : (a d N : Nat) → a ≤ N
  → AtMost (ExactNf a 0 N) (tetration (4 · N + 4) (d + 3))
closed-exact-normal-bound a d N p = exact-bound
  where
  include : ExactNf a 0 N → SizedNf a 0 (tower d N)
  include (t , eq) = t , subst (_≤ tower d N) (sym eq) (seed-bound d N)

  bound = closed-normal-bound a d N p

  exact-bound : AtMost (ExactNf a 0 N) (tetration (4 · N + 4) (d + 3))
  exact-bound .index t = index bound (include t)
  exact-bound .injective (t , eq) (u , eq′) h = Σ≡Prop (λ _ → isSetℕ _ _)
    (cong fst (injective bound (include (t , eq)) (include (u , eq′)) h))
-- ENDEXACTNORMALBOUND
