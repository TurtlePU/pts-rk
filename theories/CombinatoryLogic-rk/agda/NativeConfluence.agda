{-# OPTIONS --cubical --safe --guardedness #-}
module NativeConfluence where

-- Parallel reduction proves Church--Rosser for the annotated native syntax.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction
open import NativeTyping
open import NativeAlgebra
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Unit using (Unit; tt)

private
  variable
    m n : Nat

data Par {n : Nat} : Term n → Term n → Set where
  par-refl : ∀ {t} → Par t t
  par-pi : ∀ {A A′ B B′} → Par A A′ → Par B B′ → Par (pi A B) (pi A′ B′)
  par-lam : ∀ {A A′ b b′} → Par A A′ → Par b b′ → Par (lam A b) (lam A′ b′)
  par-app : ∀ {f f′ y y′} → Par f f′ → Par y y′ → Par (app f y) (app f′ y′)
  par-beta : ∀ {A b b′ y y′} → Par b b′ → Par y y′
    → Par (app (lam A b) y) (substitute b′ y′)

par-rename : (ρ : Fin m → Fin n) {t u : Term m}
  → Par t u → Par (rename ρ t) (rename ρ u)
par-rename ρ par-refl = par-refl
par-rename ρ (par-pi p q) = par-pi (par-rename ρ p) (par-rename (liftRenaming ρ) q)
par-rename ρ (par-lam p q) = par-lam (par-rename ρ p) (par-rename (liftRenaming ρ) q)
par-rename ρ (par-app p q) = par-app (par-rename ρ p) (par-rename ρ q)
par-rename ρ (par-beta {A} {b} {b′} {y} {y′} p q) = subst
  (Par (app (lam (rename ρ A) (rename (liftRenaming ρ) b)) (rename ρ y)))
  (sym (rename-substitute ρ b′ y′))
  (par-beta (par-rename (liftRenaming ρ) p) (par-rename ρ q))

par-lift : {σ τ : Fin m → Term n}
  → (∀ i → Par (σ i) (τ i))
  → ∀ i → Par (liftSubstitution σ i) (liftSubstitution τ i)
par-lift {σ = σ} {τ} h i = caseFin-rel Par i
  (var fzero) (λ j → shift (σ j)) (var fzero) (λ j → shift (τ j))
  par-refl (λ j → par-rename fsuc (h j))

par-replace-refl : {σ τ : Fin m → Term n}
  → (∀ i → Par (σ i) (τ i)) → (t : Term m)
  → Par (replace σ t) (replace τ t)
par-replace-refl h (U i) = par-refl
par-replace-refl h (var i) = h i
par-replace-refl h (pi A B) = par-pi
  (par-replace-refl h A) (par-replace-refl (par-lift h) B)
par-replace-refl h (lam A b) = par-lam
  (par-replace-refl h A) (par-replace-refl (par-lift h) b)
par-replace-refl h (app f y) = par-app
  (par-replace-refl h f) (par-replace-refl h y)

par-replace : {σ τ : Fin m → Term n}
  → (∀ i → Par (σ i) (τ i)) → {t u : Term m}
  → Par t u → Par (replace σ t) (replace τ u)
par-replace h (par-refl {t}) = par-replace-refl h t
par-replace h (par-pi p q) = par-pi (par-replace h p) (par-replace (par-lift h) q)
par-replace h (par-lam p q) = par-lam (par-replace h p) (par-replace (par-lift h) q)
par-replace h (par-app p q) = par-app (par-replace h p) (par-replace h q)
par-replace {σ = σ} {τ} h (par-beta {A} {b} {b′} {y} {y′} p q) = subst
  (Par (app (lam (replace σ A) (replace (liftSubstitution σ) b)) (replace σ y)))
  (sym (replace-substitute τ b′ y′))
  (par-beta (par-replace (par-lift h) p) (par-replace h q))

par-substitute : {b b′ : Term (suc n)} {y y′ : Term n}
  → Par b b′ → Par y y′ → Par (substitute b y) (substitute b′ y′)
par-substitute {y = y} {y′} p q = par-replace
  (λ i → caseFin-rel Par i y var y′ var q (λ j → par-refl)) p

-- Complete development contracts only redexes already visible in the input.
develop : Term n → Term n
develop (U i) = U i
develop (var i) = var i
develop (pi A B) = pi (develop A) (develop B)
develop (lam A b) = lam (develop A) (develop b)
develop (app (lam A b) y) = substitute (develop b) (develop y)
develop (app (U i) y) = app (U i) (develop y)
develop (app (var i) y) = app (var i) (develop y)
develop (app (pi A B) y) = app (pi (develop A) (develop B)) (develop y)
develop (app (app f x) y) = app (develop (app f x)) (develop y)

par-develop : (t : Term n) → Par t (develop t)
par-develop (U i) = par-refl
par-develop (var i) = par-refl
par-develop (pi A B) = par-pi (par-develop A) (par-develop B)
par-develop (lam A b) = par-lam (par-develop A) (par-develop b)
par-develop (app (lam A b) y) = par-beta (par-develop b) (par-develop y)
par-develop (app (U i) y) = par-app par-refl (par-develop y)
par-develop (app (var i) y) = par-app par-refl (par-develop y)
par-develop (app (pi A B) y) = par-app
  (par-pi (par-develop A) (par-develop B)) (par-develop y)
par-develop (app (app f x) y) = par-app (par-develop (app f x)) (par-develop y)

IsLam : Term n → Set
IsLam (lam A b) = Unit
IsLam (U i) = ⊥
IsLam (var i) = ⊥
IsLam (pi A B) = ⊥
IsLam (app f y) = ⊥

lam-domain : Term n → Term n
lam-domain (lam A b) = A
lam-domain (U i) = U zero
lam-domain (var i) = U zero
lam-domain (pi A B) = U zero
lam-domain (app f y) = U zero

lam-body : Term n → Term (suc n)
lam-body (lam A b) = b
lam-body (U i) = U zero
lam-body (var i) = U zero
lam-body (pi A B) = U zero
lam-body (app f y) = U zero

lam-shape : (t : Term n) → IsLam t → t ≡ lam (lam-domain t) (lam-body t)
lam-shape (lam A b) h = refl
lam-shape (U i) h = rec h
lam-shape (var i) h = rec h
lam-shape (pi A B) h = rec h
lam-shape (app f y) h = rec h

par-lam-body : {t u : Term n} → Par t u → IsLam t
  → IsLam u × Par (lam-body t) (lam-body u)
par-lam-body par-refl h = h , par-refl
par-lam-body (par-lam p q) h = tt , q
par-lam-body (par-pi p q) h = rec h
par-lam-body (par-app p q) h = rec h
par-lam-body (par-beta p q) h = rec h

triangle : {t u : Term n} → Par t u → Par u (develop t)
triangle (par-refl {t}) = par-develop t
triangle (par-pi p q) = par-pi (triangle p) (triangle q)
triangle (par-lam p q) = par-lam (triangle p) (triangle q)
triangle (par-app {f = U i} p q) = par-app (triangle p) (triangle q)
triangle (par-app {f = var i} p q) = par-app (triangle p) (triangle q)
triangle (par-app {f = pi A B} p q) = par-app (triangle p) (triangle q)
triangle (par-app {f = app f x} p q) = par-app (triangle p) (triangle q)
triangle (par-app {f = lam A b} {f′} {y} {y′} p q) =
  subst (λ f → Par (app f y′) (substitute (develop b) (develop y)))
    (sym (lam-shape f′ (fst (par-lam-body p tt))))
    (par-beta (snd (par-lam-body (triangle p) (fst (par-lam-body p tt))))
      (triangle q))
triangle (par-beta p q) = par-substitute (triangle p) (triangle q)

data Pars {n : Nat} : Term n → Term n → Set where
  pars-done : ∀ {t} → Pars t t
  pars-next : ∀ {t u v} → Par t u → Pars u v → Pars t v

pars-trans : {t u v : Term n} → Pars t u → Pars u v → Pars t v
pars-trans pars-done q = q
pars-trans (pars-next p ps) q = pars-next p (pars-trans ps q)

par-strip : {t u v : Term n} → Par t u → Pars t v
  → Σ (Term n) (λ w → Pars u w × Par v w)
par-strip p pars-done = _ , pars-done , p
par-strip {t = t} p (pars-next q qs) with par-strip (triangle q) qs
... | w , ps , r = w , pars-next (triangle p) ps , r

pars-confluence : {t u v : Term n} → Pars t u → Pars t v
  → Σ (Term n) (λ w → Pars u w × Pars v w)
pars-confluence pars-done q = _ , q , pars-done
pars-confluence (pars-next p ps) q with par-strip p q
... | w , us , vw with pars-confluence ps us
... | z , uz , wz = z , uz , pars-next vw wz

step-par : {t u : Term n} → Step t u → Par t u
step-par (pi-left p) = par-pi (step-par p) par-refl
step-par (pi-right p) = par-pi par-refl (step-par p)
step-par (lam-left p) = par-lam (step-par p) par-refl
step-par (lam-right p) = par-lam par-refl (step-par p)
step-par (app-left p) = par-app (step-par p) par-refl
step-par (app-right p) = par-app par-refl (step-par p)
step-par beta = par-beta par-refl par-refl

steps-pars : {t u : Term n} → Steps t u → Pars t u
steps-pars done = pars-done
steps-pars (next p ps) = pars-next (step-par p) (steps-pars ps)

par-steps : {t u : Term n} → Par t u → Steps t u
par-steps par-refl = done
par-steps (par-pi p q) = steps-pi (par-steps p) (par-steps q)
par-steps (par-lam p q) = steps-lam (par-steps p) (par-steps q)
par-steps (par-app p q) = steps-app (par-steps p) (par-steps q)
par-steps (par-beta p q) = steps-trans
  (steps-app (steps-lam done (par-steps p)) (par-steps q)) (next beta done)

pars-steps : {t u : Term n} → Pars t u → Steps t u
pars-steps pars-done = done
pars-steps (pars-next p ps) = steps-trans (par-steps p) (pars-steps ps)

steps-confluence : {t u v : Term n} → Steps t u → Steps t v
  → Σ (Term n) (λ w → Steps u w × Steps v w)
steps-confluence p q with pars-confluence (steps-pars p) (steps-pars q)
... | w , p′ , q′ = w , pars-steps p′ , pars-steps q′

beta-common-reduct : {t u : Term n} → Beta t u
  → Σ (Term n) (λ w → Steps t w × Steps u w)
beta-common-reduct beta-refl = _ , done , done
beta-common-reduct (beta-step p) = _ , next p done , done
beta-common-reduct (beta-sym p) with beta-common-reduct p
... | w , p′ , q′ = w , q′ , p′
beta-common-reduct (beta-trans p q) with beta-common-reduct p | beta-common-reduct q
... | x , tx , ux | y , uy , vy with steps-confluence ux uy
... | z , xz , yz = z , steps-trans tx xz , steps-trans vy yz

steps-beta : {t u : Term n} → Steps t u → Beta t u
steps-beta done = beta-refl
steps-beta (next p ps) = beta-trans (beta-step p) (steps-beta ps)

common-reduct-beta : {t u w : Term n} → Steps t w → Steps u w → Beta t u
common-reduct-beta p q = beta-trans (steps-beta p) (beta-sym (steps-beta q))

normal-steps-identity : {t u : Term n} → Normal t → Steps t u → t ≡ u
normal-steps-identity h done = refl
normal-steps-identity h (next s p) = rec (normal-sound h s)

normal-beta-unique : {t u : Term n} → Normal t → Normal u → Beta t u → t ≡ u
normal-beta-unique ht hu e with beta-common-reduct e
... | w , p , q = normal-steps-identity ht p ∙ sym (normal-steps-identity hu q)

sort-label : Term n → Nat
sort-label (U i) = i
sort-label (var i) = zero
sort-label (pi A B) = zero
sort-label (lam A b) = zero
sort-label (app f y) = zero

sort-injective : {i j : Nat} → Beta {n} (U i) (U j) → i ≡ j
sort-injective e = cong sort-label (normal-beta-unique tt tt e)

IsPi : Term n → Set
IsPi (pi A B) = Unit
IsPi (U i) = ⊥
IsPi (var i) = ⊥
IsPi (lam A b) = ⊥
IsPi (app f y) = ⊥

pi-domain : Term n → Term n
pi-domain (pi A B) = A
pi-domain (U i) = U zero
pi-domain (var i) = U zero
pi-domain (lam A b) = U zero
pi-domain (app f y) = U zero

pi-body : Term n → Term (suc n)
pi-body (pi A B) = B
pi-body (U i) = U zero
pi-body (var i) = U zero
pi-body (lam A b) = U zero
pi-body (app f y) = U zero

step-pi-parts : {t u : Term n} → Step t u → IsPi t
  → IsPi u × (Steps (pi-domain t) (pi-domain u) × Steps (pi-body t) (pi-body u))
step-pi-parts (pi-left p) h = tt , next p done , done
step-pi-parts (pi-right p) h = tt , done , next p done
step-pi-parts (lam-left p) h = rec h
step-pi-parts (lam-right p) h = rec h
step-pi-parts (app-left p) h = rec h
step-pi-parts (app-right p) h = rec h
step-pi-parts beta h = rec h

steps-pi-parts : {t u : Term n} → Steps t u → IsPi t
  → IsPi u × (Steps (pi-domain t) (pi-domain u) × Steps (pi-body t) (pi-body u))
steps-pi-parts done h = h , done , done
steps-pi-parts (next p ps) h with step-pi-parts p h
... | hu , dp , bp with steps-pi-parts ps hu
... | hv , dps , bps = hv , steps-trans dp dps , steps-trans bp bps

pi-injective : {A A′ : Term n} {B B′ : Term (suc n)}
  → Beta (pi A B) (pi A′ B′) → Beta A A′ × Beta B B′
pi-injective e with beta-common-reduct e
... | w , p , q with steps-pi-parts p tt | steps-pi-parts q tt
... | hp , dp , bp | hq , dq , bq =
  common-reduct-beta dp dq , common-reduct-beta bp bq

-- Conversion to a normal representative is realized by forward reduction.
beta-to-normal : {t u : Term n} → Beta t u → Normal u → Steps t u
beta-to-normal e hu with beta-common-reduct e
... | w , p , q = subst (Steps _) (sym (normal-steps-identity hu q)) p

sort-not-pi : {i : Nat} {A : Term n} {B : Term (suc n)}
  → Beta (U i) (pi A B) → ⊥
sort-not-pi e with beta-common-reduct e
... | w , p , q = subst IsPi (sym (normal-steps-identity tt p))
  (fst (steps-pi-parts q tt))

-- Two deterministic computations of convertible sources agree whenever
-- both results are normal; this does not assume either computation terminates.
normal-results-coherent : {t u v w : Term n}
  → Beta t u → Steps t v → Steps u w → Normal v → Normal w → v ≡ w
normal-results-coherent e p q hv hw = normal-beta-unique hv hw
  (beta-trans (beta-sym (steps-beta p)) (beta-trans e (steps-beta q)))
