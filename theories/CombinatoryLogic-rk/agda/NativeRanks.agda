{-# OPTIONS --cubical --safe --guardedness #-}
module NativeRanks where

-- Semantic ranks use the original typing judgment and include annotations.
open import PTSPrelude
open import NativeTyping
open import NativeInversion
open import NativeConfluence
open import NativeSubstitution
open import NativePreservation
open import BoundedReduction
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat.Order
  using (_≤_; _<_; ≤-refl; ≤-trans; zero-≤; suc-≤-suc; pred-≤-pred;
         ¬-<-zero; <-weaken)

TypeRank : ∀ {n} → Context n → Term n → Nat → Set
TypeRank Γ t r = Σ _ (λ T → Typ Γ t T × Typ Γ T (U r))

IsLambda : ∀ {a n} → Raw a n → Set
IsLambda (lam A b) = Unit
IsLambda (U i) = ⊥
IsLambda (var i) = ⊥
IsLambda (pi A B) = ⊥
IsLambda (app f y) = ⊥

lambda-contradiction : ∀ {a n} {t : Raw a n} → IsLambda t → NotLambda t → ⊥
lambda-contradiction {t = lam A b} p q = q
lambda-contradiction {t = U i} p q = p
lambda-contradiction {t = var i} p q = p
lambda-contradiction {t = pi A B} p q = p
lambda-contradiction {t = app f y} p q = p

max-left : (a b : Nat) → a ≤ max a b
max-left zero b = zero-≤
max-left (suc a) zero = ≤-refl
max-left (suc a) (suc b) = suc-≤-suc (max-left a b)

max-right : (a b : Nat) → b ≤ max a b
max-right zero b = ≤-refl
max-right (suc a) zero = zero-≤
max-right (suc a) (suc b) = suc-≤-suc (max-right a b)

max-least : ∀ {a b c} → a ≤ c → b ≤ c → max a b ≤ c
max-least {zero} p q = q
max-least {suc a} {zero} p q = p
max-least {suc a} {suc b} {zero} p q = Empty.rec
  (Cubical.Data.Nat.Order.¬-<-zero p)
max-least {suc a} {suc b} {suc c} p q =
  suc-≤-suc (max-least (pred-≤-pred p) (pred-≤-pred q))

redex-bound-monotone : ∀ {n Γ} {t : Term n} {a b}
  → RedexBound Γ t a → a ≤ b → RedexBound Γ t b
redex-bound-monotone h p r hr = ≤-trans (h r hr) p

normal-no-redex : ∀ {n Γ} {t : Term n} {r}
  → Normal t → RedexRank Γ t r → ⊥
normal-no-redex h (at-beta ht hp) = snd (snd h)
normal-no-redex h (in-pi-left r) = normal-no-redex (fst h) r
normal-no-redex h (in-pi-right r) = normal-no-redex (snd h) r
normal-no-redex h (in-lam-left r) = normal-no-redex (fst h) r
normal-no-redex h (in-lam-right r) = normal-no-redex (snd h) r
normal-no-redex h (in-app-left r) = normal-no-redex (fst h) r
normal-no-redex h (in-app-right r) = normal-no-redex (fst (snd h)) r

normal-redex-bound : ∀ {n Γ} {t : Term n} d → Normal t → RedexBound Γ t d
normal-redex-bound d h r hr = Empty.rec (normal-no-redex h hr)

sort-rank-unique : ∀ {n Γ} {T : Term n} {r s}
  → Typ Γ T (U r) → Typ Γ T (U s) → r ≡ s
sort-rank-unique h k = sort-injective (uniqueness h k)

convertible-sort-rank : ∀ {n Γ} {T V : Term n} {r s}
  → WellFormed Γ → Typ Γ T (U r) → Typ Γ V (U s)
  → Beta T V → r ≡ s
convertible-sort-rank wf h k e = sort-injective (type-stability wf h k e)

type-rank-unique : ∀ {n Γ} {t : Term n} {r s}
  → WellFormed Γ → TypeRank Γ t r → TypeRank Γ t s → r ≡ s
type-rank-unique wf (T , h , ht) (V , k , hv) =
  convertible-sort-rank wf ht hv (uniqueness h k)

type-rank-conversion : ∀ {n Γ} {t u : Term n} {r s}
  → WellFormed Γ → TypeRank Γ t r → TypeRank Γ u s → Beta t u → r ≡ s
type-rank-conversion wf (T , h , ht) (V , k , hv) e =
  convertible-sort-rank wf ht hv (type-stability wf h k e)

product-rank-components : ∀ {n Γ} {A : Term n} {B r}
  → Typ Γ (pi A B) (U r)
  → Σ Nat (λ a → Σ Nat (λ b → Typ Γ A (U a) ×
      (Typ (extend Γ A) B (U b) × ((r ≡ max (suc a) b) ×
      ((a < r) × (b ≤ r))))))
product-rank-components h with pi-inversion h
... | a , b , ha , hb , e = a , b , ha , hb , sym p ,
  subst (suc a ≤_) p (max-left (suc a) b) ,
  subst (b ≤_) p (max-right (suc a) b)
  where p = sort-injective e

typing-type-rank : ∀ {n Γ} {t T : Term n}
  → WellFormed Γ → Typ Γ t T → Σ Nat (TypeRank Γ t)
typing-type-rank {T = T} wf h with type-correct wf h
... | r , hr = r , T , h , hr

type-rank-reduction : ∀ {n Γ} {t u : Term n} {r}
  → WellFormed Γ → TypeRank Γ t r → Steps t u → TypeRank Γ u r
type-rank-reduction wf (T , h , ht) p = T , subject-reductions wf h p , ht

type-rank-greedy : ∀ {n Γ} {t : Term n} {r}
  → WellFormed Γ → TypeRank Γ t r → TypeRank Γ (greedy t) r
type-rank-greedy {t = t} wf h = type-rank-reduction wf h (greedy-sound t)

application-argument-rank : ∀ {n Γ} {f y A : Term n} {B r}
  → WellFormed Γ → Typ Γ f (pi A B) → Typ Γ y A → TypeRank Γ f r
  → Σ Nat (λ a → TypeRank Γ y a × (a < r))
application-argument-rank {A = A} wf hf hy hr with type-correct wf hf
... | s , hp with product-rank-components hp
... | a , b , ha , hb , eq , lt , le = a , (A , hy , ha) ,
  subst (a <_) (sym (type-rank-unique wf hr (_ , hf , hp))) lt

application-result-rank : ∀ {n Γ} {f y A : Term n} {B r}
  → WellFormed Γ → Typ Γ f (pi A B) → Typ Γ y A → TypeRank Γ f r
  → Σ Nat (λ b → TypeRank Γ (app f y) b × (b ≤ r))
application-result-rank {B = B} wf hf hy hr with type-correct wf hf
... | s , hp with product-rank-components hp
... | a , b , ha , hb , eq , lt , le = b ,
  (substitute B _ , application hf hy , substitution hb hy) ,
  subst (b ≤_) (sym (type-rank-unique wf hr (_ , hf , hp))) le

application-rank-le-function : ∀ {n Γ} {f y : Term n} {r s}
  → WellFormed Γ → TypeRank Γ (app f y) r → TypeRank Γ f s → r ≤ s
application-rank-le-function wf hr@(T , h , ht) hs with app-inversion h
... | A , B , hf , hy , e with application-result-rank wf hf hy hs
... | b , hb , le = subst (_≤ _) (sym (type-rank-unique wf hr hb)) le

redex-rank-positive : ∀ {n Γ} {t : Term n} {r} → RedexRank Γ t r → zero < r
redex-rank-positive (at-beta hf hp) with product-rank-components hp
... | a , b , ha , hb , eq , lt , le = ≤-trans (suc-≤-suc zero-≤) lt
redex-rank-positive (in-pi-left h) = redex-rank-positive h
redex-rank-positive (in-pi-right h) = redex-rank-positive h
redex-rank-positive (in-lam-left h) = redex-rank-positive h
redex-rank-positive (in-lam-right h) = redex-rank-positive h
redex-rank-positive (in-app-left h) = redex-rank-positive h
redex-rank-positive (in-app-right h) = redex-rank-positive h

lambda-redex : ∀ {n Γ} {f y A : Term n} {B r}
  → IsLambda f → Typ Γ f (pi A B) → Typ Γ (pi A B) (U r)
  → RedexRank Γ (app f y) r
lambda-redex {f = lam A b} hl hf hp = at-beta hf hp
lambda-redex {f = U i} () hf hp
lambda-redex {f = var i} () hf hp
lambda-redex {f = pi A B} () hf hp
lambda-redex {f = app f y} () hf hp

lambda-view : ∀ {a n} (t : Raw a n) → IsLambda t ⊎ NotLambda t
lambda-view (lam A b) = inl tt
lambda-view (U i) = inr tt
lambda-view (var i) = inr tt
lambda-view (pi A B) = inr tt
lambda-view (app f y) = inr tt

contract-lambda-head : ∀ {n} (f y : Term n) → IsLambda (contract f y) → IsLambda f
contract-lambda-head (lam A b) y h = tt
contract-lambda-head (U i) y ()
contract-lambda-head (var i) y ()
contract-lambda-head (pi A B) y ()
contract-lambda-head (app f z) y ()

exposed-lambda-rank : ∀ {n Γ} (t : Term n) {r}
  → WellFormed Γ → TypeRank Γ t r → NotLambda t → IsLambda (greedy t)
  → Σ Nat (λ s → RedexRank Γ t s × (r ≤ s))
exposed-lambda-rank (U i) wf hr hn ()
exposed-lambda-rank (var i) wf hr hn ()
exposed-lambda-rank (pi A B) wf hr hn ()
exposed-lambda-rank (lam A b) wf hr () hl
exposed-lambda-rank (app f y) wf hr@(T , h , ht) hn hl with app-inversion h
... | A , B , hf , hy , e with type-correct wf hf
... | s , hp with lambda-view f
... | inl hfλ = s , lambda-redex hfλ hf hp ,
  application-rank-le-function wf hr (_ , hf , hp)
... | inr hfn with exposed-lambda-rank f wf (_ , hf , hp) hfn
  (contract-lambda-head (greedy f) (greedy y) hl)
... | q , hq , le = q , in-app-left hq ,
  ≤-trans (application-rank-le-function wf hr (_ , hf , hp)) le

greedy-contracted-head-bound : ∀ {n Γ} {f y T : Term n} {d r}
  → WellFormed Γ → Typ Γ (app f y) T → RedexBound Γ (app f y) d
  → IsLambda (greedy f) → TypeRank Γ (greedy f) r → r ≤ d
greedy-contracted-head-bound {f = f} wf h bound hl hr with app-inversion h
... | A , B , hf , hy , e with type-correct wf hf
... | s , hp with lambda-view f
... | inl hλ = subst (_≤ _) (type-rank-unique wf
  (type-rank-greedy wf (_ , hf , hp)) hr) (bound s (lambda-redex hλ hf hp))
... | inr hn with exposed-lambda-rank f wf (_ , hf , hp) hn hl
... | q , hq , le = subst (_≤ _) (type-rank-unique wf
  (type-rank-greedy wf (_ , hf , hp)) hr)
  (≤-trans le (bound q (in-app-left hq)))

zero-bound-head : ∀ {n Γ} {f y A : Term n} {B r}
  → Typ Γ f (pi A B) → Typ Γ (pi A B) (U r)
  → RedexBound Γ (app f y) zero → NotLambda f
zero-bound-head {f = U i} hf hp bound = tt
zero-bound-head {f = var i} hf hp bound = tt
zero-bound-head {f = pi A B} hf hp bound = tt
zero-bound-head {f = app f y} hf hp bound = tt
zero-bound-head {f = lam A b} {y = y} hf hp bound = ¬-<-zero
  (≤-trans (redex-rank-positive (at-beta {y = y} hf hp)) (bound _ (at-beta hf hp)))

zero-bound-normal : ∀ {n Γ} (t : Term n) {T}
  → WellFormed Γ → Typ Γ t T → RedexBound Γ t zero → Normal t
zero-bound-normal (U i) wf ht bound = tt
zero-bound-normal (var i) wf ht bound = tt
zero-bound-normal (pi A B) wf ht bound with pi-inversion ht
... | a , b , ha , hb , e =
  zero-bound-normal A wf ha (λ r hr → bound r (in-pi-left hr)) ,
  zero-bound-normal B (wf-extend wf ha) hb (λ r hr → bound r (in-pi-right hr))
zero-bound-normal (lam A b) wf ht bound with lam-inversion ht
... | a , B , ha , hb , e =
  zero-bound-normal A wf ha (λ r hr → bound r (in-lam-left hr)) ,
  zero-bound-normal b (wf-extend wf ha) hb (λ r hr → bound r (in-lam-right hr))
zero-bound-normal (app f y) wf ht bound with app-inversion ht
... | A , B , hf , hy , e with type-correct wf hf
... | r , hp =
  zero-bound-normal f wf hf (λ s hr → bound s (in-app-left hr)) ,
  zero-bound-normal y wf hy (λ s hr → bound s (in-app-right hr)) ,
  zero-bound-head hf hp bound

type-rank-replace : ∀ {m n Γ Δ σ} {t : Term m} {r}
  → TypedSub Γ Δ σ → TypeRank Γ t r → TypeRank {n} Δ (replace σ t) r
type-rank-replace {σ = σ} h (T , ht , hT) = replace σ T ,
  typed-replace h ht , typed-replace h hT

type-rank-rename : ∀ {m n Γ Δ ρ} {t : Term m} {r}
  → TypedRen Γ Δ ρ → TypeRank Γ t r → TypeRank {n} Δ (rename ρ t) r
type-rank-rename {ρ = ρ} h (T , ht , hT) = rename ρ T ,
  typed-renaming h ht , typed-renaming h hT

type-rank-replace-reflect : ∀ {m n Γ Δ σ} {t T : Term m} {r}
  → WellFormed Γ → WellFormed Δ → TypedSub Γ Δ σ → Typ Γ t T
  → TypeRank {n} Δ (replace σ t) r → TypeRank Γ t r
type-rank-replace-reflect wf wf′ h ht hr with typing-type-rank wf ht
... | q , hq = subst (TypeRank _ _) (type-rank-unique wf′
  (type-rank-replace h hq) hr) hq

type-rank-rename-reflect : ∀ {m n Γ Δ ρ} {t T : Term m} {r}
  → WellFormed Γ → WellFormed Δ → TypedRen Γ Δ ρ → Typ Γ t T
  → TypeRank {n} Δ (rename ρ t) r → TypeRank Γ t r
type-rank-rename-reflect wf wf′ h ht hr with typing-type-rank wf ht
... | q , hq = subst (TypeRank _ _) (type-rank-unique wf′
  (type-rank-rename h hq) hr) hq
