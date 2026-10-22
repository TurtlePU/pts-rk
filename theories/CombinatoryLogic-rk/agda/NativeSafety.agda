{-# OPTIONS --cubical --safe --guardedness #-}
module NativeSafety where

-- A structural view of the original semantic occurrence bound.
open import PTSPrelude
open import NativeTyping
open import NativeRanks
open import NativeAlgebra
open import NativeSubstitution
open import NativeInversion
open import NativePreservation
open import NativeConfluence using (steps-beta)
open import BoundedReduction
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans)

RankSafe : ∀ {n} → Context n → Term n → Nat → Set
RankSafe Γ (U i) d = Unit
RankSafe Γ (var i) d = Unit
RankSafe Γ (pi A B) d = RankSafe Γ A d × RankSafe (extend Γ A) B d
RankSafe Γ (lam A b) d = RankSafe Γ A d × RankSafe (extend Γ A) b d
RankSafe Γ (app f y) d = RankSafe Γ f d × (RankSafe Γ y d ×
  (IsLambda f → ∀ r → TypeRank Γ f r → r ≤ d))

safe-to-bound : ∀ {n Γ} {t : Term n} {d}
  → RankSafe Γ t d → RedexBound Γ t d
safe-to-bound h r (at-beta hf hp) = snd (snd h) tt r (_ , hf , hp)
safe-to-bound h r (in-pi-left hr) = safe-to-bound (fst h) r hr
safe-to-bound h r (in-pi-right hr) = safe-to-bound (snd h) r hr
safe-to-bound h r (in-lam-left hr) = safe-to-bound (fst h) r hr
safe-to-bound h r (in-lam-right hr) = safe-to-bound (snd h) r hr
safe-to-bound h r (in-app-left hr) = safe-to-bound (fst h) r hr
safe-to-bound h r (in-app-right hr) = safe-to-bound (fst (snd h)) r hr

safe-monotone : ∀ {n Γ} (t : Term n) {a b}
  → RankSafe Γ t a → a ≤ b → RankSafe Γ t b
safe-monotone (U i) h p = tt
safe-monotone (var i) h p = tt
safe-monotone (pi A B) h p = safe-monotone A (fst h) p , safe-monotone B (snd h) p
safe-monotone (lam A b) h p = safe-monotone A (fst h) p , safe-monotone b (snd h) p
safe-monotone (app f y) h p = safe-monotone f (fst h) p
  , safe-monotone y (fst (snd h)) p
  , λ hl r hr → ≤-trans (snd (snd h) hl r hr) p

normal-rank-safe : ∀ {n Γ} (t : Term n) d → Normal t → RankSafe Γ t d
normal-rank-safe (U i) d h = tt
normal-rank-safe (var i) d h = tt
normal-rank-safe (pi A B) d h = normal-rank-safe A d (fst h)
  , normal-rank-safe B d (snd h)
normal-rank-safe (lam A b) d h = normal-rank-safe A d (fst h)
  , normal-rank-safe b d (snd h)
normal-rank-safe (app f y) d h = normal-rank-safe f d (fst h)
  , normal-rank-safe y d (fst (snd h))
  , λ hl r hr → Empty.rec (lambda-contradiction hl (snd (snd h)))

-- For originally typed terms the structural and occurrence bounds agree.
bound-to-safe : ∀ {n Γ} (t : Term n) {T d}
  → WellFormed Γ → Typ Γ t T → RedexBound Γ t d → RankSafe Γ t d
bound-to-safe (U i) wf ht bound = tt
bound-to-safe (var i) wf ht bound = tt
bound-to-safe (pi A B) wf ht bound with pi-inversion ht
... | a , b , ha , hb , e =
  bound-to-safe A wf ha (λ r hr → bound r (in-pi-left hr)) ,
  bound-to-safe B (wf-extend wf ha) hb (λ r hr → bound r (in-pi-right hr))
bound-to-safe (lam A b) wf ht bound with lam-inversion ht
... | a , B , ha , hb , e =
  bound-to-safe A wf ha (λ r hr → bound r (in-lam-left hr)) ,
  bound-to-safe b (wf-extend wf ha) hb (λ r hr → bound r (in-lam-right hr))
bound-to-safe (app f y) wf ht bound with app-inversion ht
... | A , B , hf , hy , e with type-correct wf hf
... | s , hp =
  bound-to-safe f wf hf (λ r hr → bound r (in-app-left hr)) ,
  bound-to-safe y wf hy (λ r hr → bound r (in-app-right hr)) ,
  λ hl r hr → subst (_≤ _) (sym (type-rank-unique wf hr (_ , hf , hp)))
    (bound s (lambda-redex hl hf hp))

lambda-rename-reflect : ∀ {m n} (ρ : Fin m → Fin n) (t : Term m)
  → IsLambda (rename ρ t) → IsLambda t
lambda-rename-reflect ρ (U i) ()
lambda-rename-reflect ρ (var i) ()
lambda-rename-reflect ρ (pi A B) ()
lambda-rename-reflect ρ (lam A b) h = tt
lambda-rename-reflect ρ (app f y) ()

safe-rename : ∀ {m Γ} (t : Term m) {T} {n : Nat} {Δ : Context n} {ρ d}
  → WellFormed Γ → WellFormed Δ → Typ Γ t T → TypedRen Γ Δ ρ
  → RankSafe Γ t d → RankSafe Δ (rename ρ t) d
safe-rename (U i) wf wf′ ht hρ hs = tt
safe-rename (var i) wf wf′ ht hρ hs = tt
safe-rename {Γ = Γ} (pi A B) {Δ = Δ} wf wf′ ht hρ hs with pi-inversion ht
... | a , b , ha , hb , e =
  safe-rename A wf wf′ ha hρ (fst hs) ,
  safe-rename B (wf-extend wf ha) (wf-extend wf′ (typed-renaming hρ ha))
    hb (typed-ren-lift {Γ = Γ} {Δ} hρ A) (snd hs)
safe-rename {Γ = Γ} (lam A b) {Δ = Δ} wf wf′ ht hρ hs with lam-inversion ht
... | a , B , ha , hb , e =
  safe-rename A wf wf′ ha hρ (fst hs) ,
  safe-rename b (wf-extend wf ha) (wf-extend wf′ (typed-renaming hρ ha))
    hb (typed-ren-lift {Γ = Γ} {Δ} hρ A) (snd hs)
safe-rename (app f y) {ρ = ρ} wf wf′ ht hρ hs with app-inversion ht
... | A , B , hf , hy , e =
  safe-rename f wf wf′ hf hρ (fst hs) ,
  safe-rename y wf wf′ hy hρ (fst (snd hs)) ,
  λ hl r hr → snd (snd hs) (lambda-rename-reflect ρ f hl) r
    (type-rank-rename-reflect wf wf′ hρ hf hr)

safe-shift : ∀ {n Γ} {t T A : Term n} {d a}
  → WellFormed Γ → Typ Γ t T → Typ Γ A (U a) → RankSafe Γ t d
  → RankSafe (extend Γ A) (shift t) d
safe-shift {t = t} wf ht ha hs =
  safe-rename t wf (wf-extend wf ha) ht typed-ren-shift hs

SafeImages : ∀ {m n} → Context n → (Fin m → Term n) → Nat → Set
SafeImages Δ σ d = ∀ i → RankSafe Δ (σ i) d ×
  (IsLambda (σ i) → ∀ r → TypeRank Δ (σ i) r → r ≤ d)

safe-images-lift : ∀ {m n} {Γ : Context m} {Δ : Context n} {σ} {A : Term m} {d a}
  → WellFormed Δ → TypedSub Γ Δ σ → Typ Δ (replace σ A) (U a)
  → SafeImages Δ σ d → SafeImages (extend Δ (replace σ A)) (liftSubstitution σ) d
safe-images-lift {Γ = Γ} {Δ} {σ} {A} {d} wf hσ ha hi i = fin-cases
  (λ i → RankSafe (extend Δ (replace σ A)) (liftSubstitution σ i) d ×
    (IsLambda (liftSubstitution σ i) → ∀ r →
      TypeRank (extend Δ (replace σ A)) (liftSubstitution σ i) r → r ≤ d)) i
  (tt , λ ())
  (λ j → safe-shift wf (hσ j) ha (fst (hi j)) ,
    λ hl r hr → snd (hi j) (lambda-rename-reflect fsuc (σ j) hl) r
      (type-rank-rename-reflect wf (wf-extend wf ha) typed-ren-shift (hσ j) hr))

-- A replacement creates a lambda head only from an old lambda or a variable.
replacement-head-safe : ∀ {m Γ} (f : Term m) {T} {n : Nat} {Δ : Context n} {σ d}
  → WellFormed Γ → WellFormed Δ → Typ Γ f T → TypedSub Γ Δ σ
  → SafeImages Δ σ d → (IsLambda f → ∀ r → TypeRank Γ f r → r ≤ d)
  → IsLambda (replace σ f) → ∀ r → TypeRank Δ (replace σ f) r → r ≤ d
replacement-head-safe (U i) wf wf′ ht hσ hi hh () r hr
replacement-head-safe (var i) wf wf′ ht hσ hi hh hl r hr = snd (hi i) hl r hr
replacement-head-safe (pi A B) wf wf′ ht hσ hi hh () r hr
replacement-head-safe (lam A b) wf wf′ ht hσ hi hh hl r hr =
  hh tt r (type-rank-replace-reflect wf wf′ hσ ht hr)
replacement-head-safe (app f y) wf wf′ ht hσ hi hh () r hr

safe-replace : ∀ {m Γ} (t : Term m) {T} {n : Nat} {Δ : Context n} {σ d}
  → WellFormed Γ → WellFormed Δ → Typ Γ t T → TypedSub Γ Δ σ
  → SafeImages Δ σ d → RankSafe Γ t d → RankSafe Δ (replace σ t) d
safe-replace (U i) wf wf′ ht hσ hi hs = tt
safe-replace (var i) wf wf′ ht hσ hi hs = fst (hi i)
safe-replace {Γ = Γ} (pi A B) {Δ = Δ} wf wf′ ht hσ hi hs with pi-inversion ht
... | a , b , ha , hb , e =
  safe-replace A wf wf′ ha hσ hi (fst hs) ,
  safe-replace B (wf-extend wf ha) (wf-extend wf′ (typed-replace hσ ha))
    hb (typed-lift {Γ = Γ} {Δ} hσ A)
    (safe-images-lift {Γ = Γ} {A = A} wf′ hσ (typed-replace hσ ha) hi) (snd hs)
safe-replace {Γ = Γ} (lam A b) {Δ = Δ} wf wf′ ht hσ hi hs with lam-inversion ht
... | a , B , ha , hb , e =
  safe-replace A wf wf′ ha hσ hi (fst hs) ,
  safe-replace b (wf-extend wf ha) (wf-extend wf′ (typed-replace hσ ha))
    hb (typed-lift {Γ = Γ} {Δ} hσ A)
    (safe-images-lift {Γ = Γ} {A = A} wf′ hσ (typed-replace hσ ha) hi) (snd hs)
safe-replace (app f y) wf wf′ ht hσ hi hs with app-inversion ht
... | A , B , hf , hy , e =
  safe-replace f wf wf′ hf hσ hi (fst hs) ,
  safe-replace y wf wf′ hy hσ hi (fst (snd hs)) ,
  replacement-head-safe f wf wf′ hf hσ hi (snd (snd hs))

safe-single-images : ∀ {n Γ} {u : Term n} {a d}
  → WellFormed Γ → TypeRank Γ u a → RankSafe Γ u d
  → SafeImages Γ (single u) (max d a)
safe-single-images {Γ = Γ} {u} {a} {d} wf hr hs i = fin-cases
  (λ i → RankSafe Γ (single u i) (max d a) ×
    (IsLambda (single u i) → ∀ r → TypeRank Γ (single u i) r → r ≤ max d a)) i
  (safe-monotone u hs (max-left d a) ,
    λ hl r hr′ → subst (_≤ max d a) (type-rank-unique wf hr hr′) (max-right d a))
  (λ j → tt , λ ())

safe-substitution : ∀ {n Γ} {u U : Term n} {t T : Term (suc n)} {d a}
  → WellFormed Γ → WellFormed (extend Γ U)
  → Typ Γ u U → Typ (extend Γ U) t T → TypeRank Γ u a
  → RankSafe Γ u d → RankSafe (extend Γ U) t d
  → RankSafe Γ (substitute t u) (max d a)
safe-substitution {t = t} {d = d} {a} wf wfU hu ht hr hsu hst =
  safe-replace t wfU wf ht (single-typed hu) (safe-single-images wf hr hsu)
    (safe-monotone t hst (max-left d a))

redex-bound-substitution : ∀ {n Γ} {u U : Term n} {t T : Term (suc n)} {d a}
  → WellFormed Γ → WellFormed (extend Γ U)
  → Typ Γ u U → Typ (extend Γ U) t T → TypeRank Γ u a
  → RedexBound Γ u d → RedexBound (extend Γ U) t d
  → RedexBound Γ (substitute t u) (max d a)
redex-bound-substitution {u = u} {t = t} wf wfU hu ht hr hbu hbt =
  safe-to-bound (safe-substitution wf wfU hu ht hr
    (bound-to-safe u wf hu hbu) (bound-to-safe t wfU ht hbt))

safe-context-last-reduction : ∀ {n Γ} {A A′ : Term n} {t T : Term (suc n)} {d a}
  → WellFormed Γ → Typ Γ A (U a) → Steps A A′
  → Typ (extend Γ A) t T → RankSafe (extend Γ A) t d
  → RankSafe (extend Γ A′) t d
safe-context-last-reduction {Γ = Γ} {A} {A′} {t} {d = d} wf ha p ht hs =
  subst (λ v → RankSafe (extend Γ A′) v d) (rename-id t)
    (safe-rename t (wf-extend wf ha) (wf-extend wf (subject-reductions wf ha p)) ht
      (λ i → subst (Typ (extend Γ A′) (var i))
        (sym (rename-id (lookup (extend Γ A) i)))
        (context-last-images ha (steps-beta p) i)) hs)
