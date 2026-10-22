{-# OPTIONS --cubical --safe --guardedness #-}
module NativeDescent where

-- Every bottom-up pass lowers the original semantic redex-rank bound.
-- Neither normality nor preservation is assumed as an input certificate.
open import PTSPrelude
open import NativeTyping
open import NativeInversion
open import NativeConfluence
open import NativePreservation
open import NativeRanks
open import NativeSafety
open import BoundedReduction
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Nat.Order
  using (_≤_; ≤-refl; ≤-trans; pred-≤-pred)

private
  contract-safe-bound : ∀ {n Γ} (f y : Term n) {A B d}
    → WellFormed Γ → Typ Γ f (pi A B) → Typ Γ y A
    → RankSafe Γ f d → RankSafe Γ y d
    → (IsLambda f → ∀ r → TypeRank Γ f r → r ≤ suc d)
    → RankSafe Γ (contract f y) d
  contract-safe-bound (U i) y wf hf hy sf sy bound = sf , sy , λ ()
  contract-safe-bound (var i) y wf hf hy sf sy bound = sf , sy , λ ()
  contract-safe-bound (pi A B) y wf hf hy sf sy bound = sf , sy , λ ()
  contract-safe-bound (app f z) y wf hf hy sf sy bound = sf , sy , λ ()
  contract-safe-bound (lam A b) y wf hf hy sf sy bound with type-correct wf hf
  ... | r , hp with application-argument-rank wf hf hy (_ , hf , hp)
  ... | q , hq , lt with lam-inversion hf
  ... | a , B , ha , hb , e with pi-injective e
  ... | eA , eB = safe-monotone (substitute b y)
    (safe-substitution wf (wf-extend wf ha)
      (conversion hy ha (beta-sym eA)) hb hq sy (snd sf))
    (max-least ≤-refl (pred-≤-pred (≤-trans lt (bound tt r (_ , hf , hp)))))

greedy-safe-descent : ∀ {n Γ} (t : Term n) {T d}
  → WellFormed Γ → Typ Γ t T → RankSafe Γ t (suc d)
  → RankSafe Γ (greedy t) d
greedy-safe-descent (U i) wf ht safe = tt
greedy-safe-descent (var i) wf ht safe = tt
greedy-safe-descent (pi A B) wf ht safe with pi-inversion ht
... | a , b , ha , hb , e = greedy-safe-descent A wf ha (fst safe) ,
  safe-context-last-reduction wf ha (greedy-sound A)
    (greedy-typed (wf-extend wf ha) hb)
    (greedy-safe-descent B (wf-extend wf ha) hb (snd safe))
greedy-safe-descent (lam A b) wf ht safe with lam-inversion ht
... | a , B , ha , hb , e = greedy-safe-descent A wf ha (fst safe) ,
  safe-context-last-reduction wf ha (greedy-sound A)
    (greedy-typed (wf-extend wf ha) hb)
    (greedy-safe-descent b (wf-extend wf ha) hb (snd safe))
greedy-safe-descent (app f y) wf ht safe with app-inversion ht
... | A , B , hf , hy , e =
  contract-safe-bound (greedy f) (greedy y) wf
    (greedy-typed wf hf) (greedy-typed wf hy)
    (greedy-safe-descent f wf hf (fst safe))
    (greedy-safe-descent y wf hy (fst (snd safe)))
    (λ hl r hr → greedy-contracted-head-bound wf ht (safe-to-bound safe) hl hr)

greedy-strict-descent : ∀ {n Γ} {t T : Term n} {d}
  → WellFormed Γ → Typ Γ t T → RedexBound Γ t (suc d)
  → RedexBound Γ (greedy t) d
greedy-strict-descent {t = t} wf ht bound = safe-to-bound
  (greedy-safe-descent t wf ht (bound-to-safe t wf ht bound))

-- BEGIN NATIVEDESCENT
bounded-rounds-normal : ∀ {n Γ} (d : Nat) {t T : Term n}
  → WellFormed Γ → Typ Γ t T → RedexBound Γ t d
  → Normal (rounds d t)
bounded-rounds-normal zero {t = t} wf ht bound = zero-bound-normal t wf ht bound
bounded-rounds-normal (suc d) wf ht bound = bounded-rounds-normal d wf
  (greedy-typed wf ht) (greedy-strict-descent wf ht bound)
-- END NATIVEDESCENT

-- Normal arguments have no internal redexes, including in annotations.
normal-application-rank-bound : ∀ {n Γ} {f y : Term n} {r}
  → WellFormed Γ → Normal f → Normal y → TypeRank Γ f r
  → RedexBound Γ (app f y) r
normal-application-rank-bound {f = f} {y = y} {r = r} wf nf ny hr =
  safe-to-bound (normal-rank-safe f r nf , normal-rank-safe y r ny ,
    λ hl s hs → subst (_≤ r) (sym (type-rank-unique wf hs hr)) ≤-refl)

normal-application-normalizes : ∀ {n Γ} {f y A : Term n} {B d}
  → WellFormed Γ → Typ Γ f (pi A B) → Typ Γ y A
  → Typ Γ (pi A B) (U d) → Normal f → Normal y
  → Normal (rounds d (app f y))
normal-application-normalizes wf hf hy hp nf ny = bounded-rounds-normal _ wf
  (application hf hy) (normal-application-rank-bound wf nf ny (_ , hf , hp))
