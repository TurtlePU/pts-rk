{-# OPTIONS --cubical --safe --guardedness #-}
module NativeRankPreservation where

-- The rank bound holds at every beta intermediate, not only after a pass.
open import PTSPrelude
open import NativeTyping
open import NativeInversion
open import NativeConfluence
open import NativePreservation
open import NativeRanks
open import NativeSafety
open import BoundedReduction
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; <-weaken)

step-exposed-lambda-rank : ∀ {n Γ} {t u : Term n} {r}
  → Step t u → WellFormed Γ → TypeRank Γ t r
  → NotLambda t → IsLambda u
  → Σ Nat (λ s → RedexRank Γ t s × (r ≤ s))
step-exposed-lambda-rank (pi-left p) wf hr hn ()
step-exposed-lambda-rank (pi-right p) wf hr hn ()
step-exposed-lambda-rank (lam-left p) wf hr () hl
step-exposed-lambda-rank (lam-right p) wf hr () hl
step-exposed-lambda-rank (app-left p) wf hr hn ()
step-exposed-lambda-rank (app-right p) wf hr hn ()
step-exposed-lambda-rank beta wf hr@(T , ht , hT) hn hl with app-inversion ht
... | A , B , hf , hy , e with type-correct wf hf
... | s , hp = s , at-beta hf hp , application-rank-le-function wf hr (_ , hf , hp)

private
  changed-head-bound : ∀ {n Γ} {f f′ T : Term n} {d}
    → Step f f′ → WellFormed Γ → Typ Γ f T → RankSafe Γ f d
    → (IsLambda f → ∀ r → TypeRank Γ f r → r ≤ d)
    → IsLambda f′ → ∀ r → TypeRank Γ f′ r → r ≤ d
  changed-head-bound {f = f} p wf hf sf bound hl r hr with typing-type-rank wf hf
  ... | q , hq with lambda-view f
  ... | inl hλ = subst (_≤ _) (type-rank-unique wf
    (type-rank-reduction wf hq (next p done)) hr) (bound hλ q hq)
  ... | inr hn with step-exposed-lambda-rank p wf hq hn hl
  ... | s , hs , le = subst (_≤ _) (type-rank-unique wf
    (type-rank-reduction wf hq (next p done)) hr)
    (≤-trans le (safe-to-bound sf s hs))

step-rank-safe : ∀ {n Γ} {t u T : Term n} {d}
  → Step t u → WellFormed Γ → Typ Γ t T → RankSafe Γ t d → RankSafe Γ u d
step-rank-safe (pi-left p) wf ht hs with pi-inversion ht
... | a , b , ha , hb , e = step-rank-safe p wf ha (fst hs) ,
  safe-context-last-reduction wf ha (next p done) hb (snd hs)
step-rank-safe (pi-right p) wf ht hs with pi-inversion ht
... | a , b , ha , hb , e = fst hs , step-rank-safe p (wf-extend wf ha) hb (snd hs)
step-rank-safe (lam-left p) wf ht hs with lam-inversion ht
... | a , B , ha , hb , e = step-rank-safe p wf ha (fst hs) ,
  safe-context-last-reduction wf ha (next p done) hb (snd hs)
step-rank-safe (lam-right p) wf ht hs with lam-inversion ht
... | a , B , ha , hb , e = fst hs , step-rank-safe p (wf-extend wf ha) hb (snd hs)
step-rank-safe (app-left p) wf ht hs with app-inversion ht
... | A , B , hf , hy , e = step-rank-safe p wf hf (fst hs) ,
  fst (snd hs) , changed-head-bound p wf hf (fst hs) (snd (snd hs))
step-rank-safe (app-right p) wf ht hs with app-inversion ht
... | A , B , hf , hy , e = fst hs ,
  step-rank-safe p wf hy (fst (snd hs)) , snd (snd hs)
step-rank-safe (beta {b = b} {u = y}) wf ht hs with app-inversion ht
... | A , B , hf , hy , e with type-correct wf hf
... | r , hp with application-argument-rank wf hf hy (_ , hf , hp)
... | a , ha , lt with lam-inversion hf
... | c , C , hD , hb , ec with pi-injective ec
... | eA , eB = safe-monotone (substitute b y)
  (safe-substitution wf (wf-extend wf hD)
    (conversion hy hD (beta-sym eA)) hb ha (fst (snd hs)) (snd (fst hs)))
  (max-least ≤-refl (≤-trans (<-weaken lt) (snd (snd hs) tt r (_ , hf , hp))))

step-preserves-rank-bound : ∀ {n Γ} {t u T : Term n} {d}
  → WellFormed Γ → Typ Γ t T → RedexBound Γ t d → Step t u
  → RedexBound Γ u d
step-preserves-rank-bound {t = t} wf ht bound p = safe-to-bound
  (step-rank-safe p wf ht (bound-to-safe t wf ht bound))

reduction-preserves-rank-bound : ∀ {n Γ} {t u T : Term n} {d}
  → WellFormed Γ → Typ Γ t T → RedexBound Γ t d → Steps t u
  → RedexBound Γ u d
reduction-preserves-rank-bound wf ht bound done = bound
reduction-preserves-rank-bound wf ht bound (next p ps) =
  reduction-preserves-rank-bound wf (subject-reduction wf ht p)
    (step-preserves-rank-bound wf ht bound p) ps
