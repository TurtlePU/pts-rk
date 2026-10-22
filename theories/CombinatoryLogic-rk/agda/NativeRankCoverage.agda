{-# OPTIONS --cubical --safe --guardedness #-}
module NativeRankCoverage where

-- Every original typing derivation supplies a finite semantic redex bound.
-- The bound is computed from the whole annotated syntax, not its outer type.
open import PTSPrelude
open import FiniteSyntax
open import NativeTyping
open import NativeRanks
open import NativeSafety
open import NativeInversion
open import NativeNormalization
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans)

safe-coverage : ∀ {n Γ} (t : Term n) {T}
  → WellFormed Γ → Typ Γ t T → Σ Nat (RankSafe Γ t)
safe-coverage (U i) wf ht = zero , tt
safe-coverage (var i) wf ht = zero , tt
safe-coverage (pi A B) wf ht with pi-inversion ht
... | a , b , ha , hb , eq with safe-coverage A wf ha
  | safe-coverage B (wf-extend wf ha) hb
... | d , hA | e , hB = max d e ,
  safe-monotone A hA (max-left d e) , safe-monotone B hB (max-right d e)
safe-coverage (lam A b) wf ht with lam-inversion ht
... | a , B , ha , hb , eq with safe-coverage A wf ha
  | safe-coverage b (wf-extend wf ha) hb
... | d , hA | e , hb′ = max d e ,
  safe-monotone A hA (max-left d e) , safe-monotone b hb′ (max-right d e)
safe-coverage (app f y) wf ht with app-inversion ht
... | A , B , hf , hy , eq with safe-coverage f wf hf
  | safe-coverage y wf hy | typing-type-rank wf hf
... | d , sf | e , sy | r , hr = max (max d e) r ,
  safe-monotone f sf (≤-trans (max-left d e) (max-left (max d e) r)) ,
  safe-monotone y sy (≤-trans (max-right d e) (max-left (max d e) r)) ,
  λ hl s hs → subst (λ q → q ≤ max (max d e) r)
    (sym (type-rank-unique wf hs hr)) (max-right (max d e) r)

rank-coverage : ∀ {n Γ} {t T : Term n}
  → WellFormed Γ → Typ Γ t T → Σ Nat (RedexBound Γ t)
rank-coverage {t = t} wf ht with safe-coverage t wf ht
... | d , safe = d , safe-to-bound safe

rank-budget : ∀ {n Γ} {t T : Term n} → WellFormed Γ → Typ Γ t T → Nat
rank-budget wf ht = fst (rank-coverage wf ht)

-- No redex-rank or termination witness is required from the caller.
normalize-typed : ∀ {n Γ} {t T : Term n}
  → (wf : WellFormed Γ) → (ht : Typ Γ t T)
  → Normalized Γ t T (rank-budget wf ht)
normalize-typed wf ht = normalize (rank-budget wf ht) wf ht (snd (rank-coverage wf ht))
