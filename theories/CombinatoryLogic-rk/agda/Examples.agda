{-# OPTIONS --cubical --safe --guardedness #-}
module Examples where

open import PTSPrelude
open import Combinatory
open import SCanonical using (S; SType; S-type)

-- These checks instantiate the public constructors; they are regressions,
-- not a consistency, completeness or native-syntax interpretation theorem.
universe-check : (r : Nat) → tyOf (univ {Γ = empty} r) ≡ (zero , U zero)
universe-check r = refl

universe-decode : (r : Nat) → El zero (univ {Γ = empty} r) refl ≡ U r
universe-decode r = El-univ r

constant-check : (a b : Nat) → TmAt empty (KType a b)
constant-check a b = K-atom a b , refl

product-check : (a b : Nat) → TmAt empty (PType a b)
product-check a b = P-atom a b , refl

substitution-check : (a b c : Nat) → TmAt empty (SType a b c)
substitution-check a b c = S a b c , S-type a b c

variable-check : (Γ : Con) (r : Nat)
               → tyOf (sndS {A = U {Γ = Γ} r} id) ≡ (zero , U r)
variable-check Γ r = varUType r

projection-check : ∀ {Γ Δ r} {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
                   (p : tyOf t ≡ (r , subTy A σ))
                 → sndS (pair σ t p) ≡ t
projection-check = beta-snd-derived

-- Rank normalization is independent of the object-level inhabitants.
max-next : (n : Nat) → max (suc n) n ≡ suc n
max-next zero = refl
max-next (suc n) = cong suc (max-next n)

k-core-rank : (a b : Nat)
            → max (suc a) (max (suc b) a) ≡ max (suc a) (suc b)
k-core-rank zero b = refl
k-core-rank (suc a) zero = cong suc (max-next a)
k-core-rank (suc a) (suc b) = cong suc (k-core-rank a b)

k-rank : (a b : Nat) → kRank a b ≡ max (suc a) (suc b)
k-rank a b = cong (λ n → max 1 (max 1 n)) (k-core-rank a b)
