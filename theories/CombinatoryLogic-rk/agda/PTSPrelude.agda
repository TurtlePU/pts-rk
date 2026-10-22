{-# OPTIONS --cubical --safe --guardedness #-}
module PTSPrelude where

-- The Cubical library is the only dependency beyond Agda's builtins.
open import Cubical.Foundations.Prelude public
  using (_≡_; PathP; I; i0; i1; refl; sym; cong; cong₂; _∙_; isSet;
         transport; subst; funExt; Σ; _,_; fst; snd)
open import Cubical.Foundations.HLevels public using (isSetΣ)
open import Cubical.Data.Nat.Base public using (zero; suc) renaming (ℕ to Nat)
open import Cubical.Data.Nat.Properties public using (isSetℕ)

max : Nat → Nat → Nat
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)
