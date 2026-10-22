{-# OPTIONS --cubical --safe --guardedness #-}
module ExponentialBounds where

open import FiniteBounds using (Nat; suc; _+_; _·_; _^_; _≤_;
  power-exponent-monotone; power-addition)
open import Cubical.Foundations.Prelude using (_≡_; _,_; refl; sym; cong; subst)
open import Cubical.Data.Nat.Order using (≤-trans)
open import Cubical.Tactics.NatSolver

private
  double-product : (A B : Nat) → 2 ≤ A → 2 ≤ B
    → suc (A + B) ≤ 2 · (A · B)
  double-product A B (x , p) (y , q) =
    subst (λ A → suc (A + B) ≤ 2 · (A · B)) p
      (subst (λ B → suc ((x + 2) + B) ≤ 2 · ((x + 2) · B)) q
        (2 · x · y + 3 · x + 3 · y + 3 , solveℕ!))

-- A binary syntax node joins two exponential child-size bounds.
exponential-join : (a b : Nat) → 1 ≤ a → 1 ≤ b
  → suc (2 ^ a + 2 ^ b) ≤ 2 ^ suc (a + b)
exponential-join a b ha hb =
  subst (suc (2 ^ a + 2 ^ b) ≤_)
    (sym (cong (2 ·_) (power-addition 2 a b)))
    (double-product (2 ^ a) (2 ^ b)
      (power-exponent-monotone 2 (1 , refl) ha)
      (power-exponent-monotone 2 (1 , refl) hb))
