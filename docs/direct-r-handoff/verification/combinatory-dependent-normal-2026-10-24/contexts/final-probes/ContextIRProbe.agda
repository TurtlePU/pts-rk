{-# OPTIONS --cubical --safe --guardedness #-}
module ContextIRProbe where

open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NormalizedFamilies
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

mutual
  data Con : Set where
    ε : Con
    ext : (Γ : Con) {r : Nat} → TyNF (context Γ) r → Con

  length : Con → Nat
  length ε = zero
  length (ext Γ A) = suc (length Γ)

  context : (Γ : Con) → Context (length Γ)
  context ε = empty
  context (ext Γ A) = extend (context Γ) (term A)

wellformed : (Γ : Con) → ∥ WellFormed (context Γ) ∥₁
wellformed ε = ∣ wf-empty ∣₁
wellformed (ext Γ A) = PT.rec2 squash₁
  (λ wf hA → ∣ wf-extend wf hA ∣₁) (wellformed Γ) (typed A)
