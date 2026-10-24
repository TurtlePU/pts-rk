{-# OPTIONS --cubical --safe --guardedness #-}
module ContextActionProbe where
open import ContextIRProbe
open import ContextNormalizeProbe
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NormalizedFamilies
open import NormalizedSubstitution using (SubNF)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

Ty : Con → Nat → Set
Ty Γ r = TyNF (context Γ) r

Tm : (Γ : Con) {r : Nat} → Ty Γ r → Set
Tm Γ A = NfAt (context Γ) (term A)

Sub : Con → Con → Set
Sub Γ Δ = SubNF (context Γ) (context Δ)

actTy : {Γ Δ : Con} {r : Nat} → Sub Γ Δ → Ty Γ r → Ty Δ r
actTy {Δ = Δ} σ A = normalizeContextTerm Δ (raw-act-typed σ (typed A))

actTy-sound : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r)
  → ∥ Beta (raw-act σ (term A)) (term (actTy {Γ} {Δ} σ A)) ∥₁
actTy-sound {Δ = Δ} σ A = normalizeContext-sound Δ (raw-act-typed σ (typed A))

abstract
  actTy-agrees : {Γ Δ : Con} {r : Nat} (wf : WellFormed (context Δ))
    (σ : Sub Γ Δ) (A : Ty Γ r) → actTy {Γ} {Δ} σ A ≡ pullTy wf σ A
  actTy-agrees {Δ = Δ} wf σ A = normalizeContext-agrees Δ wf (raw-act-typed σ (typed A))
