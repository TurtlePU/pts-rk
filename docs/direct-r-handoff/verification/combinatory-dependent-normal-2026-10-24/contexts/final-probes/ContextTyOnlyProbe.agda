{-# OPTIONS --cubical --safe --guardedness #-}
module ContextTyOnlyProbe where
open import ContextIRProbe
open import ContextNormalizeProbe
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NormalizedFamilies
open import NormalizedSubstitution using (SubNF)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)

actTy : {Γ Δ : Con} {r : Nat}
  → SubNF (context Γ) (context Δ) → TyNF (context Γ) r → TyNF (context Δ) r
actTy {Γ} {Δ} {r} σ A = normalizeContextTerm Δ
  {t = raw-act σ (term A)} {A = U r}
  (raw-act-typed σ (typed A))

actTy-sound : {Γ Δ : Con} {r : Nat}
  (σ : SubNF (context Γ) (context Δ)) (A : TyNF (context Γ) r)
  → ∥ Beta (raw-act σ (term A)) (term (actTy {Γ} {Δ} σ A)) ∥₁
actTy-sound {Γ} {Δ} {r} σ A = normalizeContext-sound Δ
  {t = raw-act σ (term A)} {A = U r}
  (raw-act-typed σ (typed A))

abstract
  actTy-agrees : {Γ Δ : Con} {r : Nat} (wf : WellFormed (context Δ))
    (σ : SubNF (context Γ) (context Δ)) (A : TyNF (context Γ) r)
    → actTy {Γ} {Δ} σ A ≡ pullTy wf σ A
  actTy-agrees {Γ} {Δ} {r} wf σ A = normalizeContext-agrees Δ
    {t = raw-act σ (term A)} {A = U r} wf (raw-act-typed σ (typed A))
