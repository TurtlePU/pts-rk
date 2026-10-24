{-# OPTIONS --cubical --safe --guardedness #-}
module ContextNormalizeProbe where
open import ContextIRProbe
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NormalizedFamilies
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

private
  module Normalize (Γ : Con) {t A : Term (length Γ)}
    (ht : ∥ Typ (context Γ) t A ∥₁) where
    run : ∥ WellFormed (context Γ) ∥₁ → NfAt (context Γ) A
    run = PT.rec→Set nf-isSet (λ wf → normalizeProof wf ht)
      (λ wf wf′ → normalizeProof-coherent wf wf′ ht ht ∣ beta-refl ∣₁)

    sound : (wf : ∥ WellFormed (context Γ) ∥₁) → ∥ Beta t (term (run wf)) ∥₁
    sound = PT.elim {P = λ wf → ∥ Beta t (term (run wf)) ∥₁}
      (λ _ → squash₁) (λ wf → normalizeProof-sound wf ht)

normalizeContextTerm : (Γ : Con) {t A : Term (length Γ)}
  → ∥ Typ (context Γ) t A ∥₁ → NfAt (context Γ) A
normalizeContextTerm Γ ht = Normalize.run Γ ht (wellformed Γ)

normalizeContext-sound : (Γ : Con) {t A : Term (length Γ)}
  (ht : ∥ Typ (context Γ) t A ∥₁)
  → ∥ Beta t (term (normalizeContextTerm Γ ht)) ∥₁
normalizeContext-sound Γ ht = Normalize.sound Γ ht (wellformed Γ)

normalizeContext-agrees : (Γ : Con) {t A : Term (length Γ)}
  (wf : WellFormed (context Γ)) (ht : ∥ Typ (context Γ) t A ∥₁)
  → normalizeContextTerm Γ ht ≡ normalizeProof wf ht
normalizeContext-agrees Γ wf ht = nf-path
  (normal-equal (normal (normalizeContextTerm Γ ht)) (normal (normalizeProof wf ht))
    (PT.rec2 squash₁ (λ left right → ∣ beta-trans (beta-sym left) right ∣₁)
      (normalizeContext-sound Γ ht) (normalizeProof-sound wf ht)))
