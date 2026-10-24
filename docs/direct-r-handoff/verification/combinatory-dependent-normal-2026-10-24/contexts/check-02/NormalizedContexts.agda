{-# OPTIONS --cubical --safe --guardedness #-}
module NormalizedContexts where

-- An inductive-recursive context presentation using normal PTS declarations.
-- Typing/well-formedness witnesses stay truncated: operations never choose one.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping using (Context; Typ; WellFormed; Beta; beta-refl;
  beta-sym; beta-trans; conversion; empty; extend; wf-empty; wf-extend)
import NativeTyping as Native
open import NormalizedSubstitution using (SubNF)
open import NormalizedFamilies
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

-- BEGINNORMALCONTEXTS
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

Ty : Con → Nat → Set
Ty Γ r = TyNF (context Γ) r

Tm : (Γ : Con) {r : Nat} → Ty Γ r → Set
Tm Γ A = NfAt (context Γ) (term A)

Sub : Con → Con → Set
Sub Γ Δ = SubNF (context Γ) (context Δ)
-- ENDNORMALCONTEXTS

wellformed : (Γ : Con) → ∥ WellFormed (context Γ) ∥₁
wellformed ε = ∣ wf-empty ∣₁
wellformed (ext Γ A) = PT.rec2 squash₁
  (λ wf hA → ∣ wf-extend wf hA ∣₁) (wellformed Γ) (typed A)

normalizeContextTerm : (Γ : Con) {t A : Native.Term (length Γ)}
  → ∥ Typ (context Γ) t A ∥₁ → NfAt (context Γ) A
normalizeContextTerm Γ ht = PT.rec→Set nf-isSet
  (λ wf → normalizeProof wf ht)
  (λ wf wf′ → normalizeProof-coherent wf wf′ ht ht ∣ beta-refl ∣₁)
  (wellformed Γ)

normalizeContext-sound : (Γ : Con) {t A : Native.Term (length Γ)}
  (ht : ∥ Typ (context Γ) t A ∥₁)
  → ∥ Beta t (term (normalizeContextTerm Γ ht)) ∥₁
normalizeContext-sound Γ {t} ht = PT.elim
  {P = λ wf → ∥ Beta t (term (PT.rec→Set nf-isSet
    (λ wf → normalizeProof wf ht)
    (λ wf wf′ → normalizeProof-coherent wf wf′ ht ht ∣ beta-refl ∣₁) wf)) ∥₁}
  (λ _ → squash₁) (λ wf → normalizeProof-sound wf ht) (wellformed Γ)

normalizeContext-agrees : (Γ : Con) {t A : Native.Term (length Γ)}
  (wf : WellFormed (context Γ)) (ht : ∥ Typ (context Γ) t A ∥₁)
  → normalizeContextTerm Γ ht ≡ normalizeProof wf ht
normalizeContext-agrees Γ wf ht = nf-path
  (normal-equal (normal (normalizeContextTerm Γ ht)) (normal (normalizeProof wf ht))
    (PT.rec2 squash₁ (λ left right → ∣ beta-trans (beta-sym left) right ∣₁)
      (normalizeContext-sound Γ ht) (normalizeProof-sound wf ht)))

actTy : {Γ Δ : Con} {r : Nat} → Sub Γ Δ → Ty Γ r → Ty Δ r
actTy {Δ = Δ} σ A = normalizeContextTerm Δ (raw-act-typed σ (typed A))

actTy-sound : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r)
  → ∥ Beta (raw-act σ (term A)) (term (actTy {Γ} {Δ} σ A)) ∥₁
actTy-sound {Δ = Δ} σ A = normalizeContext-sound Δ (raw-act-typed σ (typed A))

actTy-agrees : {Γ Δ : Con} {r : Nat} (wf : WellFormed (context Δ))
  (σ : Sub Γ Δ) (A : Ty Γ r) → actTy {Γ} {Δ} σ A ≡ pullTy wf σ A
actTy-agrees {Δ = Δ} wf σ A = normalizeContext-agrees Δ wf (raw-act-typed σ (typed A))

private
  actTm-typing : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r) (t : Tm Γ A)
    → ∥ Typ (context Δ) (raw-act σ (term t)) (term (actTy {Γ} {Δ} σ A)) ∥₁
  actTm-typing {Γ} {Δ} σ A t = PT.rec3 squash₁ (λ ht hA e → ∣ conversion ht hA e ∣₁)
    (raw-act-typed σ (typed t)) (typed (actTy {Γ} {Δ} σ A)) (actTy-sound {Γ} {Δ} σ A)

actTm : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r)
  → Tm Γ A → Tm Δ (actTy {Γ} {Δ} σ A)
actTm {Γ} {Δ} σ A t = normalizeContextTerm Δ (actTm-typing {Γ} {Δ} σ A t)

actTm-sound : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r) (t : Tm Γ A)
  → ∥ Beta (raw-act σ (term t)) (term (actTm {Γ} {Δ} σ A t)) ∥₁
actTm-sound {Γ} {Δ} σ A t = normalizeContext-sound Δ (actTm-typing {Γ} {Δ} σ A t)

actTm-agrees : {Γ Δ : Con} {r : Nat} (wf : WellFormed (context Δ))
  (σ : Sub Γ Δ) (A : Ty Γ r) (t : Tm Γ A)
  → subst (NfAt (context Δ)) (cong term (actTy-agrees {Γ} {Δ} wf σ A))
      (actTm {Γ} {Δ} σ A t)
    ≡ pullTm wf σ A t
actTm-agrees {Γ} {Δ} wf σ A t = nf-path
  (term-transport (cong term (actTy-agrees {Γ} {Δ} wf σ A)) (actTm {Γ} {Δ} σ A t)
  ∙ normal-equal (normal (actTm {Γ} {Δ} σ A t)) (normal (pullTm wf σ A t))
    (PT.rec2 squash₁ (λ left right → ∣ beta-trans (beta-sym left) right ∣₁)
      (actTm-sound {Γ} {Δ} σ A t) (pullTm-sound wf σ A t)))
