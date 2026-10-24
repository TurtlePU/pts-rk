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
import NormalizedInference as Infer
open import NativeCertificates using (term-discrete)
open import Cubical.Relation.Nullary using (Discrete→isSet)
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

private
  module Normalize (Γ : Con) {t A : Native.Term (length Γ)}
    (ht : ∥ Typ (context Γ) t A ∥₁) where

    run : ∥ WellFormed (context Γ) ∥₁ → NfAt (context Γ) A
    run = PT.rec→Set nf-isSet (λ wf → normalizeProof wf ht)
      (λ wf wf′ → normalizeProof-coherent wf wf′ ht ht ∣ beta-refl ∣₁)

    sound : (wf : ∥ WellFormed (context Γ) ∥₁) → ∥ Beta t (term (run wf)) ∥₁
    sound = PT.elim {P = λ wf → ∥ Beta t (term (run wf)) ∥₁}
      (λ _ → squash₁) (λ wf → normalizeProof-sound wf ht)

normalizeContextTerm : (Γ : Con) {t A : Native.Term (length Γ)}
  → ∥ Typ (context Γ) t A ∥₁ → NfAt (context Γ) A
normalizeContextTerm Γ ht = Normalize.run Γ ht (wellformed Γ)

normalizeContext-sound : (Γ : Con) {t A : Native.Term (length Γ)}
  (ht : ∥ Typ (context Γ) t A ∥₁)
  → ∥ Beta t (term (normalizeContextTerm Γ ht)) ∥₁
normalizeContext-sound Γ ht = Normalize.sound Γ ht (wellformed Γ)

normalizeContext-agrees : (Γ : Con) {t A : Native.Term (length Γ)}
  (wf : WellFormed (context Γ)) (ht : ∥ Typ (context Γ) t A ∥₁)
  → normalizeContextTerm Γ ht ≡ normalizeProof wf ht
normalizeContext-agrees Γ wf ht = nf-path
  {t = normalizeContextTerm Γ ht} {u = normalizeProof wf ht}
  (normal-equal {t = term (normalizeContextTerm Γ ht)} {u = term (normalizeProof wf ht)}
    (normal (normalizeContextTerm Γ ht)) (normal (normalizeProof wf ht))
    (PT.rec2 squash₁ (λ left right → ∣ beta-trans (beta-sym left) right ∣₁)
      (normalizeContext-sound Γ ht) (normalizeProof-sound wf ht)))

actTy : {Γ Δ : Con} {r : Nat} → Sub Γ Δ → Ty Γ r → Ty Δ r
actTy {Γ} {Δ} {r} σ A = normalizeContextTerm Δ
  {t = raw-act σ (term A)} {A = U r} (raw-act-typed σ (typed A))

actTy-sound : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r)
  → ∥ Beta (raw-act σ (term A)) (term (actTy {Γ} {Δ} σ A)) ∥₁
actTy-sound {Γ} {Δ} {r} σ A = normalizeContext-sound Δ
  {t = raw-act σ (term A)} {A = U r} (raw-act-typed σ (typed A))

abstract
  actTy-agrees : {Γ Δ : Con} {r : Nat} (wf : WellFormed (context Δ))
    (σ : Sub Γ Δ) (A : Ty Γ r) → actTy {Γ} {Δ} σ A ≡ pullTy wf σ A
  actTy-agrees {Γ} {Δ} {r} wf σ A = normalizeContext-agrees Δ
    {t = raw-act σ (term A)} {A = U r} wf (raw-act-typed σ (typed A))

private
  actTm-typing : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r) (t : Tm Γ A)
    → ∥ Typ (context Δ) (raw-act σ (term t)) (term (actTy {Γ} {Δ} σ A)) ∥₁
  actTm-typing {Γ} {Δ} σ A t = PT.rec3 squash₁ (λ ht hA e → ∣ conversion ht hA e ∣₁)
    (raw-act-typed σ (typed t)) (typed (actTy {Γ} {Δ} σ A)) (actTy-sound {Γ} {Δ} σ A)

actTm : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r)
  → Tm Γ A → Tm Δ (actTy {Γ} {Δ} σ A)
actTm {Γ} {Δ} σ A t = normalizeContextTerm Δ
  {t = raw-act σ (term t)} {A = term (actTy {Γ} {Δ} σ A)}
  (actTm-typing {Γ} {Δ} σ A t)

actTm-sound : {Γ Δ : Con} {r : Nat} (σ : Sub Γ Δ) (A : Ty Γ r) (t : Tm Γ A)
  → ∥ Beta (raw-act σ (term t)) (term (actTm {Γ} {Δ} σ A t)) ∥₁
actTm-sound {Γ} {Δ} σ A t = normalizeContext-sound Δ
  {t = raw-act σ (term t)} {A = term (actTy {Γ} {Δ} σ A)}
  (actTm-typing {Γ} {Δ} σ A t)

actTm-agrees : {Γ Δ : Con} {r : Nat} (wf : WellFormed (context Δ))
  (σ : Sub Γ Δ) (A : Ty Γ r) (t : Tm Γ A)
  → castNF (cong term (actTy-agrees {Γ} {Δ} wf σ A)) (actTm {Γ} {Δ} σ A t)
    ≡ pullTm wf σ A t
actTm-agrees {Γ} {Δ} wf σ A t = nf-path
  {t = castNF (cong term (actTy-agrees {Γ} {Δ} wf σ A)) (actTm {Γ} {Δ} σ A t)}
  {u = pullTm wf σ A t}
  (normal-equal {t = term (actTm {Γ} {Δ} σ A t)} {u = term (pullTm wf σ A t)}
    (normal (actTm {Γ} {Δ} σ A t)) (normal (pullTm wf σ A t))
    (PT.rec2 squash₁ (λ left right → ∣ beta-trans (beta-sym left) right ∣₁)
      (actTm-sound {Γ} {Δ} σ A t) (pullTm-sound wf σ A t)))

-- The computed-type surface also needs no chosen well-formedness witness.
InferTm : Con → Set
InferTm Γ = Infer.Tm (context Γ)

private
  module InferType (Γ : Con) (t : InferTm Γ) where
    run : ∥ WellFormed (context Γ) ∥₁ → Σ Nat (λ _ → Native.Term (length Γ))
    run = PT.rec→Set (isSetΣ isSetℕ (λ _ → Discrete→isSet term-discrete))
      (λ wf → Infer.rankOf wf t , Infer.tyOf wf t)
      (λ wf wf′ → Infer.wellformed-independent wf wf′ t)

    normal-type : (wf : ∥ WellFormed (context Γ) ∥₁) → Normal (snd (run wf))
    normal-type = PT.elim {P = λ wf → Normal (snd (run wf))}
      (λ _ → normal-isProp) (λ wf → Infer.type-normal wf t)

    sorted : (wf : ∥ WellFormed (context Γ) ∥₁)
      → ∥ Typ (context Γ) (snd (run wf)) (U (fst (run wf))) ∥₁
    sorted = PT.elim {P = λ wf → ∥ Typ (context Γ) (snd (run wf)) (U (fst (run wf))) ∥₁}
      (λ _ → squash₁) (λ wf → Infer.type-sorted wf t)

    inhabits : (wf : ∥ WellFormed (context Γ) ∥₁)
      → ∥ Typ (context Γ) (Infer.body t) (snd (run wf)) ∥₁
    inhabits = PT.elim {P = λ wf → ∥ Typ (context Γ) (Infer.body t) (snd (run wf)) ∥₁}
      (λ _ → squash₁) (λ wf → Infer.has-type wf t)

rankOf : (Γ : Con) → InferTm Γ → Nat
rankOf Γ t = fst (InferType.run Γ t (wellformed Γ))

tyOf : (Γ : Con) → InferTm Γ → Native.Term (length Γ)
tyOf Γ t = snd (InferType.run Γ t (wellformed Γ))

inferred-type : (Γ : Con) (t : InferTm Γ) → Ty Γ (rankOf Γ t)
inferred-type Γ t = normal-at (tyOf Γ t)
  (InferType.normal-type Γ t (wellformed Γ)) (InferType.sorted Γ t (wellformed Γ))

inferred-term : (Γ : Con) (t : InferTm Γ) → Tm Γ (inferred-type Γ t)
inferred-term Γ t = normal-at (Infer.body t) (Infer.body-normal t)
  (InferType.inhabits Γ t (wellformed Γ))

inferred-retraction : (Γ : Con) (t : InferTm Γ) → Infer.from-normal (inferred-term Γ t) ≡ t
inferred-retraction Γ t = Infer.tm-path refl
