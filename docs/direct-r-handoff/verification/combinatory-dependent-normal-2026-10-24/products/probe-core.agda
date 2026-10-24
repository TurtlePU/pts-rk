{-# OPTIONS --cubical --safe --guardedness #-}
module NormalizedProducts where

-- All dependent PTS product operations on normal representatives. Products
-- and abstractions preserve normality structurally; application normalizes.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NativeAlgebra using (beta-pi; beta-lam; beta-app; beta-replace;
  replace-substitute; beta-substitute-argument)
open import NativeSubstitution using (substitution)
open import NativeInversion using (beta-path)
open import NormalizedSubstitution
open import NormalizedFamilies
open import NormalizedComprehension using (liftNF; lift-images)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    m n a b r : Nat

universeNF : {Γ : Context n} (i : Nat) → TyNF Γ zero
universeNF i = normal-at (U i) tt ∣ universe i ∣₁

-- BEGINNORMALPRODUCTS
piNF : {Γ : Context n} (A : TyNF Γ a)
  → TyNF (extend Γ (term A)) b → TyNF Γ (max (suc a) b)
piNF A B = normal-at (pi (term A) (term B)) (normal A , normal B)
  (PT.rec2 squash₁ (λ hA hB → ∣ product hA hB ∣₁) (typed A) (typed B))

lamNF : {Γ : Context n} (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  → NfAt (extend Γ (term A)) (term B) → NfAt Γ (term (piNF A B))
lamNF A B t = normal-at (lam (term A) (term t)) (normal A , normal t)
  (PT.rec2 squash₁ (λ hA ht → ∣ abstraction hA ht ∣₁) (typed A) (typed t))
-- ENDNORMALPRODUCTS

-- Change a type, never the stored normal subject. Only original conversion
-- is used, and its target-sorting premise is supplied by the normal type.
convertNF : {Γ : Context n} {A : Term n} (B : TyNF Γ r)
  → ∥ Beta A (term B) ∥₁ → NfAt Γ A → NfAt Γ (term B)
convertNF B e t = normal-at (term t) (normal t)
  (PT.rec3 squash₁ (λ ht hB p → ∣ conversion ht hB p ∣₁)
    (typed t) (typed B) e)

appType : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b) → NfAt Γ (term A) → TyNF Γ b
appType wf A B x = normalizeProof wf
  (PT.rec2 squash₁ (λ hB hx → ∣ substitution hB hx ∣₁) (typed B) (typed x))

appType-sound : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b) (x : NfAt Γ (term A))
  → ∥ Beta (substitute (term B) (term x)) (term (appType wf A B x)) ∥₁
appType-sound wf A B x = normalizeProof-sound wf
  (PT.rec2 squash₁ (λ hB hx → ∣ substitution hB hx ∣₁) (typed B) (typed x))

-- BEGINNORMALAPPLICATION
appNF : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  → NfAt Γ (term (piNF A B)) → (x : NfAt Γ (term A))
  → NfAt Γ (term (appType wf A B x))
appNF wf A B f x = convertNF (appType wf A B x) (appType-sound wf A B x)
  (normalizeProof wf (PT.rec2 squash₁
    (λ hf hx → ∣ application hf hx ∣₁) (typed f) (typed x)))
-- ENDNORMALAPPLICATION

appNF-sound : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  (f : NfAt Γ (term (piNF A B))) (x : NfAt Γ (term A))
  → ∥ Beta (app (term f) (term x)) (term (appNF wf A B f x)) ∥₁
appNF-sound wf A B f x = normalizeProof-sound wf
  (PT.rec2 squash₁ (λ hf hx → ∣ application hf hx ∣₁) (typed f) (typed x))

substituteNF : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  → NfAt (extend Γ (term A)) (term B) → (x : NfAt Γ (term A))
  → NfAt Γ (term (appType wf A B x))
substituteNF wf A B t x = convertNF (appType wf A B x) (appType-sound wf A B x)
  (normalizeProof wf (PT.rec2 squash₁
    (λ ht hx → ∣ substitution ht hx ∣₁) (typed t) (typed x)))

substituteNF-sound : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  (t : NfAt (extend Γ (term A)) (term B)) (x : NfAt Γ (term A))
  → ∥ Beta (substitute (term t) (term x)) (term (substituteNF wf A B t x)) ∥₁
substituteNF-sound wf A B t x = normalizeProof-sound wf
  (PT.rec2 squash₁ (λ ht hx → ∣ substitution ht hx ∣₁) (typed t) (typed x))

-- This is the ORIGINAL annotated beta rule, not an imposed equation.
betaNF : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  (t : NfAt (extend Γ (term A)) (term B)) (x : NfAt Γ (term A))
  → appNF wf A B (lamNF A B t) x ≡ substituteNF wf A B t x
betaNF wf A B t x = nf-path (normal-equal
  (normal (appNF wf A B (lamNF A B t) x)) (normal (substituteNF wf A B t x))
  (PT.rec2 squash₁ (λ p q → ∣ beta-trans (beta-sym p)
    (beta-trans (beta-step beta) q) ∣₁)
    (appNF-sound wf A B (lamNF A B t) x) (substituteNF-sound wf A B t x)))

-- Normalized substitution commutes with dependent product formation.
-- The supplied well-formedness witness is for the ACTUAL normalized
-- extension; it is not a new closure or normalization assumption.
abstract
  piNF-natural : {Γ : Context m} {Δ : Context n}
    (wf : WellFormed Δ) (σ : SubNF Γ Δ) (A : TyNF Γ a)
    (B : TyNF (extend Γ (term A)) b)
    (wf′ : WellFormed (extend Δ (term (pullTy wf σ A))))
    → pullTy wf σ (piNF A B)
      ≡ piNF (pullTy wf σ A) (pullTy wf′ (liftNF wf σ A) B)
  piNF-natural wf σ A B wf′ = nf-path (normal-equal
    (normal (pullTy wf σ (piNF A B)))
    (normal (piNF (pullTy wf σ A) (pullTy wf′ (liftNF wf σ A) B)))
    (PT.rec3 squash₁ (λ p q s → ∣ beta-trans (beta-sym p)
      (beta-pi q s) ∣₁)
      (pullTy-sound wf σ (piNF A B)) (pullTy-sound wf σ A)
      (pullTy-sound wf′ (liftNF wf σ A) B)))

lamNF-natural : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  (t : NfAt (extend Γ (term A)) (term B))
  (wf′ : WellFormed (extend Δ (term (pullTy wf σ A))))
  → term (pullTm wf σ (piNF A B) (lamNF A B t))
    ≡ term (lamNF (pullTy wf σ A) (pullTy wf′ (liftNF wf σ A) B)
      (pullTm wf′ (liftNF wf σ A) B t))
lamNF-natural wf σ A B t wf′ = normal-equal
  (normal (pullTm wf σ (piNF A B) (lamNF A B t)))
  (normal (lamNF (pullTy wf σ A) (pullTy wf′ (liftNF wf σ A) B)
    (pullTm wf′ (liftNF wf σ A) B t)))
  (PT.rec3 squash₁ (λ p q s → ∣ beta-trans (beta-sym p)
    (beta-lam q s) ∣₁)
    (pullTm-sound wf σ (piNF A B) (lamNF A B t)) (pullTy-sound wf σ A)
    (pullTm-sound wf′ (liftNF wf σ A) B t))

lamNF-natural-typed : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  (t : NfAt (extend Γ (term A)) (term B))
  (wf′ : WellFormed (extend Δ (term (pullTy wf σ A))))
  → subst (NfAt Δ) (cong term (piNF-natural wf σ A B wf′))
      (pullTm wf σ (piNF A B) (lamNF A B t))
    ≡ lamNF (pullTy wf σ A) (pullTy wf′ (liftNF wf σ A) B)
        (pullTm wf′ (liftNF wf σ A) B t)
lamNF-natural-typed wf σ A B t wf′ = nf-path
  (term-transport (cong term (piNF-natural wf σ A B wf′))
    (pullTm wf σ (piNF A B) (lamNF A B t))
  ∙ lamNF-natural wf σ A B t wf′)
