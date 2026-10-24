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

-- Decoding a normal universe inhabitant is literally the same family.
ElNF : {Γ : Context n} (r : Nat) → NfAt Γ (term (universeNF r)) → TyNF Γ r
ElNF r t = t

abstract
  universeNF-natural : {Γ : Context m} {Δ : Context n}
    (wf : WellFormed Δ) (σ : SubNF Γ Δ) (i : Nat)
    → pullTy wf σ (universeNF i) ≡ universeNF i
  universeNF-natural wf σ i = nf-path (normal-equal
    {t = term (pullTy wf σ (universeNF i))} {u = U i}
    (normal (pullTy wf σ (universeNF i))) tt
    (PT.map beta-sym (pullTy-sound wf σ (universeNF i))))

ElNF-natural : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) (r : Nat)
  (t : NfAt Γ (term (universeNF r)))
  → pullTy wf σ (ElNF r t)
    ≡ ElNF r (castNF (cong term (universeNF-natural wf σ r))
      (pullTm wf σ (universeNF r) t))
ElNF-natural wf σ r t = nf-path (normal-equal
  {t = term (pullTy wf σ t)} {u = term (pullTm wf σ (universeNF r) t)}
  (normal (pullTy wf σ t)) (normal (pullTm wf σ (universeNF r) t))
  (PT.rec2 squash₁ (λ p q → ∣ beta-trans (beta-sym p) q ∣₁)
    (pullTy-sound wf σ t) (pullTm-sound wf σ (universeNF r) t)))

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

-- The two sides' dependent result types normalize to the same type.
private
  application-type-chain : (σ : Fin m → Term n) (B : Term (suc m))
    (x T : Term m) (B′ : Term (suc n)) (x′ L R : Term n)
    → Beta (replace σ T) L → Beta (substitute B x) T
    → Beta (substitute B′ x′) R
    → Beta (replace (liftSubstitution σ) B) B′ → Beta (replace σ x) x′
    → Beta L R
  application-type-chain σ B x T B′ x′ L R p q s eB ex =
    beta-trans (beta-sym p)
      (beta-trans (beta-replace σ (beta-sym q))
        (beta-trans (beta-path (replace-substitute σ B x))
          (beta-trans (beta-replace (single (replace σ x)) eB)
            (beta-trans (beta-substitute-argument B′ ex) s))))

abstract
  appType-natural : {Γ : Context m} {Δ : Context n}
    (wfΓ : WellFormed Γ) (wf : WellFormed Δ) (σ : SubNF Γ Δ)
    (A : TyNF Γ a) (B : TyNF (extend Γ (term A)) b) (x : NfAt Γ (term A))
    (wf′ : WellFormed (extend Δ (term (pullTy wf σ A))))
    → pullTy wf σ (appType wfΓ A B x)
      ≡ appType wf (pullTy wf σ A) (pullTy wf′ (liftNF wf σ A) B) (pullTm wf σ A x)
  appType-natural {b = b} {Δ = Δ} wfΓ wf σ A B x wf′ = nf-path
    {t = left} {u = right} (normal-equal {t = term left} {u = term right}
    (normal left) (normal right)
    (PT.rec3 {P = ∥ Beta (term left) (term right) ∥₁} squash₁
      (λ p q s → PT.rec2 {P = ∥ Beta (term left) (term right) ∥₁} squash₁
      (λ eB ex → ∣ application-type-chain (sub-images σ) (term B) (term x)
        (term (appType wfΓ A B x)) (term B′) (term (pullTm wf σ A x))
        (term left) (term right) p q s eB ex ∣₁)
      (pullTy-sound wf′ (liftNF wf σ A) B) (pullTm-sound wf σ A x))
      (pullTy-sound wf σ (appType wfΓ A B x)) (appType-sound wfΓ A B x)
      (appType-sound wf (pullTy wf σ A) B′ (pullTm wf σ A x))))
    where
    B′ : TyNF (extend Δ (term (pullTy wf σ A))) b
    B′ = pullTy wf′ (liftNF wf σ A) B
    left : TyNF Δ b
    left = pullTy wf σ (appType wfΓ A B x)
    right : TyNF Δ b
    right = appType wf (pullTy wf σ A) B′ (pullTm wf σ A x)

appNF-natural : {Γ : Context m} {Δ : Context n}
  (wfΓ : WellFormed Γ) (wf : WellFormed Δ) (σ : SubNF Γ Δ)
  (A : TyNF Γ a) (B : TyNF (extend Γ (term A)) b)
  (f : NfAt Γ (term (piNF A B))) (x : NfAt Γ (term A))
  (wf′ : WellFormed (extend Δ (term (pullTy wf σ A))))
  → castNF (cong term (appType-natural wfΓ wf σ A B x wf′))
      (pullTm wf σ (appType wfΓ A B x) (appNF wfΓ A B f x))
    ≡ appNF wf (pullTy wf σ A) (pullTy wf′ (liftNF wf σ A) B)
      (castNF (cong term (piNF-natural wf σ A B wf′))
        (pullTm wf σ (piNF A B) f)) (pullTm wf σ A x)
appNF-natural {Δ = Δ} wfΓ wf σ A B f x wf′ = nf-path
  (normal-equal {t = term left} {u = term right} (normal left) (normal right)
    (PT.rec3 squash₁ (λ p q ef → PT.rec2 squash₁
      (λ ex s → ∣ beta-trans (beta-sym p)
        (beta-trans (beta-replace (sub-images σ) (beta-sym q))
          (beta-trans (beta-app
            ef ex) s)) ∣₁)
      (pullTm-sound wf σ A x) (appNF-sound wf A′ B′ f′ x′))
      (pullTm-sound wf σ (appType wfΓ A B x) (appNF wfΓ A B f x))
      (appNF-sound wfΓ A B f x) (pullTm-sound wf σ (piNF A B) f)))
  where
  A′ = pullTy wf σ A
  B′ = pullTy wf′ (liftNF wf σ A) B
  pulledF = pullTm wf σ (piNF A B) f
  fPath = cong term (piNF-natural wf σ A B wf′)
  f′ = castNF fPath pulledF
  x′ = pullTm wf σ A x
  left = pullTm wf σ (appType wfΓ A B x) (appNF wfΓ A B f x)
  right = appNF wf A′ B′ f′ x′
