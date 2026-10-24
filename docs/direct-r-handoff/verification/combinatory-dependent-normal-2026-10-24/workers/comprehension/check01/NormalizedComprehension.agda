{-# OPTIONS --cubical --safe --guardedness #-}
module NormalizedComprehension where

-- Comprehension of ORIGINAL dependent contexts by normal substitutions.
-- Only typing witnesses are truncated; equations compare literal images.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NativeAlgebra using (fin-cases; replace-rename)
open import NativeSubstitution using (TypedSub)
open import NativeValuations
open import NormalizedSubstitution
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    m n : Nat

terminalNF : (Δ : Context n) → SubNF empty Δ
terminalNF Δ = pack (terminal Δ) (λ ())

terminal-unique : {Δ : Context n} (σ : SubNF empty Δ)
  → σ ≡ terminalNF Δ
terminal-unique σ = sub-path (λ ())

projectionNF : (Γ : Context n) (A : Term n) → SubNF Γ (extend Γ A)
projectionNF Γ A = pack (projection Γ A) (λ i → tt)

restrictNF : {Γ : Context m} {Δ : Context n} {A : Term m}
  → SubNF (extend Γ A) Δ → SubNF Γ Δ
restrictNF {Γ = Γ} {Δ} {A} (sub σ ns hs) = sub
  (λ i → σ (fsuc i)) (λ i → ns (fsuc i))
  (PT.map (λ ps → images-typed (restrict
    (valuation {Γ = extend Γ A} {Δ = Δ} σ ps))) hs)

lastNF : {Γ : Context m} {Δ : Context n} {A : Term m}
  → SubNF (extend Γ A) Δ → Term n
lastNF σ = sub-images σ fzero

last-normal : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : SubNF (extend Γ A) Δ) → Normal (lastNF σ)
last-normal σ = sub-normal σ fzero

last-typing : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : SubNF (extend Γ A) Δ)
  → ∥ Typ Δ (lastNF σ) (replace (sub-images (restrictNF σ)) A) ∥₁
last-typing {Γ = Γ} {Δ} {A} (sub σ ns hs) = PT.map
  (λ ps → last-typed (valuation {Γ = extend Γ A} {Δ = Δ} σ ps)) hs

-- BEGINNORMALCOMPREHENSION
pairNF : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : SubNF Γ Δ) (y : Term n) → Normal y
  → ∥ Typ Δ y (replace (sub-images σ) A) ∥₁
  → SubNF (extend Γ A) Δ
pairNF {Γ = Γ} {Δ} {A} (sub σ ns hs) y ny hy = sub
  (λ i → caseFin i y σ)
  (λ i → fin-cases (λ i → Normal (caseFin i y σ)) i ny ns)
  (PT.rec2 squash₁ (λ ps py → ∣ images-typed
    (extend-valuation {A = A} (valuation {Γ = Γ} {Δ = Δ} σ ps) y py) ∣₁) hs hy)

restrict-pair : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : SubNF Γ Δ) (y : Term n) (ny : Normal y)
  (hy : ∥ Typ Δ y (replace (sub-images σ) A) ∥₁)
  → restrictNF (pairNF {A = A} σ y ny hy) ≡ σ
restrict-pair σ y ny hy = sub-path (λ i → refl)

last-pair : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : SubNF Γ Δ) (y : Term n) (ny : Normal y)
  (hy : ∥ Typ Δ y (replace (sub-images σ) A) ∥₁)
  → lastNF (pairNF {A = A} σ y ny hy) ≡ y
last-pair σ y ny hy = refl

pair-eta : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : SubNF (extend Γ A) Δ)
  → pairNF (restrictNF σ) (lastNF σ) (last-normal σ) (last-typing σ) ≡ σ
pair-eta σ = sub-path (λ i → fin-cases
  (λ i → caseFin i (lastNF σ) (sub-images (restrictNF σ)) ≡ sub-images σ i)
  i refl (λ j → refl))
-- ENDNORMALCOMPREHENSION

pair-unique : {Γ : Context m} {Δ : Context n} {A : Term m}
  {σ τ : SubNF (extend Γ A) Δ}
  → restrictNF σ ≡ restrictNF τ → lastNF σ ≡ lastNF τ → σ ≡ τ
pair-unique {σ = σ} {τ} e p = sub-path (λ i → fin-cases
  (λ i → sub-images σ i ≡ sub-images τ i) i p
  (λ j → cong (λ ρ → sub-images ρ j) e))

projection-identity : {Γ : Context n} {A : Term n}
  → restrictNF (idNF (extend Γ A)) ≡ projectionNF Γ A
projection-identity = sub-path (λ i → refl)
