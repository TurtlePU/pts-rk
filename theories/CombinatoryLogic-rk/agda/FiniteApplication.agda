{-# OPTIONS --cubical --safe --guardedness #-}
module FiniteApplication where

open import FiniteSyntax
open import FiniteBounds using (tower; tetration)
open import FiniteCarriers using (AtMost; subtype-finite)
open import NormalForms using (Nf; nf-U; nf-var; nf-lam; erase; SizedNf; from-normal;
  erase-from-normal; closed-normal-bound)
open import BoundedReduction using (Normal; normal?; rounds)
open import BoundedTrace using (BoundedSteps; rounds-bounded)
open import RawSizeBounds using (rounds-size)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Maybe.Base using (Maybe; just; nothing)
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Relation.Nullary.Base using (yes; no)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; isPropPropTrunc)

private
  variable
    a : Nat

application : Nf (Fin a) 0 → Nf (Fin a) 0 → Raw (Fin a) 0
application {a} f y = app (erase (Fin a) f) (erase (Fin a) y)

inputSize : Nf (Fin a) 0 → Nf (Fin a) 0 → Nat
inputSize f y = nodes (application f y)

-- BEGINFINITEAPPLICATIONTYPE
-- The output is a bounded IIR normal form, not a raw term with an opaque tag.
-- Truncation counts represented terms, rather than their reduction proofs.
ApplicationResult : (d : Nat) (f y : Nf (Fin a) 0) → Set
ApplicationResult {a} d f y =
  Σ (SizedNf a 0 (tower d (inputSize f y)))
    (λ v → ∥ BoundedSteps (tower d (inputSize f y))
      (application f y) (erase (Fin a) (fst v)) ∥₁)

application-result-bound : (d : Nat) (f y : Nf (Fin a) 0)
  → a ≤ inputSize f y
  → AtMost (ApplicationResult d f y)
      (tetration (4 · inputSize f y + 4) (d + 3))
application-result-bound {a} d f y labelsBound =
  subtype-finite (λ v → ∥ BoundedSteps (tower d (inputSize f y))
      (application f y) (erase (Fin a) (fst v)) ∥₁)
    (λ _ → isPropPropTrunc)
    (closed-normal-bound a d (inputSize f y) labelsBound)
-- ENDFINITEAPPLICATIONTYPE

private
  pack-result : (d : Nat) (f y : Nf (Fin a) 0)
    → Normal (rounds d (application f y))
    → nodes (rounds d (application f y)) ≤ tower d (inputSize f y)
    → ApplicationResult d f y
  pack-result {a} d f y normal sizeBound =
    (from-normal t normal , subst (λ u → nodes u ≤ tower d (inputSize f y))
      (sym p) sizeBound)
    , ∣ subst (BoundedSteps (tower d (inputSize f y)) (application f y)) (sym p)
          (rounds-bounded d (application f y)) ∣₁
    where
      t = rounds d (application f y)
      p = erase-from-normal t normal

-- Internal packaging: typed callers prove normality by rank descent.
result-from-normal : (d : Nat) (f y : Nf (Fin a) 0)
  → Normal (rounds d (application f y)) → ApplicationResult d f y
result-from-normal d f y normal =
  pack-result d f y normal (rounds-size d (application f y))

result-recovers : (d : Nat) (f y : Nf (Fin a) 0)
  (normal : Normal (rounds d (application f y)))
  → erase (Fin a) (fst (fst (result-from-normal d f y normal)))
      ≡ rounds d (application f y)
result-recovers d f y normal = erase-from-normal _ normal

-- BEGINFINITEAPPLICATION
-- A total bounded attempt. The size bound is proved unconditionally;
-- Nothing means only that these passes have not reached normal form.
applyWithinFinite : (d : Nat) (f y : Nf (Fin a) 0)
  → a ≤ inputSize f y → Maybe (ApplicationResult d f y)
applyWithinFinite d f y labelsBound
  with normal? (rounds d (application f y))
... | yes normal = just (result-from-normal d f y normal)
... | no _ = nothing
-- ENDFINITEAPPLICATION

-- Every certified single-beta state fits the finite carrier above.
-- The implementation evaluates rounds on Raw internally: this is not
-- an elementary bound on every intermediate Agda runtime allocation.

private
  identity : Nf (Fin 1) 0
  identity = nf-lam (nf-U fzero) (nf-var fzero)

  argument : Nf (Fin 1) 0
  argument = nf-U fzero

  succeeds : ∀ {A : Set} → Maybe A → Bool
  succeeds nothing = false
  succeeds (just _) = true

-- A single pass returns the closed universe atom,
-- while no passes report the still-present application redex.
identity-success : succeeds (applyWithinFinite 1 identity argument (4 , refl)) ≡ true
identity-success = refl

identity-zero-fuel : applyWithinFinite 0 identity argument (4 , refl) ≡ nothing
identity-zero-fuel = refl
