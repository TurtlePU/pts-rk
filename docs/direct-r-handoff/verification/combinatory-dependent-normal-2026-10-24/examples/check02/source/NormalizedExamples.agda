{-# OPTIONS --cubical --safe --guardedness #-}
module NormalizedExamples where

-- Regression tests use genuine dependency and the ORIGINAL PTS universes.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NormalizedSubstitution
open import NormalizedFamilies
open import NormalizedComprehension
open import NormalizedProducts
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

U₀ : TyNF empty zero
U₀ = universeNF zero

arrow : TyNF empty (suc zero)
arrow = piNF U₀ (universeNF zero)

Γf : Context (suc zero)
Γf = extend empty (term arrow)

-- f : U₀ → U₀; the normal type f U₀ becomes a redex after substitution.
neutral-type : TyNF Γf zero
neutral-type = normal-at (app (var fzero) (U zero)) (tt , tt , tt)
  ∣ application (lookup-var fzero) (universe zero) ∣₁

constant-type : NfAt empty (term arrow)
constant-type = lamNF U₀ (universeNF zero) (universeNF zero)

σ : SubNF Γf empty
σ = pairNF (terminalNF empty) (term constant-type) (normal constant-type)
  (typed constant-type)

-- BEGINNORMALDEPENDENTEXAMPLES
neutral-type-substitution : term (pullTy wf-empty σ neutral-type) ≡ U zero
neutral-type-substitution = refl
-- ENDNORMALDEPENDENTEXAMPLES

ΓA : Context (suc zero)
ΓA = extend empty (U zero)

Avar : TyNF ΓA zero
Avar = normal-at (var fzero) tt ∣ lookup-var fzero ∣₁

identity-family : TyNF ΓA (suc zero)
identity-family = piNF Avar (weakTyNF Avar)

identity-body : NfAt ΓA (term identity-family)
identity-body = lamNF Avar (weakTyNF Avar) (variableNF Avar)

polymorphic-identity : NfAt empty (term (piNF U₀ identity-family))
polymorphic-identity = lamNF U₀ identity-family identity-body

polymorphic-identity-syntax : term polymorphic-identity
  ≡ lam (U zero) (lam (var fzero) (var fzero))
polymorphic-identity-syntax = refl

identity-at-universe : NfAt empty (term (appType wf-empty U₀ identity-family U₀))
identity-at-universe = appNF wf-empty U₀ identity-family polymorphic-identity U₀

identity-at-universe-type : term (appType wf-empty U₀ identity-family U₀)
  ≡ pi (U zero) (U zero)
identity-at-universe-type = refl

identity-at-universe-computes : term identity-at-universe ≡ lam (U zero) (var fzero)
identity-at-universe-computes = refl

identity-at-universe-typed : NfAt empty (term arrow)
identity-at-universe-typed = subst (NfAt empty) identity-at-universe-type identity-at-universe

seven : NfAt empty (U zero)
seven = universeNF 7

identity-applied : NfAt empty (term (appType wf-empty U₀ (universeNF zero) seven))
identity-applied = appNF wf-empty U₀ (universeNF zero) identity-at-universe-typed seven

identity-applied-type : term (appType wf-empty U₀ (universeNF zero) seven) ≡ U zero
identity-applied-type = refl

identity-applied-computes : term identity-applied ≡ U 7
identity-applied-computes = refl
