{-# OPTIONS --cubical --safe --guardedness #-}
module NeutralProbe where
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NormalizedSubstitution
open import NormalizedFamilies
open import NormalizedComprehension
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

Γf : Context (suc zero)
Γf = extend empty (pi (U zero) (U zero))

neutral-type : TyNF Γf zero
neutral-type = normal-at (app (var fzero) (U zero)) (tt , tt , tt)
  ∣ application (lookup-var fzero) (universe zero) ∣₁

σ : SubNF Γf empty
σ = pairNF (terminalNF empty) (lam (U zero) (U zero)) (tt , tt)
  ∣ abstraction (universe zero) (universe zero) ∣₁

neutral-type-substitution : term (pullTy wf-empty σ neutral-type) ≡ U zero
neutral-type-substitution = refl
