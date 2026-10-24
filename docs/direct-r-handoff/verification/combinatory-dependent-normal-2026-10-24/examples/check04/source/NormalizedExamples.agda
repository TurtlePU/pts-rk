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
import NormalizedInference as NI
import NormalizedContexts as NC
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
identity-at-universe-typed = castNF identity-at-universe-type identity-at-universe

seven : NfAt empty (U zero)
seven = universeNF 7

identity-applied : NfAt empty (term (appType wf-empty U₀ (universeNF zero) seven))
identity-applied = appNF wf-empty U₀ (universeNF zero) identity-at-universe-typed seven

identity-applied-type : term (appType wf-empty U₀ (universeNF zero) seven) ≡ U zero
identity-applied-type = refl

identity-applied-computes : term identity-applied ≡ U 7
identity-applied-computes = refl

identity-computed-type : NI.tyOf wf-empty (NI.from-normal identity-applied) ≡ U zero
identity-computed-type = snd (NI.embed wf-empty tt identity-applied)

-- The dependent declaration f U₀ has become U₀, so U₇ may be paired.
dependent-pair : SubNF (extend Γf (term neutral-type)) empty
dependent-pair = pairTypedNF wf-empty σ neutral-type seven

dependent-pair-first : restrictNF dependent-pair ≡ σ
dependent-pair-first = restrict-pairTyped wf-empty σ neutral-type seven

dependent-pair-last : lastNF dependent-pair ≡ U 7
dependent-pair-last = refl

dependent-pair-eta : pairTypedNF wf-empty (restrictNF dependent-pair) neutral-type
  (lastTypedNF wf-empty neutral-type dependent-pair) ≡ dependent-pair
dependent-pair-eta = pairTyped-eta wf-empty neutral-type dependent-pair

lifted : SubNF (extend Γf (term neutral-type)) (extend empty (U zero))
lifted = liftNF wf-empty σ neutral-type

lifted-last : sub-images lifted fzero ≡ var fzero
lifted-last = refl

lifted-previous : sub-images lifted (fsuc fzero) ≡ lam (U zero) (U zero)
lifted-previous = refl

lifted-projection : composeNF (wf-extend wf-empty (universe zero))
    (projectionNF Γf (term neutral-type)) lifted
  ≡ composeNF (wf-extend wf-empty (universe zero)) σ
      (projectionNF empty (U zero))
lifted-projection = projection-lift wf-empty σ neutral-type
  (wf-extend wf-empty (universe zero))

-- The inductive-recursive context interface chooses no WF certificate.
IR-ΓA : NC.Con
IR-ΓA = NC.ext NC.ε U₀

IR-context-decodes : NC.context IR-ΓA ≡ ΓA
IR-context-decodes = refl

IR-computed-type : NC.tyOf IR-ΓA (NI.from-normal (variableNF U₀)) ≡ U zero
IR-computed-type = refl

IR-Γf : NC.Con
IR-Γf = NC.ext NC.ε arrow

IR-dependent-substitution : term (NC.actTy {Γ = IR-Γf} {Δ = NC.ε} σ neutral-type) ≡ U zero
IR-dependent-substitution = refl
