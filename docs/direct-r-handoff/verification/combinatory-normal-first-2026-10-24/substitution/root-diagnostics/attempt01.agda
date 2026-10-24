{-# OPTIONS --cubical --safe --guardedness #-}
module NormalizedSubstitution where

-- Normal substitutions for the ORIGINAL dependent typing relation.
-- Images are canonical; typing witnesses are propositionally truncated.
-- Category equations below are literal paths, not new quotient constructors.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NativeSubstitution using (TypedSub)
open import NativeAlgebra using (step-rename; fin-cases)
open import NativePreservation using (type-correct; subject-reductions)
open import NativeConfluence using (steps-beta)
open import NativeRankCoverage using (normalize-typed)
open import NativeNormalization
open import NativeCertificates using (term-discrete)
open import NativeValuations
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Foundations.Prelude using (isProp; isProp→isSet)
open import Cubical.Foundations.HLevels using (isPropΠ; isProp×; isSetΠ)
open import Cubical.Relation.Nullary using (Discrete→isSet)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    k l m n : Nat

-- Reducing every substitution image reduces its action, including under
-- annotations and binders. No typing or normality premise is needed here.
lift-image-steps : {σ τ : Fin m → Term n}
  → (∀ i → Steps (σ i) (τ i))
  → ∀ i → Steps (liftSubstitution σ i) (liftSubstitution τ i)
lift-image-steps {σ = σ} {τ} h i = fin-cases
  (λ i → Steps (liftSubstitution σ i) (liftSubstitution τ i)) i done
  (λ j → steps-map shift (step-rename fsuc) (h j))

replace-image-steps : {σ τ : Fin m → Term n}
  → (∀ i → Steps (σ i) (τ i)) → (t : Term m)
  → Steps (replace σ t) (replace τ t)
replace-image-steps h (U i) = done
replace-image-steps h (var i) = h i
replace-image-steps h (pi A B) = steps-pi (replace-image-steps h A)
  (replace-image-steps (lift-image-steps h) B)
replace-image-steps h (lam A b) = steps-lam (replace-image-steps h A)
  (replace-image-steps (lift-image-steps h) b)
replace-image-steps h (app f x) = steps-app (replace-image-steps h f)
  (replace-image-steps h x)

module Normalize {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) where

  result : (i : Fin m) → _
  result i = normalize-typed wf (images-typed σ i)

  normal-images : Fin m → Term n
  normal-images i = nf (result i)

  image-steps : ∀ i → Steps (images σ i) (normal-images i)
  image-steps i = nf-reduces (result i)

  -- The dependent type changes when earlier images normalize. Reduction
  -- of the ORIGINAL substituted lookup supplies its well-sortedness.
  normal-typing : TypedSub Γ Δ normal-images
  normal-typing i = conversion (nf-typed (result i))
    (subject-reductions wf (snd (type-correct wf (images-typed σ i)))
      (replace-image-steps image-steps (lookup Γ i)))
    (steps-beta (replace-image-steps image-steps (lookup Γ i)))

  valuation-nf : Valuation Γ Δ
  valuation-nf = valuation normal-images normal-typing

  images-normal : ∀ i → Normal (normal-images i)
  images-normal i = nf-normal (result i)

  equivalent : Equivalent valuation-nf σ
  equivalent i = beta-sym (steps-beta (image-steps i))

normalize-valuation : {Γ : Context m} {Δ : Context n}
  → WellFormed Δ → Valuation Γ Δ → Valuation Γ Δ
normalize-valuation = Normalize.valuation-nf

normalize-coherent : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ τ : Valuation Γ Δ) → Equivalent σ τ
  → Same (normalize-valuation wf σ) (normalize-valuation wf τ)
normalize-coherent wf σ τ h i = normalization-coherent
  (Normalize.result wf σ i) (Normalize.result wf τ i) (h i)

normalize-on-normal : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) → (∀ i → Normal (images σ i))
  → Same (normalize-valuation wf σ) σ
normalize-on-normal wf σ h i = normal-convertible-unique
  (Normalize.result wf σ i) (h i) beta-refl

-- BEGINNORMALSUBSTITUTION
SubNF : Context m → Context n → Set
SubNF Γ Δ = Σ (Fin _ → Term _) (λ σ →
  (∀ i → Normal (σ i)) × ∥ TypedSub Γ Δ σ ∥₁)

sub-images : {Γ : Context m} {Δ : Context n} → SubNF Γ Δ → Fin m → Term n
sub-images = fst

sub-path : {Γ : Context m} {Δ : Context n} {σ τ : SubNF Γ Δ}
  → (∀ i → sub-images σ i ≡ sub-images τ i) → σ ≡ τ
sub-path e = Σ≡Prop (λ _ → isProp× (isPropΠ (λ _ → normal-isProp)) squash₁)
  (funExt e)

sub-isSet : {Γ : Context m} {Δ : Context n} → isSet (SubNF Γ Δ)
sub-isSet = isSetΣ (isSetΠ (λ _ → Discrete→isSet term-discrete))
  (λ _ → isProp→isSet (isProp× (isPropΠ (λ _ → normal-isProp)) squash₁))

pack : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) → (∀ i → Normal (images σ i)) → SubNF Γ Δ
pack σ h = images σ , h , ∣ images-typed σ ∣₁

normalizeSub : {Γ : Context m} {Δ : Context n}
  → WellFormed Δ → Valuation Γ Δ → SubNF Γ Δ
normalizeSub wf σ = pack (normalize-valuation wf σ) (Normalize.images-normal wf σ)

idNF : (Γ : Context n) → SubNF Γ Γ
idNF Γ = pack (identity Γ) (λ i → tt)

composeNF : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  → WellFormed Θ → SubNF Γ Δ → SubNF Δ Θ → SubNF Γ Θ
composeNF wf (σ , ns , hs) (τ , nt , ht) = PT.rec2→Set sub-isSet
  (λ ps pt → normalizeSub wf (compose (valuation σ ps) (valuation τ pt)))
  (λ ps qs pt qt → sub-path (normalize-coherent wf _ _ (λ i → beta-refl))) hs ht
-- ENDNORMALSUBSTITUTION

compose-normalized-assoc : {Γ : Context k} {Δ : Context l}
  {Θ : Context m} {Ξ : Context n}
  (wfΘ : WellFormed Θ) (wfΞ : WellFormed Ξ)
  (σ : Valuation Γ Δ) (τ : Valuation Δ Θ) (υ : Valuation Θ Ξ)
  → Same
    (normalize-valuation wfΞ (compose (normalize-valuation wfΘ (compose σ τ)) υ))
    (normalize-valuation wfΞ (compose σ (normalize-valuation wfΞ (compose τ υ))))
compose-normalized-assoc wfΘ wfΞ σ τ υ = normalize-coherent wfΞ _ _
  (equivalent-trans
    (compose-equivalent (Normalize.equivalent wfΘ (compose σ τ)) (λ i → beta-refl))
    (equivalent-trans (same-equivalent (compose-associative σ τ υ))
      (compose-equivalent (λ i → beta-refl)
        (equivalent-sym (Normalize.equivalent wfΞ (compose τ υ))))))

identity-left : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) → composeNF wf (idNF Γ) σ ≡ σ
identity-left {Γ = Γ} wf (σ , ns , hs) = PT.elim
  (λ h → sub-isSet (composeNF wf (idNF Γ) (σ , ns , h)) (σ , ns , h))
  (λ ps → sub-path (λ i → normal-convertible-unique
    (Normalize.result wf (compose (identity Γ) (valuation σ ps)) i) (ns i) beta-refl)) hs

identity-right : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) → composeNF wf σ (idNF Δ) ≡ σ
identity-right {Δ = Δ} wf (σ , ns , hs) = PT.elim
  (λ h → sub-isSet (composeNF wf (σ , ns , h) (idNF Δ)) (σ , ns , h))
  (λ ps → sub-path (λ i → normal-convertible-unique
    (Normalize.result wf (compose (valuation σ ps) (identity Δ)) i) (ns i)
    (subst (Beta _) (compose-right-identity (valuation σ ps) i) beta-refl))) hs

associative : {Γ : Context k} {Δ : Context l} {Θ : Context m} {Ξ : Context n}
  (wfΘ : WellFormed Θ) (wfΞ : WellFormed Ξ)
  (σ : SubNF Γ Δ) (τ : SubNF Δ Θ) (υ : SubNF Θ Ξ)
  → composeNF wfΞ (composeNF wfΘ σ τ) υ
    ≡ composeNF wfΞ σ (composeNF wfΞ τ υ)
associative wfΘ wfΞ (σ , ns , hs) (τ , nt , ht) (υ , nu , hu) = PT.elim3
  (λ ps pt pu → sub-isSet
    (composeNF wfΞ (composeNF wfΘ (σ , ns , ps) (τ , nt , pt)) (υ , nu , pu))
    (composeNF wfΞ (σ , ns , ps) (composeNF wfΞ (τ , nt , pt) (υ , nu , pu))))
  (λ ps pt pu → sub-path (compose-normalized-assoc wfΘ wfΞ
    (valuation σ ps) (valuation τ pt) (valuation υ pu))) hs ht hu

normal-retraction : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (normal : ∀ i → Normal (images σ i))
  → normalizeSub wf σ ≡ pack σ normal
normal-retraction wf σ normal = sub-path (normalize-on-normal wf σ normal)

normalizeSub-coherent : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ τ : Valuation Γ Δ) → Equivalent σ τ
  → normalizeSub wf σ ≡ normalizeSub wf τ
normalizeSub-coherent wf σ τ h = sub-path (normalize-coherent wf σ τ h)
