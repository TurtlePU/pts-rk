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
open import NativeInversion using (beta-path)
open import NativeRankCoverage using (normalize-typed)
open import NativeNormalization
open import NativeCertificates using (term-discrete)
open import NativeValuations
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Foundations.Prelude using (isProp; isProp→isSet)
open import Cubical.Foundations.HLevels using (isPropΠ; isProp×; isSetΠ; isSetRetract)
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
record SubNF (Γ : Context m) (Δ : Context n) : Set where
  constructor sub
  field
    sub-images : Fin m → Term n
    sub-normal : ∀ i → Normal (sub-images i)
    sub-typed : ∥ TypedSub Γ Δ sub-images ∥₁
open SubNF public

sub-view : {Γ : Context m} {Δ : Context n} → SubNF Γ Δ
  → Σ (Fin m → Term n) (λ σ → (∀ i → Normal (σ i)) × ∥ TypedSub Γ Δ σ ∥₁)
sub-view (sub σ ns hs) = σ , ns , hs

sub-from-view : {Γ : Context m} {Δ : Context n}
  → Σ (Fin m → Term n) (λ σ → (∀ i → Normal (σ i)) × ∥ TypedSub Γ Δ σ ∥₁)
  → SubNF Γ Δ
sub-from-view (σ , ns , hs) = sub σ ns hs

sub-path : {Γ : Context m} {Δ : Context n} {σ τ : SubNF Γ Δ}
  → (∀ i → sub-images σ i ≡ sub-images τ i) → σ ≡ τ
sub-path {σ = σ} {τ} e = cong sub-from-view
  (Σ≡Prop (λ _ → isProp× (isPropΠ (λ _ → normal-isProp)) squash₁)
    {u = sub-view σ} {v = sub-view τ} (funExt e))

sub-isSet : {Γ : Context m} {Δ : Context n} → isSet (SubNF Γ Δ)
sub-isSet = isSetRetract sub-view sub-from-view (λ _ → refl)
  (isSetΣ (isSetΠ (λ _ → Discrete→isSet term-discrete))
    (λ _ → isProp→isSet (isProp× (isPropΠ (λ _ → normal-isProp)) squash₁)))

pack : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) → (∀ i → Normal (images σ i)) → SubNF Γ Δ
pack σ h = sub (images σ) h ∣ images-typed σ ∣₁

normalizeSub : {Γ : Context m} {Δ : Context n}
  → WellFormed Δ → Valuation Γ Δ → SubNF Γ Δ
normalizeSub wf σ = pack (normalize-valuation wf σ) (Normalize.images-normal wf σ)

idNF : (Γ : Context n) → SubNF Γ Γ
idNF Γ = pack (identity Γ) (λ i → tt)

private
  -- Point clauses compute directly; no product/truncation equivalence is
  -- expanded when proving the category laws on concrete typing witnesses.
  rec2-set : {A B C : Set} → isSet C → (f : A → B → C)
    → (∀ a a′ b b′ → f a b ≡ f a′ b′) → ∥ A ∥₁ → ∥ B ∥₁ → C
  rec2-set cset f coherent x y = PT.rec→Set cset
    (λ a → PT.rec→Set cset (f a) (coherent a a) y)
    (λ a a′ → PT.elim (λ _ → cset _ _)
      (λ b → coherent a a′ b b) y) x

composeNF : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  → WellFormed Θ → SubNF Γ Δ → SubNF Δ Θ → SubNF Γ Θ
composeNF {Γ = Γ} {Δ} {Θ} wf (sub σ ns hs) (sub τ nt ht) = rec2-set sub-isSet
  (λ ps pt → normalizeSub wf
    (compose (valuation {Γ = Γ} {Δ = Δ} σ ps) (valuation {Γ = Δ} {Δ = Θ} τ pt)))
  (λ ps qs pt qt → sub-path (normalize-coherent wf
    (compose (valuation {Γ = Γ} {Δ = Δ} σ ps) (valuation {Γ = Δ} {Δ = Θ} τ pt))
    (compose (valuation {Γ = Γ} {Δ = Δ} σ qs) (valuation {Γ = Δ} {Δ = Θ} τ qt))
    (λ i → beta-refl))) hs ht
-- ENDNORMALSUBSTITUTION

compose-normalized-assoc : {Γ : Context k} {Δ : Context l}
  {Θ : Context m} {Ξ : Context n}
  (wfΘ : WellFormed Θ) (wfΞ : WellFormed Ξ)
  (σ : Valuation Γ Δ) (τ : Valuation Δ Θ) (υ : Valuation Θ Ξ)
  → Same
    (normalize-valuation wfΞ (compose (normalize-valuation wfΘ (compose σ τ)) υ))
    (normalize-valuation wfΞ (compose σ (normalize-valuation wfΞ (compose τ υ))))
compose-normalized-assoc wfΘ wfΞ σ τ υ = normalize-coherent wfΞ
  (compose (normalize-valuation wfΘ (compose σ τ)) υ)
  (compose σ (normalize-valuation wfΞ (compose τ υ)))
  (λ i → beta-trans (act-beta υ (Normalize.equivalent wfΘ (compose σ τ) i))
    (beta-trans (beta-path (act-compose τ υ (images σ i)))
      (equivalent-action {σ = compose τ υ} {τ = normalize-valuation wfΞ (compose τ υ)}
        (λ j → beta-sym (Normalize.equivalent wfΞ (compose τ υ) j)) (images σ i))))

identity-left : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) → composeNF wf (idNF Γ) σ ≡ σ
identity-left {Γ = Γ} wf (sub σ ns hs) = PT.elim
  (λ h → sub-isSet (composeNF wf (idNF Γ) (sub σ ns h)) (sub σ ns h))
  (λ ps → sub-path (λ i → normal-convertible-unique
    (Normalize.result wf (compose (identity Γ) (valuation σ ps)) i) (ns i) beta-refl)) hs

identity-right : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) → composeNF wf σ (idNF Δ) ≡ σ
identity-right {Γ = Γ} {Δ} wf (sub σ ns hs) = PT.elim
  (λ h → sub-isSet (composeNF wf (sub σ ns h) (idNF Δ)) (sub σ ns h))
  (λ ps → sub-path (λ i → normal-convertible-unique
    (Normalize.result wf (compose (valuation {Γ = Γ} {Δ = Δ} σ ps) (identity Δ)) i) (ns i)
    (beta-path (compose-right-identity (valuation {Γ = Γ} {Δ = Δ} σ ps) i)))) hs

associative : {Γ : Context k} {Δ : Context l} {Θ : Context m} {Ξ : Context n}
  (wfΘ : WellFormed Θ) (wfΞ : WellFormed Ξ)
  (σ : SubNF Γ Δ) (τ : SubNF Δ Θ) (υ : SubNF Θ Ξ)
  → composeNF wfΞ (composeNF wfΘ σ τ) υ
    ≡ composeNF wfΞ σ (composeNF wfΞ τ υ)
associative {Γ = Γ} {Δ} {Θ} {Ξ} wfΘ wfΞ (sub σ ns hs) (sub τ nt ht) (sub υ nu hu) = PT.elim3
  (λ ps pt pu → sub-isSet
    (composeNF wfΞ (composeNF wfΘ (sub σ ns ps) (sub τ nt pt)) (sub υ nu pu))
    (composeNF wfΞ (sub σ ns ps) (composeNF wfΞ (sub τ nt pt) (sub υ nu pu))))
  (λ ps pt pu → sub-path (compose-normalized-assoc wfΘ wfΞ
    (valuation {Γ = Γ} {Δ = Δ} σ ps) (valuation {Γ = Δ} {Δ = Θ} τ pt)
    (valuation {Γ = Θ} {Δ = Ξ} υ pu))) hs ht hu

normal-retraction : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (normal : ∀ i → Normal (images σ i))
  → normalizeSub wf σ ≡ pack σ normal
normal-retraction wf σ normal = sub-path (normalize-on-normal wf σ normal)

normalizeSub-coherent : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ τ : Valuation Γ Δ) → Equivalent σ τ
  → normalizeSub wf σ ≡ normalizeSub wf τ
normalizeSub-coherent wf σ τ h = sub-path (normalize-coherent wf σ τ h)
