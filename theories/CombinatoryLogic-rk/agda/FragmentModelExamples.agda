{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentModelExamples where

-- Regressions start from raw certificate data, not native typing derivations.
open import FiniteSyntax
open import NativeTyping
open import NativeCertificates
open import CertificateContexts
open import NativeAlgebra using (fin-cases)
open import NativeConfluence using (normal-results-coherent)
open import FragmentModelSoundness
open import FragmentInterpretation using (element; typeRank)
open import FragmentUniverses using (elementCarrier-normal; typeCarrier-normal; elementType)
open import FragmentPackages using (ContextElementPackage; packageContext; packageTerm; packageType)
open import BoundedReduction using (Normal; done; replace)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.FinData.Base using (toℕ)
open import Cubical.Data.Sigma.Base using (_×_)

private
  successful : ∀ {A : Set} → Maybe A → Bool
  successful nothing = false
  successful (just _) = true

identityTerm : Term zero
identityTerm = lam (U zero) (var fzero)

identityType : Term zero
identityType = pi (U zero) (U zero)

closed-identity-input : ModelInput zero zero
closed-identity-input .source = empty-context
closed-identity-input .target = empty-context
closed-identity-input .environment = empty-valuation
closed-identity-input .derivation = identity-certificate

closed-identity-accepted : InputAccepted closed-identity-input
closed-identity-accepted = tt , tt , (λ ()) , tt , refl , (refl , refl) , (refl , refl)

closed-identity-checks : successful (check-and-interpret closed-identity-input) ≡ true
closed-identity-checks = refl

closed-identity-output : ModelOutput closed-identity-input
closed-identity-output = model-soundness closed-identity-input closed-identity-accepted

closed-identity-value : model-value closed-identity-input closed-identity-output ≡ identityTerm
closed-identity-value = normal-results-coherent beta-refl
  (model-reduces closed-identity-input closed-identity-output) done
  (elementCarrier-normal (element closed-identity-output)) (tt , tt)

closed-identity-exact-type : Typ empty identityTerm identityType
closed-identity-exact-type = subst (λ t → Typ empty t identityType) closed-identity-value
  (model-exact-typing closed-identity-input closed-identity-accepted closed-identity-output)

-- In source context X : U₀, this raw tree certifies λ x : X. x.
dependent-identity-certificate : Certificate 1
dependent-identity-certificate =
  abstraction-rule (var fzero) (var fzero) (var (fsuc fzero)) zero
    (variable-rule fzero (U zero)) (variable-rule fzero (var (fsuc fzero)))

universe-environment : ValuationCertificate 1 zero
universe-environment .valuation-images _ = U zero
universe-environment .valuation-proofs _ = sort-rule zero

universe-environment-accepted :
  ValuationAccepted (certificate-context one-variable-context) empty universe-environment
universe-environment-accepted i = fin-cases
  (λ i → Accepted empty (valuation-proofs universe-environment i)
    × Matches (valuation-proofs universe-environment i) (valuation-images universe-environment i)
      (replace (valuation-images universe-environment)
        (lookup (certificate-context one-variable-context) i)))
  i (tt , refl , refl) (λ ())

dependent-input : ModelInput 1 zero
dependent-input .source = one-variable-context
dependent-input .target = empty-context
dependent-input .environment = universe-environment
dependent-input .derivation = dependent-identity-certificate

dependent-accepted : InputAccepted dependent-input
dependent-accepted = (tt , tt , refl , refl) , tt , universe-environment-accepted ,
  refl , refl , (refl , refl) , (refl , refl)

dependent-checks : successful (check-and-interpret dependent-input) ≡ true
dependent-checks = refl

dependent-substitution-term : instantiated-term dependent-input ≡ identityTerm
dependent-substitution-term = refl

dependent-substitution-type : instantiated-type dependent-input ≡ identityType
dependent-substitution-type = refl

dependent-output : ModelOutput dependent-input
dependent-output = model-soundness dependent-input dependent-accepted

dependent-value : model-value dependent-input dependent-output ≡ identityTerm
dependent-value = normal-results-coherent beta-refl
  (model-reduces dependent-input dependent-output) done
  (elementCarrier-normal (element dependent-output)) (tt , tt)

dependent-type : model-type dependent-input dependent-output ≡ identityType
dependent-type = normal-results-coherent beta-refl
  (model-type-reduces dependent-input dependent-output) done
  (typeCarrier-normal (elementType (element dependent-output))) (tt , tt)

dependent-exact-type : Typ empty identityTerm identityType
dependent-exact-type = subst (λ t → Typ empty t identityType) dependent-value
  (model-exact-typing dependent-input dependent-accepted dependent-output)

dependent-package : ContextElementPackage {a = model-alphabet dependent-input} toℕ zero
  (model-size dependent-input dependent-output) (typeRank dependent-output)
dependent-package = model-package dependent-input dependent-accepted dependent-output

dependent-package-context : packageContext dependent-package ≡ empty
dependent-package-context = model-package-context dependent-input dependent-accepted dependent-output

dependent-package-term : packageTerm dependent-package ≡ identityTerm
dependent-package-term = model-package-term dependent-input dependent-accepted dependent-output ∙ dependent-value

dependent-package-type : packageType dependent-package ≡ identityType
dependent-package-type = model-package-type dependent-input dependent-accepted dependent-output ∙ dependent-type

-- The target context is also part of the finite package, not an uncounted
-- parameter: here X : U₀ is interpreted as Y : U₀ in a nonempty target.
variable-environment : ValuationCertificate 1 1
variable-environment .valuation-images _ = var fzero
variable-environment .valuation-proofs _ = variable-rule fzero (U zero)

variable-environment-accepted : ValuationAccepted
  (certificate-context one-variable-context) (certificate-context one-variable-context) variable-environment
variable-environment-accepted i = fin-cases
  (λ i → Accepted (certificate-context one-variable-context) (valuation-proofs variable-environment i)
    × Matches (valuation-proofs variable-environment i) (valuation-images variable-environment i)
      (replace (valuation-images variable-environment)
        (lookup (certificate-context one-variable-context) i)))
  i (refl , refl , refl) (λ ())

open-input : ModelInput 1 1
open-input .source = one-variable-context
open-input .target = one-variable-context
open-input .environment = variable-environment
open-input .derivation = dependent-identity-certificate

open-accepted : InputAccepted open-input
open-accepted = (tt , tt , refl , refl) , (tt , tt , refl , refl) , variable-environment-accepted ,
  refl , refl , (refl , refl) , (refl , refl)

open-checks : successful (check-and-interpret open-input) ≡ true
open-checks = refl

open-output : ModelOutput open-input
open-output = model-soundness open-input open-accepted

open-package-context : packageContext (model-package open-input open-accepted open-output)
  ≡ extend empty (U zero)
open-package-context = model-package-context open-input open-accepted open-output

-- The context and environment are valid, but the variable's claimed type is
-- not its lookup type. Rejection occurs before normalization is requested.
wrong-variable-input : ModelInput 1 zero
wrong-variable-input .source = one-variable-context
wrong-variable-input .target = empty-context
wrong-variable-input .environment = universe-environment
wrong-variable-input .derivation = variable-rule fzero (U 1)

wrong-variable-input-rejected : check-and-interpret wrong-variable-input ≡ nothing
wrong-variable-input-rejected = refl

-- This derivation is valid, but its environment tree certifies U₁ instead
-- of the declared image U₀. Independent valuation checking rejects it.
wrong-environment-input : ModelInput 1 zero
wrong-environment-input .source = one-variable-context
wrong-environment-input .target = empty-context
wrong-environment-input .environment .valuation-images _ = U zero
wrong-environment-input .environment .valuation-proofs _ = sort-rule 1
wrong-environment-input .derivation = dependent-identity-certificate

wrong-environment-rejected : check-and-interpret wrong-environment-input ≡ nothing
wrong-environment-rejected = refl
