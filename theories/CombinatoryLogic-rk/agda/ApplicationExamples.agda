{-# OPTIONS --cubical --safe --guardedness #-}
module ApplicationExamples where

-- Executable dependent and conversion-rule regressions for the total API.
-- Every premise is supplied by the original PTS typing rules.
open import FiniteSyntax
open import NormalForms using (nf-U; nf-var; nf-lam)
open import BoundedReduction using (rounds; beta; shift; Normal)
open import NativeTyping
open import NativeAlgebra using (beta-pi)
open import NativePreservation using (rounds-typed)
open import NativeSafety using (bound-to-safe; safe-to-bound)
open import NativeDescent using (bounded-rounds-normal; normal-application-rank-bound)
open import TypedApplication
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁)

-- (λ A : U₀. λ x : A. x) U₀ has dependent result type
-- (Π x : A. A)[A := U₀], literally Π x : U₀. U₀.
polymorphic-input : TypedInputs 1
polymorphic-input .labels _ = 0
polymorphic-input .d = 1
polymorphic-input .X = U 0
polymorphic-input .Y = pi (var fzero) (var (fsuc fzero))
polymorphic-input .f = nf-lam (nf-U fzero)
  (nf-lam (nf-var fzero) (nf-var fzero))
polymorphic-input .y = nf-U fzero
polymorphic-input .function-typed = ∣ abstraction (universe 0)
  (abstraction (lookup-var fzero) (lookup-var fzero)) ∣₁
polymorphic-input .argument-typed = ∣ universe 0 ∣₁
polymorphic-input .function-rank = ∣ product (universe 0)
  (product (lookup-var fzero) (lookup-var (fsuc fzero))) ∣₁
polymorphic-input .alphabet-bound = 6 , refl

polymorphic-computes :
  outputTerm polymorphic-input (fst (applyTypedWithin polymorphic-input))
    ≡ lam (U 0) (var fzero)
polymorphic-computes = output-rounds polymorphic-input

polymorphic-result-type : outputType polymorphic-input ≡ pi (U 0) (U 0)
polymorphic-result-type = refl

polymorphic-output-typed : ∥ Typ empty (lam (U 0) (var fzero)) (pi (U 0) (U 0)) ∥₁
polymorphic-output-typed = subst
  (λ t → ∥ Typ empty t (pi (U 0) (U 0)) ∥₁)
  polymorphic-computes (snd (applyTypedWithin polymorphic-input))

-- The second input uses the native conversion rule genuinely: its function
-- is annotated with U₀, while its supplied domain is the reducible R below.
reducible-domain : Term 0
reducible-domain = app (lam (U 0) (var fzero)) (U 0)

reducible-domain-typed : Typ empty reducible-domain (U 0)
reducible-domain-typed = application
  (abstraction (universe 0) (lookup-var fzero)) (universe 0)

conversion-input : TypedInputs 1
conversion-input .labels _ = 0
conversion-input .d = 1
conversion-input .X = reducible-domain
conversion-input .Y = U 0
conversion-input .f = nf-lam (nf-U fzero) (nf-var fzero)
conversion-input .y = nf-U fzero
conversion-input .function-typed = ∣ conversion
  (abstraction (universe 0) (lookup-var fzero))
  (product reducible-domain-typed (universe 0))
  (beta-pi (beta-sym (beta-step beta)) beta-refl) ∣₁
conversion-input .argument-typed = ∣ conversion
  (universe 0) reducible-domain-typed (beta-sym (beta-step beta)) ∣₁
conversion-input .function-rank = ∣ product reducible-domain-typed (universe 0) ∣₁
conversion-input .alphabet-bound = 4 , refl

conversion-computes :
  outputTerm conversion-input (fst (applyTypedWithin conversion-input)) ≡ U 0
conversion-computes = output-rounds conversion-input

conversion-output-typed : ∥ Typ empty (U 0) (U 0) ∥₁
conversion-output-typed = subst (λ t → ∥ Typ empty t (U 0) ∥₁)
  conversion-computes (snd (applyTypedWithin conversion-input))

-- A beta redex in a lambda annotation is normalized too. Subject reduction
-- retains the exact original (unreduced) dependent product type.
annotation-input : Term 0
annotation-input = lam reducible-domain (var fzero)

annotation-typed : Typ empty annotation-input
  (pi reducible-domain (shift reducible-domain))
annotation-typed = abstraction reducible-domain-typed (lookup-var fzero)

domain-rank-bound : RedexBound empty reducible-domain 1
domain-rank-bound = normal-application-rank-bound wf-empty (tt , tt) tt
  (pi (U 0) (U 0) , abstraction (universe 0) (lookup-var fzero) ,
    product (universe 0) (universe 0))

annotation-rank-bound : RedexBound empty annotation-input 1
annotation-rank-bound = safe-to-bound
  (bound-to-safe reducible-domain wf-empty reducible-domain-typed domain-rank-bound , tt)

annotation-normalizes : Normal (rounds 1 annotation-input)
annotation-normalizes = bounded-rounds-normal 1 wf-empty annotation-typed annotation-rank-bound

annotation-computes : rounds 1 annotation-input ≡ lam (U 0) (var fzero)
annotation-computes = refl

annotation-output-typed : Typ empty (lam (U 0) (var fzero))
  (pi reducible-domain (shift reducible-domain))
annotation-output-typed = rounds-typed 1 wf-empty annotation-typed
