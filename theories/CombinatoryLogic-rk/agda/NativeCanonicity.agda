{-# OPTIONS --cubical --safe --guardedness #-}
module NativeCanonicity where

-- External canonicity and nontriviality of the original annotated calculus.
-- These are Agda metatheorems, not internal PTS proofs of consistency.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction using (Normal; NotLambda)
open import NativeTyping
open import NativeAlgebra using (fin-cases)
open import NativeInversion
open import NativeConfluence
  using (normal-beta-unique; beta-to-normal; sort-not-pi; pi-injective;
         IsPi; steps-pi-parts)
open import NativeRankCoverage using (normalize-typed)
open import NativeNormalization using (nf; nf-normal; nf-typed)
open import NativeCertificates
open import FragmentEmbeddings using (Fragment; fragment-term; fragment-typing)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥; isProp⊥)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    n : Nat

  IsSort : Term n → Set
  IsSort (U i) = Unit
  IsSort (var i) = ⊥
  IsSort (pi A B) = ⊥
  IsSort (lam A b) = ⊥
  IsSort (app f y) = ⊥

sort-not-variable : {r : Nat} {i : Fin n} → Beta (U r) (var i) → ⊥
sort-not-variable e = subst IsSort (normal-beta-unique tt tt e) tt

product-not-variable : {A : Term n} {B : Term (suc n)} {i : Fin n}
  → Beta (pi A B) (var i) → ⊥
product-not-variable e = fst (steps-pi-parts (beta-to-normal e tt) tt)

SortLookups : Context n → Set
SortLookups Γ = ∀ i → Σ Nat (λ r → lookup Γ i ≡ U r)

-- A neutral normal function cannot be headed by a variable whose type is
-- a sort. Products and universe constants also have sorts, never products.
normal-nonlambda-not-function : {Γ : Context n} (t : Term n)
  {A : Term n} {B : Term (suc n)}
  → SortLookups Γ → Normal t → NotLambda t → Typ Γ t (pi A B) → ⊥
normal-nonlambda-not-function (U i) look normal head typed =
  sort-not-pi (universe-inversion typed)
normal-nonlambda-not-function (var i) look normal head typed with look i
... | r , e = sort-not-pi
  (subst (λ T → Beta T _) e (variable-inversion typed))
normal-nonlambda-not-function (pi A B) look normal head typed with pi-inversion typed
... | a , b , ha , hb , e = sort-not-pi e
normal-nonlambda-not-function (lam A b) look normal () typed
normal-nonlambda-not-function (app f y) look (nf , ny , head) outer typed
  with app-inversion typed
... | A , B , hf , hy , e = normal-nonlambda-not-function f look nf head hf

-- This context contains the arbitrary type variable X : U_0.
type-variable-context : Context 1
type-variable-context = extend empty (U zero)

type-variable-lookups : SortLookups type-variable-context
type-variable-lookups i = fin-cases
  (λ i → Σ Nat (λ r → lookup type-variable-context i ≡ U r)) i
  (zero , refl) (λ ())

normal-arbitrary-type-empty : (t : Term 1) → Normal t
  → Typ type-variable-context t (var fzero) → ⊥
normal-arbitrary-type-empty (U i) normal typed =
  sort-not-variable (universe-inversion typed)
normal-arbitrary-type-empty (var i) normal typed with type-variable-lookups i
... | r , e = sort-not-variable
  (subst (λ T → Beta T (var fzero)) e (variable-inversion typed))
normal-arbitrary-type-empty (pi A B) normal typed with pi-inversion typed
... | a , b , ha , hb , e = sort-not-variable e
normal-arbitrary-type-empty (lam A b) normal typed with lam-inversion typed
... | a , B , ha , hb , e = product-not-variable e
normal-arbitrary-type-empty (app f y) (nf , ny , head) typed with app-inversion typed
... | A , B , hf , hy , e =
  normal-nonlambda-not-function f type-variable-lookups nf head hf

-- BEGIN VOIDSEPARATION
Void : Term zero
Void = pi (U zero) (var fzero)

Void-formation : Typ empty Void (U 1)
Void-formation = product (universe zero) (lookup-var fzero)

normal-Void-empty : (t : Term zero) → Normal t → Typ empty t Void → ⊥
normal-Void-empty (U i) normal typed = sort-not-pi (universe-inversion typed)
normal-Void-empty (var ()) normal typed
normal-Void-empty (pi A B) normal typed with pi-inversion typed
... | a , b , ha , hb , e = sort-not-pi e
normal-Void-empty (lam A b) (nA , nb) typed with lam-inversion typed
... | a , B , ha , hb , e with pi-injective e
... | eA , eB = normal-arbitrary-type-empty b nb
  (conversion
    (subst (λ A → Typ (extend empty A) b B) (normal-beta-unique nA tt eA) hb)
    (lookup-var fzero) eB)
normal-Void-empty (app f y) (nf , ny , head) typed with app-inversion typed
... | A , B , hf , hy , e = normal-nonlambda-not-function f (λ ()) nf head hf

-- No supplied rank, normality or desired contradiction premise is needed.
Void-empty : {t : Term zero} → Typ empty t Void → ⊥
Void-empty typed = normal-Void-empty (nf normalized)
  (nf-normal normalized) (nf-typed normalized)
  where
  normalized = normalize-typed wf-empty typed

accepted-Void-rejected : (c : Certificate zero) → Accepted empty c
  → certificate-type c ≡ Void → ⊥
accepted-Void-rejected c accepted type-equality =
  Void-empty (subst (Typ empty (certificate-term c)) type-equality (accepted-typing accepted))
-- END VOIDSEPARATION

-- Every finite normal-code fibre of Void is empty, independently of its
-- alphabet and size grade. This excludes the all-true trivial semantics.
fragment-Void-empty : {a s : Nat} {labels : Fin a → Nat} → Fragment labels s Void → ⊥
fragment-Void-empty x = PT.rec isProp⊥ Void-empty (fragment-typing x)
