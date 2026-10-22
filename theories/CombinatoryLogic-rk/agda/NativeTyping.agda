{-# OPTIONS --cubical --safe --guardedness #-}
module NativeTyping where

-- The original six annotated PTS-rk typing rules, not a checking algorithm.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Foundations.Prelude using (isProp)
open import Cubical.Foundations.HLevels using (isPropΠ; isProp×)
open import Cubical.HITs.PropositionalTruncation.Base
  using (∥_∥₁; ∣_∣₁; squash₁)

Term : Nat → Set
Term = Raw Nat

data Context : Nat → Set where
  empty : Context zero
  extend : ∀ {n} → Context n → Term n → Context (suc n)

lookup : ∀ {n} → Context n → Fin n → Term n
lookup empty ()
lookup (extend Γ A) i = shift (caseFin i A (lookup Γ))

-- Reflexive, symmetric, transitive closure of original annotated beta steps.
data Beta {n : Nat} : Term n → Term n → Set where
  beta-refl : ∀ {t} → Beta t t
  beta-step : ∀ {t u} → Step t u → Beta t u
  beta-sym : ∀ {t u} → Beta t u → Beta u t
  beta-trans : ∀ {t u v} → Beta t u → Beta u v → Beta t v

-- BEGIN NATIVE TYPING
data Typ {n : Nat} (Γ : Context n) : Term n → Term n → Set where
  universe : (i : Nat) → Typ Γ (U i) (U zero)
  product : ∀ {A B a b} → Typ Γ A (U a)
    → Typ (extend Γ A) B (U b) → Typ Γ (pi A B) (U (max (suc a) b))
  lookup-var : (i : Fin n) → Typ Γ (var i) (lookup Γ i)
  abstraction : ∀ {A b B r} → Typ Γ A (U r)
    → Typ (extend Γ A) b B → Typ Γ (lam A b) (pi A B)
  application : ∀ {f y A B} → Typ Γ f (pi A B) → Typ Γ y A
    → Typ Γ (app f y) (substitute B y)
  conversion : ∀ {t A B r} → Typ Γ t A → Typ Γ B (U r)
    → Beta A B → Typ Γ t B
-- END NATIVE TYPING

data WellFormed : ∀ {n} → Context n → Set where
  wf-empty : WellFormed empty
  wf-extend : ∀ {n} {Γ : Context n} {A r}
    → WellFormed Γ → Typ Γ A (U r) → WellFormed (extend Γ A)

-- As in RedexRanks.v, rank is the rank of the redex head's product TYPE.
data RedexRank {n : Nat} (Γ : Context n) : Term n → Nat → Set where
  at-beta : ∀ {A b y D E r} → Typ Γ (lam A b) (pi D E)
    → Typ Γ (pi D E) (U r) → RedexRank Γ (app (lam A b) y) r
  in-pi-left : ∀ {A B r} → RedexRank Γ A r → RedexRank Γ (pi A B) r
  in-pi-right : ∀ {A B r} → RedexRank (extend Γ A) B r → RedexRank Γ (pi A B) r
  in-lam-left : ∀ {A b r} → RedexRank Γ A r → RedexRank Γ (lam A b) r
  in-lam-right : ∀ {A b r} → RedexRank (extend Γ A) b r → RedexRank Γ (lam A b) r
  in-app-left : ∀ {f y r} → RedexRank Γ f r → RedexRank Γ (app f y) r
  in-app-right : ∀ {f y r} → RedexRank Γ y r → RedexRank Γ (app f y) r

RedexBound : ∀ {n} → Context n → Term n → Nat → Set
RedexBound Γ t d = ∀ r → RedexRank Γ t r → r ≤ d

-- A syntax fibre counts proofs only propositionally, not derivation trees.
-- Its sort certificate is about the fixed type A, not a normalization witness.
NormalAt : ∀ {a} → (Fin a → Nat) → Nat → Nat → Term zero
  → Raw (Fin a) zero → Set
NormalAt labels N d A t = Normal t × ((nodes t ≡ N) ×
  (∥ Typ empty (relabel labels t) A ∥₁ ×
   ∥ Σ Nat (λ r → (r ≤ d) × Typ empty A (U r)) ∥₁))

normalAt-isProp : ∀ {a} (labels : Fin a → Nat) N d A t
  → isProp (NormalAt labels N d A t)
normalAt-isProp labels N d A t = isProp× normal-isProp
  (isProp× (isSetℕ (nodes t) N) (isProp× squash₁ squash₁))

-- A type-correct source application requires no guessed checker relation.
typed-application : ∀ {f y A B}
  → Typ empty f (pi A B) → Typ empty y A
  → Typ empty (app f y) (substitute B y)
typed-application = application
