{-# OPTIONS --cubical --safe --guardedness #-}
module TypedNormalFibres where

open import FiniteSyntax
open import FiniteBounds using (tetration)
open import FiniteCarriers using (AtMost; subtype-finite)
open import NormalForms using (ExactNf; erase; closed-exact-normal-bound;
  from-normal; erase-from-normal)
open import NativeTyping using (Term; NormalAt; normalAt-isProp; Typ; empty)
open import BoundedReduction using (Normal)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)

-- BEGINTYPEDNORMALFIBRE
-- labels names the fixed alphabet; A is an original closed annotated type.
-- Length is exactly N; d bounds the rank of A, not just redexes (there are none).
TypedNormal : ∀ {a} → (labels : Fin a → Nat) → (N d : Nat) → Term 0 → Set
TypedNormal {a} labels N d A = Σ (ExactNf a 0 N)
  (λ t → NormalAt labels N d A (erase (Fin a) (fst t)))

typed-normal-bound : ∀ {a} (labels : Fin a → Nat) (N d : Nat) (A : Term 0)
  → a ≤ N → AtMost (TypedNormal labels N d A)
      (tetration (4 · N + 4) (d + 3))
typed-normal-bound {a} labels N d A p = subtype-finite
  (λ t → NormalAt labels N d A (erase (Fin a) (fst t)))
  (λ t → normalAt-isProp labels N d A (erase (Fin a) (fst t)))
  (closed-exact-normal-bound a d N p)
-- ENDTYPEDNORMALFIBRE

-- Every original typed normal input over this alphabet enters the fibre.
pack-typed-normal : ∀ {a N d r A} (labels : Fin a → Nat)
  (t : Raw (Fin a) 0) → Normal t → nodes t ≡ N
  → Typ empty (relabel labels t) A → Typ empty A (U r) → r ≤ d
  → TypedNormal labels N d A
pack-typed-normal {a} {N} {d} {r} {A} labels t nf length typed sorted bound =
  (from-normal t nf , cong nodes recovers ∙ length)
  , subst (NormalAt labels N d A) (sym recovers)
      (nf , length , ∣ typed ∣₁ , ∣ r , bound , sorted ∣₁)
  where
  recovers : erase (Fin a) (from-normal t nf) ≡ t
  recovers = erase-from-normal t nf
