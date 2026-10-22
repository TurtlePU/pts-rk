{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentApplication where

-- Application closes the finite normal fibres at an explicitly larger grade.
open import FiniteSyntax
open import FiniteBounds using (tower; tetration; tower-monotone)
open import FiniteCarriers using (AtMost)
open import NormalForms using (erase)
open import FiniteApplication using (application; inputSize; result-recovers)
open import FragmentEmbeddings
open import TypedApplication
import NativeTyping as Native
open import NativeAlgebra using (beta-app)
open import NativeConfluence using (normal-results-coherent; steps-beta)
open import NativeDescent using (normal-application-rank-bound)
open import NativeNormalization using (reachable-invariant)
open import BoundedReduction using (Normal; rounds; Steps; substitute)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; ≤-+-≤; suc-≤-suc)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; squash₁; rec3)

fragment-inputs : ∀ {a s t X Y} (labels : Fin a → Nat) (d : Nat)
  (f : Fragment labels s (pi X Y)) (y : Fragment labels t X)
  → ∥ Native.Typ Native.empty (pi X Y) (U d) ∥₁
  → a ≤ inputSize (fragment-nf f) (fragment-nf y) → TypedInputs a
fragment-inputs {X = X} {Y} labels d f y hp small = record
  { labels = labels ; d = d ; X = X ; Y = Y
  ; f = fragment-nf f ; y = fragment-nf y
  ; function-typed = fragment-typing f ; argument-typed = fragment-typing y
  ; function-rank = hp ; alphabet-bound = small }

application-grade-bound : ∀ {a labels s t X Y}
  (f : Fragment {a} labels s (pi X Y)) (y : Fragment labels t X)
  → inputSize (fragment-nf f) (fragment-nf y) ≤ suc (s + t)
application-grade-bound f y = suc-≤-suc (≤-+-≤ (fragment-bound f) (fragment-bound y))

-- BEGINFRAGMENTAPPLICATION
apply-fragment : ∀ {a s t X Y} (labels : Fin a → Nat) (d : Nat)
  (f : Fragment labels s (pi X Y)) (y : Fragment labels t X)
  → ∥ Native.Typ Native.empty (pi X Y) (U d) ∥₁
  → a ≤ inputSize (fragment-nf f) (fragment-nf y)
  → Fragment labels (tower d (suc (s + t))) (substitute Y (fragment-term y))
apply-fragment labels d f y hp small =
  (fst (fst result) , ≤-trans (snd (fst result))
    (tower-monotone d (application-grade-bound f y))) , typed
  where
  inputs = fragment-inputs labels d f y hp small
  result = fst (applyTypedWithin inputs)
  typed = snd (applyTypedWithin inputs)
-- ENDFRAGMENTAPPLICATION

apply-fragment-raw : ∀ {a s t X Y} (labels : Fin a → Nat) (d : Nat)
  (f : Fragment labels s (pi X Y)) (y : Fragment labels t X)
  (hp : ∥ Native.Typ Native.empty (pi X Y) (U d) ∥₁)
  (small : a ≤ inputSize (fragment-nf f) (fragment-nf y))
  → fragment-raw (apply-fragment labels d f y hp small)
      ≡ rounds d (application (fragment-nf f) (fragment-nf y))
apply-fragment-raw labels d f y hp small = result-recovers d
  (fragment-nf f) (fragment-nf y)
  (input-normalizes (fragment-inputs labels d f y hp small))

apply-fragment-reduces : ∀ {a s t X Y} (labels : Fin a → Nat) (d : Nat)
  (f : Fragment labels s (pi X Y)) (y : Fragment labels t X)
  (hp : ∥ Native.Typ Native.empty (pi X Y) (U d) ∥₁)
  (small : a ≤ inputSize (fragment-nf f) (fragment-nf y))
  → Steps (app (fragment-term f) (fragment-term y))
      (fragment-term (apply-fragment labels d f y hp small))
apply-fragment-reduces labels d f y hp small =
  output-reduces (fragment-inputs labels d f y hp small)

apply-fragment-finite : ∀ {a s t X Y} (labels : Fin a → Nat) (d : Nat)
  (f : Fragment labels s (pi X Y)) (y : Fragment labels t X)
  → a ≤ inputSize (fragment-nf f) (fragment-nf y)
  → AtMost (Fragment labels (tower d (suc (s + t)))
      (substitute Y (fragment-term y)))
      (tetration (4 · suc (s + t) + 4) (d + 3))
apply-fragment-finite labels d f y small = fragment-knuth-bound labels d _ _
  (≤-trans small (application-grade-bound f y))

-- Conversion-compatible inputs yield identical native normal outputs, even
-- when their types and size/rank grades differ. No injective label dictionary
-- is assumed, so equality here concerns decoded native syntax.
apply-fragment-coherent : ∀ {a s t u v X Y X′ Y′}
  (labels : Fin a → Nat) (d e : Nat)
  (f : Fragment labels s (pi X Y)) (y : Fragment labels t X)
  (g : Fragment labels u (pi X′ Y′)) (z : Fragment labels v X′)
  (hp : ∥ Native.Typ Native.empty (pi X Y) (U d) ∥₁)
  (hq : ∥ Native.Typ Native.empty (pi X′ Y′) (U e) ∥₁)
  (small : a ≤ inputSize (fragment-nf f) (fragment-nf y))
  (small′ : a ≤ inputSize (fragment-nf g) (fragment-nf z))
  → FragmentEq f g → FragmentEq y z
  → fragment-term (apply-fragment labels d f y hp small)
      ≡ fragment-term (apply-fragment labels e g z hq small′)
apply-fragment-coherent labels d e f y g z hp hq small small′ ef ey =
  normal-results-coherent (beta-app ef ey)
    (apply-fragment-reduces labels d f y hp small)
    (apply-fragment-reduces labels e g z hq small′)
    (fragment-normal (apply-fragment labels d f y hp small))
    (fragment-normal (apply-fragment labels e g z hq small′))

-- Increasing input budgets leaves the actual finite-alphabet output intact.
apply-embedding-raw : ∀ {a s t u v X Y} (labels : Fin a → Nat) (d : Nat)
  (p : s ≤ u) (q : t ≤ v)
  (f : Fragment labels s (pi X Y)) (y : Fragment labels t X)
  (hp : ∥ Native.Typ Native.empty (pi X Y) (U d) ∥₁)
  (small : a ≤ inputSize (fragment-nf f) (fragment-nf y))
  → fragment-raw (apply-fragment labels d (embed-fragment p f) (embed-fragment q y) hp small)
      ≡ fragment-raw (apply-fragment labels d f y hp small)
apply-embedding-raw labels d p q f y hp small =
  apply-fragment-raw labels d (embed-fragment p f) (embed-fragment q y) hp small
  ∙ sym (apply-fragment-raw labels d f y hp small)

-- Every reachable state of application, under any strategy, has the exact
-- substituted type and the original semantic redex-rank bound. The selected
-- deterministic strategy additionally supplies the elementary size bound.
application-state-sound : ∀ {a s t X Y} (labels : Fin a → Nat) (d : Nat)
  (f : Fragment labels s (pi X Y)) (y : Fragment labels t X)
  → ∥ Native.Typ Native.empty (pi X Y) (U d) ∥₁
  → {u : Native.Term 0} → Steps (app (fragment-term f) (fragment-term y)) u
  → ∥ Native.Typ Native.empty u (substitute Y (fragment-term y))
      × Native.RedexBound Native.empty u d ∥₁
application-state-sound labels d f y hp path = rec3 squash₁
  (λ hf hy sorted → ∣ reachable-invariant Native.wf-empty
    (Native.application hf hy)
    (normal-application-rank-bound Native.wf-empty (fragment-normal f)
      (fragment-normal y) (_ , hf , sorted)) path ∣₁)
  (fragment-typing f) (fragment-typing y) hp
