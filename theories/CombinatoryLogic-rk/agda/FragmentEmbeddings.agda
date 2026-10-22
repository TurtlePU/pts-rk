{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentEmbeddings where

-- Finite typed normal carriers and their coherent size inclusions.
-- These are ingredients for graded fragment models, not a model definition.
open import FiniteSyntax
open import FiniteBounds using (capacity; tower; tetration)
open import FiniteCarriers using (AtMost; subtype-finite)
open import NormalForms
open import NativeTyping
open import NativeConfluence using (normal-beta-unique)
open import BoundedReduction using (Normal; normal-relabel)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; isProp≤)
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

-- BEGINFRAGMENTCARRIER
-- The dictionary is fixed; s counts every node, including annotations.
-- A is an original closed type, and typing proofs are counted propositionally.
Fragment : ∀ {a} → (labels : Fin a → Nat) → Nat → Term 0 → Set
Fragment {a} labels s A = Σ (SizedNf a 0 s)
  (λ t → ∥ Typ empty (relabel labels (erase (Fin a) (fst t))) A ∥₁)

fragment-nf : ∀ {a labels s A} → Fragment {a} labels s A → Nf (Fin a) 0
fragment-nf x = fst (fst x)

fragment-raw : ∀ {a labels s A} → Fragment {a} labels s A → Raw (Fin a) 0
fragment-raw {a} x = erase (Fin a) (fragment-nf x)

fragment-term : ∀ {a labels s A} → Fragment {a} labels s A → Term 0
fragment-term {labels = labels} x = relabel labels (fragment-raw x)

fragment-bound : ∀ {a labels s A} (x : Fragment {a} labels s A)
  → nodes (fragment-raw x) ≤ s
fragment-bound x = snd (fst x)

fragment-typing : ∀ {a labels s A} (x : Fragment {a} labels s A)
  → ∥ Typ empty (fragment-term x) A ∥₁
fragment-typing = snd
-- ENDFRAGMENTCARRIER

fragment-raw-normal : ∀ {a labels s A} (x : Fragment {a} labels s A)
  → Normal (fragment-raw x)
fragment-raw-normal x = erase-normal (fragment-nf x)

fragment-normal : ∀ {a labels s A} (x : Fragment {a} labels s A)
  → Normal (fragment-term x)
fragment-normal {labels = labels} x = normal-relabel labels (fragment-raw-normal x)

fragment-native-bound : ∀ {a labels s A} (x : Fragment {a} labels s A)
  → nodes (fragment-term x) ≤ s
fragment-native-bound {labels = labels} {s} x =
  subst (_≤ s) (sym (relabel-nodes labels (fragment-raw x))) (fragment-bound x)

pack-fragment : ∀ {a s A} (labels : Fin a → Nat)
  (t : Raw (Fin a) 0) → Normal t → nodes t ≤ s
  → Typ empty (relabel labels t) A → Fragment labels s A
pack-fragment {a} {s} {A} labels t nf bound typed =
  (from-normal t nf , subst (λ u → nodes u ≤ s) (sym recovers) bound)
  , ∣ subst (λ u → Typ empty (relabel labels u) A) (sym recovers) typed ∣₁
  where
  recovers : erase (Fin a) (from-normal t nf) ≡ t
  recovers = erase-from-normal t nf

pack-fragment-raw : ∀ {a s A} (labels : Fin a → Nat)
  (t : Raw (Fin a) 0) (nf : Normal t) (bound : nodes t ≤ s)
  (typed : Typ empty (relabel labels t) A)
  → fragment-raw (pack-fragment labels t nf bound typed) ≡ t
pack-fragment-raw labels t nf bound typed = erase-from-normal t nf

pack-fragment-term : ∀ {a s A} (labels : Fin a → Nat)
  (t : Raw (Fin a) 0) (nf : Normal t) (bound : nodes t ≤ s)
  (typed : Typ empty (relabel labels t) A)
  → fragment-term (pack-fragment labels t nf bound typed) ≡ relabel labels t
pack-fragment-term labels t nf bound typed =
  cong (relabel labels) (pack-fragment-raw labels t nf bound typed)

fragment-nf-injective : ∀ {a labels s A} (x y : Fragment {a} labels s A)
  → fragment-nf x ≡ fragment-nf y → x ≡ y
fragment-nf-injective x y p = Σ≡Prop (λ _ → squash₁)
  (Σ≡Prop (λ _ → isProp≤) p)

fragment-raw-injective : ∀ {a labels s A} (x y : Fragment {a} labels s A)
  → fragment-raw x ≡ fragment-raw y → x ≡ y
fragment-raw-injective x y p = fragment-nf-injective x y
  (erase-injective (fragment-nf x) (fragment-nf y) p)

fragment-finite : ∀ {a} (labels : Fin a → Nat) s A
  → AtMost (Fragment labels s A) (capacity a 0 s)
fragment-finite {a} labels s A = subtype-finite
  (λ t → ∥ Typ empty (relabel labels (erase (Fin a) (fst t))) A ∥₁)
  (λ _ → squash₁) (normal-finite a 0 s)

fragment-knuth-bound : ∀ {a} (labels : Fin a → Nat) d N A → a ≤ N
  → AtMost (Fragment labels (tower d N) A)
      (tetration (4 · N + 4) (d + 3))
fragment-knuth-bound {a} labels d N A p = subtype-finite
  (λ t → ∥ Typ empty (relabel labels (erase (Fin a) (fst t))) A ∥₁)
  (λ _ → squash₁) (closed-normal-bound a d N p)

-- BEGINFRAGMENTEMBEDDING
embed-fragment : ∀ {a labels s t A} → s ≤ t
  → Fragment {a} labels s A → Fragment labels t A
embed-fragment p ((nf , bound) , typed) = (nf , ≤-trans bound p) , typed

embed-raw : ∀ {a labels s t A} (p : s ≤ t) (x : Fragment {a} labels s A)
  → fragment-raw (embed-fragment p x) ≡ fragment-raw x
embed-raw p x = refl

embed-term : ∀ {a labels s t A} (p : s ≤ t) (x : Fragment {a} labels s A)
  → fragment-term (embed-fragment p x) ≡ fragment-term x
embed-term p x = refl

embed-injective : ∀ {a labels s t A} (p : s ≤ t) (x y : Fragment {a} labels s A)
  → embed-fragment p x ≡ embed-fragment p y → x ≡ y
embed-injective p x y e = fragment-nf-injective x y (cong fragment-nf e)

embed-identity : ∀ {a labels s A} (x : Fragment {a} labels s A)
  → embed-fragment ≤-refl x ≡ x
embed-identity x = fragment-nf-injective _ _ refl

embed-composition : ∀ {a labels s t u A} (p : s ≤ t) (q : t ≤ u)
  (x : Fragment {a} labels s A)
  → embed-fragment q (embed-fragment p x) ≡ embed-fragment (≤-trans p q) x
embed-composition p q x = fragment-nf-injective _ _ refl
-- ENDFRAGMENTEMBEDDING

embed-typing : ∀ {a labels s t A} (p : s ≤ t) (x : Fragment {a} labels s A)
  → fragment-typing (embed-fragment p x) ≡ fragment-typing x
embed-typing p x = refl

embed-proof-independent : ∀ {a labels s t A} (p q : s ≤ t)
  (x : Fragment {a} labels s A) → embed-fragment p x ≡ embed-fragment q x
embed-proof-independent p q x = fragment-nf-injective _ _ refl

-- Native conversion is sound on canonical representatives. A dictionary may
-- repeat labels, so this conclusion deliberately concerns decoded native
-- terms, not equality of their finite-alphabet representatives.
FragmentEq : ∀ {a labels s t A B}
  → Fragment {a} labels s A → Fragment labels t B → Set
FragmentEq x y = Beta (fragment-term x) (fragment-term y)

fragment-eq-refl : ∀ {a labels s A} (x : Fragment {a} labels s A) → FragmentEq x x
fragment-eq-refl x = beta-refl

fragment-eq-sym : ∀ {a labels s t A B}
  {x : Fragment {a} labels s A} {y : Fragment labels t B}
  → FragmentEq x y → FragmentEq y x
fragment-eq-sym = beta-sym

fragment-eq-trans : ∀ {a labels s t u A B C}
  {x : Fragment {a} labels s A} {y : Fragment labels t B} {z : Fragment labels u C}
  → FragmentEq x y → FragmentEq y z → FragmentEq x z
fragment-eq-trans = beta-trans

fragment-eq-sound : ∀ {a labels s t A B}
  (x : Fragment {a} labels s A) (y : Fragment labels t B)
  → FragmentEq x y → fragment-term x ≡ fragment-term y
fragment-eq-sound x y = normal-beta-unique (fragment-normal x) (fragment-normal y)

fragment-eq-complete : ∀ {a labels s t A B}
  (x : Fragment {a} labels s A) (y : Fragment labels t B)
  → fragment-term x ≡ fragment-term y → FragmentEq x y
fragment-eq-complete x y p = subst (Beta (fragment-term x)) p beta-refl

embed-eq : ∀ {a labels s t u v A B} (p : s ≤ u) (q : t ≤ v)
  {x : Fragment {a} labels s A} {y : Fragment labels t B}
  → FragmentEq x y → FragmentEq (embed-fragment p x) (embed-fragment q y)
embed-eq p q e = e

embed-eq-reflect : ∀ {a labels s t u v A B} (p : s ≤ u) (q : t ≤ v)
  {x : Fragment {a} labels s A} {y : Fragment labels t B}
  → FragmentEq (embed-fragment p x) (embed-fragment q y) → FragmentEq x y
embed-eq-reflect p q e = e

-- Type conversion changes only the proof-valued fibre. Its sort premise is
-- precisely the original conversion rule, not a presumed semantic model law.
convert-fragment : ∀ {a labels s A B r}
  → Typ empty B (U r) → Beta A B → Fragment {a} labels s A → Fragment labels s B
convert-fragment sorted e (nf , typed) = nf , PT.map (λ p → conversion p sorted e) typed

convert-term : ∀ {a labels s A B r} (sorted : Typ empty B (U r)) (e : Beta A B)
  (x : Fragment {a} labels s A)
  → fragment-term (convert-fragment sorted e x) ≡ fragment-term x
convert-term sorted e x = refl

embed-convert : ∀ {a labels s t A B r} (p : s ≤ t)
  (sorted : Typ empty B (U r)) (e : Beta A B) (x : Fragment {a} labels s A)
  → embed-fragment p (convert-fragment sorted e x)
      ≡ convert-fragment sorted e (embed-fragment p x)
embed-convert p sorted e x = fragment-nf-injective _ _ refl
