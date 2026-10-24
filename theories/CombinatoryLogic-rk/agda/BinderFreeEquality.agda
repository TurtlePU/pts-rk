{-# OPTIONS --cubical --safe --guardedness #-}
module BinderFreeEquality where

-- Finite constructor codes supply an ordinary discrete equality test.
-- All type parameters are retained, including hidden intermediate types.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; discreteℕ; znots; snotz)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd; Σ≡Prop)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Discrete→isSet)
open import BinderFreeCore using (Ty; ι; _⇒_; Tm; Nf; erase; normal; normalize; normalize-erase)
import BinderFreeBidirectional as Bidirectional
open Bidirectional using (Raw; s; k; ground; _$_; Typing;
  forget; forget-typed; elaborate; elaboration-forget; typing-isProp)

private
  data Tree : Set where
    leaf : ℕ → Tree
    node : Tree → Tree → Tree

  tag : Tree → ℕ
  tag (leaf n) = 0
  tag (node l r) = 1

  value : Tree → ℕ
  value (leaf n) = n
  value (node l r) = 0

  left right : Tree → Tree
  left (leaf n) = leaf n
  left (node l r) = l
  right (leaf n) = leaf n
  right (node l r) = r

  tree-discrete : Discrete Tree
  tree-discrete (leaf m) (leaf n) with discreteℕ m n
  ... | yes p = yes (cong leaf p)
  ... | no p = no (λ q → p (cong value q))
  tree-discrete (leaf m) (node l r) = no (λ p → znots (cong tag p))
  tree-discrete (node l r) (leaf n) = no (λ p → snotz (cong tag p))
  tree-discrete (node l r) (node l′ r′) with tree-discrete l l′
  ... | no p = no (λ q → p (cong left q))
  ... | yes p with tree-discrete r r′
  ...   | no q = no (λ e → q (cong right e))
  ...   | yes q = yes (cong₂ node p q)

  encode-type : Ty → Tree
  encode-type ι = leaf 0
  encode-type (A ⇒ B) = node (encode-type A) (encode-type B)

  decode-type : Tree → Ty
  decode-type (leaf n) = ι
  decode-type (node l r) = decode-type l ⇒ decode-type r

  type-retract : (A : Ty) → decode-type (encode-type A) ≡ A
  type-retract ι = refl
  type-retract (A ⇒ B) = cong₂ _⇒_ (type-retract A) (type-retract B)

  encode : Raw → Tree
  encode (s A B C) = node (leaf 0)
    (node (encode-type A) (node (encode-type B) (encode-type C)))
  encode (k A B) = node (leaf 1) (node (encode-type A) (encode-type B))
  encode (ground n) = node (leaf 2) (leaf n)
  encode (f $ x) = node (leaf 3) (node (encode f) (encode x))

  decode : Tree → Raw
  decode (node (leaf 0) (node A (node B C))) =
    s (decode-type A) (decode-type B) (decode-type C)
  decode (node (leaf 1) (node A B)) = k (decode-type A) (decode-type B)
  decode (node (leaf 2) (leaf n)) = ground n
  decode (node (leaf 3) (node f x)) = decode f $ decode x
  decode _ = ground 0

  retract : (t : Raw) → decode (encode t) ≡ t
  retract (s A B C) j = s (type-retract A j) (type-retract B j) (type-retract C j)
  retract (k A B) = cong₂ k (type-retract A) (type-retract B)
  retract (ground n) = refl
  retract (f $ x) = cong₂ _$_ (retract f) (retract x)

  encode-injective : {t u : Raw} → encode t ≡ encode u → t ≡ u
  encode-injective {t} {u} p = sym (retract t) ∙ cong decode p ∙ retract u

raw-discrete : Discrete Raw
raw-discrete t u with tree-discrete (encode t) (encode u)
... | yes p = yes (encode-injective p)
... | no p = no (λ q → p (cong encode q))

-- The proof fibre is propositional independently of the checker, so the
-- fully annotated untyped code determines the intrinsic typed term.
forget-injective : ∀ {A} {t u : Tm A} → forget t ≡ forget u → t ≡ u
forget-injective {A} {t} {u} p =
  sym (elaboration-forget t) ∙
  cong (λ (z : Σ Raw (λ v → Typing v A)) → elaborate (snd z))
    (Σ≡Prop (λ v → typing-isProp {t = v} {A = A}) p) ∙
  elaboration-forget u

normal-code : ∀ {A} → Nf A → Raw
normal-code n = forget (erase n)

normal-code-injective : ∀ {A} {n m : Nf A}
                      → normal-code n ≡ normal-code m → n ≡ m
normal-code-injective {n = n} {m = m} p =
  sym (normalize-erase n) ∙
  cong (λ t → normal (normalize t)) (forget-injective p) ∙
  normalize-erase m

normal-discrete : ∀ {A} → Discrete (Nf A)
normal-discrete n m with raw-discrete (normal-code n) (normal-code m)
... | yes p = yes (normal-code-injective p)
... | no p = no (λ q → p (cong normal-code q))

normal-isSet : ∀ {A} → isSet (Nf A)
normal-isSet = Discrete→isSet normal-discrete
